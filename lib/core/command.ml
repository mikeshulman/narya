open Bwd
open Util
open Tbwd
open Dim
open Syntax
open Raw
open Term
open Norm
open Check
open Readback
open Reporter
open Asai.Range

module ModeState = struct
  type t = { interactive : bool }
end

module Mode = Algaeff.Reader.Make (ModeState)

(* A mutual "def" command can contain multiple constant definitions, each one checking or synthesizing.  *)
type defconst =
  | Def_check : {
      params : (N.zero, 'b, 'c) Raw.tel;
      ty : 'c check located;
      tm : 'c check located;
    }
      -> defconst
  | Def_synth : { params : (N.zero, 'b, 'c) Raw.tel; tm : 'c synth located } -> defconst

type t =
  | Axiom : Constant.t * (N.zero, 'b, 'c) Raw.tel * 'c check located -> t
  | Def : (Constant.t * defconst) list -> t
  | Solve :
      Global.data
      * ('b, 's) status
      * ('a, 'b) Termctx.t
      * 'a check located
      * ('b, kinetic) term
      * (('b, 's) term -> unit)
      -> t

(* When checking a mutual "def", we first check all the parameter telescopes, and the types in the checking cases when they are provided.  Here are the outputs of that stage, saving the as-yet-unchecked raw term along with its checked parameters and type. *)
type defined_const =
  | Defined_check : {
      const : Constant.t;
      bplus : (N.zero, 'c, 'ac) Fwn.bplus;
      params : (emp, 'c, 'bc) Telescope.t;
      ty : ('bc, kinetic) term;
      tm : 'ac check located;
    }
      -> defined_const
  | Defined_synth : {
      const : Constant.t;
      (* We don't bother checking the parameter telescopes of a synthesizing one, since it can't be used in other ones anyway. *)
      params : (N.zero, 'b, 'c) Raw.tel;
      tm : 'c synth located;
    }
      -> defined_const

(* Given such a thing, we can proceed to check or synthesize the term, producing the type and defined value for the constant, and then define it.  *)
let check_term : defined_const -> printable * bool = function
  | Defined_check { const; bplus; params; ty; tm } ->
      (* It's essential that we evaluate the type at this point, rather than sooner, so that the evaluation uses the *definitions* of previous constants in the mutual block and not just their types.  For the same reason, we need to re-evaluate the telescope of parameters. *)
      let ctx = eval_append Ctx.empty bplus params in
      let ety = eval_term (Ctx.env ctx) ty in
      let tree = check (Potential (Constant const, Ctx.apps ctx, Ctx.lam ctx)) ctx tm ety in
      let discrete =
        match tree with
        | Canonical (Data { discrete = true; _ }) -> true
        | _ -> false in
      Global.set const (Defined (Ctx.lam ctx tree));
      (PConstant const, discrete)
  | Defined_synth { const; params; tm } ->
      let Checked_tel (cparams, ctx), _ = check_tel Ctx.empty params in
      let ctm, ety = synth (Potential (Constant const, Ctx.apps ctx, Ctx.lam ctx)) ctx tm in
      let cty = readback_val ctx ety in
      let ty = Telescope.pis cparams cty in
      let tree = Ctx.lam ctx ctm in
      let discrete =
        match tree with
        | Canonical (Data { discrete = true; _ }) -> true
        | _ -> false in
      Global.add const ty (Defined tree);
      (PConstant const, discrete)

(* When checking a "def", therefore, we first iterate through checking the parameters and types, and then go back and check all the terms.  Moreover, whenever we check a type, we temporarily define the corresponding constant as an axiom having that type, so that its type can be used recursively in typechecking its definition, as well as the types of later mutual constants and the definitions of any other mutual constants. *)
let check_defs (defs : (Constant.t * defconst) list) : (printable * bool) list =
  let rec go defs defineds =
    match defs with
    | [] -> List.map check_term (Bwd.to_list defineds)
    | (const, Def_check { params; ty; tm }) :: defs ->
        let bplus = Raw.bplus_of_tel params in
        let Checked_tel (params, ctx), _ = check_tel Ctx.empty params in
        let ty = check (Kinetic `Nolet) ctx ty (universe D.zero) in
        let pi_cty = Telescope.pis params ty in
        (* We set the type now; the value will be added later. *)
        Global.add const pi_cty (Axiom `Parametric);
        go defs (Snoc (defineds, Defined_check { const; bplus; params; ty; tm }))
    | (const, Def_synth { params; tm }) :: defs ->
        Global.add_error const (Synthesizing_recursion (Reporter.PConstant const));
        go defs (Snoc (defineds, Defined_synth { const; params; tm })) in
  go defs Emp

let execute : t -> unit = function
  | Axiom (const, params, ty) ->
      let Checked_tel (params, ctx), _ = check_tel Ctx.empty params in
      let cty = check (Kinetic `Nolet) ctx ty (universe D.zero) in
      let cty = Telescope.pis params cty in
      Global.add const cty (Axiom `Nonparametric);
      Global.end_command (fun h -> Constant_assumed (PConstant const, h))
  | Def defs ->
      let printables = check_defs defs in
      Global.end_command (fun h -> Constant_defined (printables, h))
  | Solve (global, status, termctx, tm, ty, callback) ->
      if not (Mode.read ()).interactive then fatal (Forbidden_interactive_command "solve");
      let ctm =
        Global.run_command_with ~init:global (fun h -> Hole_solved h) @@ fun () ->
        let ctx = Norm.eval_ctx termctx in
        let ety = Norm.eval_term (Ctx.env ctx) ty in
        Check.check status ctx tm ety in
      callback ctm
