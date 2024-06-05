open Bwd
open Util
open Tbwd
open Dim
open Syntax
open Raw
open Term
open Inst
open Norm
open Check
open Readback
open Reporter
open Asai.Range

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

(* When checking a mutual "def", we first check all the parameter telescopes, making contexts, and also evaluate all the types, in the checking cases when they are provided.  Here are the outputs of that stage, saving the as-yet-unchecked raw term and also the context of parameters. *)
type defined_const =
  | Defined_check : {
      const : Constant.t;
      params : (N.zero, 'b, 'c) Raw.tel;
      ty : 'c check located;
      pi_cty : (emp, kinetic) term;
      tm : 'c check located;
    }
      -> defined_const
  | Defined_synth : {
      const : Constant.t;
      params : (N.zero, 'b, 'c) Raw.tel;
      tm : 'c synth located;
    }
      -> defined_const

(* Given such a thing, we can proceed to check or synthesize the term, producing the type and defined value for the constant, and then define it.  *)
let check_term : defined_const -> unit = function
  | Defined_check { const; params; ty; pi_cty; tm } ->
      (* It's essential that we evaluate the type at this point, rather than sooner, so that the evaluation uses the *definitions* of previous constants in the mutual block and not just their types.  For the same reason, we need to re-evaluate the telescope of parameters. *)
      let Checked_tel (_, ctx), _ = check_tel Ctx.empty params in
      let cty = check (Kinetic `Nolet) ctx ty (universe D.zero) in
      let ety = eval_term (Ctx.env ctx) cty in
      let tree =
        Ctx.lam ctx (check (Potential (Constant const, Ctx.apps ctx, Ctx.lam ctx)) ctx tm ety) in
      Global.add const pi_cty (Defined tree)
  | Defined_synth { const; params; tm } ->
      let Checked_tel (cparams, ctx), _ = check_tel Ctx.empty params in
      let ctm, ety = synth (Potential (Constant const, Ctx.apps ctx, Ctx.lam ctx)) ctx tm in
      let cty = readback_val ctx ety in
      Global.add const (Telescope.pis cparams cty) (Defined (Ctx.lam ctx ctm))

(* When checking a "def", therefore, we first iterate through checking the parameters and types, and then go back and check all the terms.  Moreover, whenever we check a type, we temporarily define the corresponding constant as an axiom having that type, so that its type can be used recursively in typechecking its definition, as well as the types of later mutual constants and the definitions of any other mutual constants. *)
let check_defs (defs : (Constant.t * defconst) list) : unit =
  let rec go defs defineds =
    match defs with
    | [] -> List.iter check_term (Bwd.to_list defineds)
    | (const, Def_check { params; ty; tm }) :: defs ->
        let Checked_tel (cparams, ctx), _ = check_tel Ctx.empty params in
        let cty = check (Kinetic `Nolet) ctx ty (universe D.zero) in
        let pi_cty = Telescope.pis cparams cty in
        (* This temporary definition will be overridden later. *)
        Global.add const pi_cty (Axiom `Parametric);
        go defs (Snoc (defineds, Defined_check { const; params; ty; pi_cty; tm }))
    | (const, Def_synth { params; tm }) :: defs ->
        Global.add_error const (Synthesizing_recursion (Reporter.PConstant const));
        go defs (Snoc (defineds, Defined_synth { const; params; tm })) in
  go defs Emp

let execute : t -> unit = function
  | Axiom (const, params, ty) ->
      Discrete.run ~init:Constant.Map.empty @@ fun () ->
      let Checked_tel (params, ctx), _ = check_tel Ctx.empty params in
      let cty = check (Kinetic `Nolet) ctx ty (universe D.zero) in
      let cty = Telescope.pis params cty in
      Global.add const cty (Axiom `Nonparametric);
      let h = Eternity.end_command () in
      emit (Constant_assumed (PConstant const, h))
  | Def defs ->
      let init =
        List.fold_left (fun map (c, _) -> map |> Constant.Map.add c false) Constant.Map.empty defs
      in
      (* Currently, mutual families of definitions can never be discrete. *)
      Discreteness.run ~env:(Discreteness.read () && List.length defs = 1) @@ fun () ->
      Discrete.run ~init @@ fun () ->
      check_defs defs;
      let h = Eternity.end_command () in
      let printables =
        List.map (fun (c, _) -> (PConstant c, Constant.Map.find c (Discrete.get ()))) defs in
      emit (Constant_defined (printables, h))
