open Bwd
open Util
open Tbwd
open Dim
open Syntax
open Raw
open Term
open Inst
open Check
open Readback
open Asai.Range

(* A mutual "def" command can contain multiple constant definitions, each one checking or synthesizing.  *)
type defconst =
  | Def_check :
      (Constant.t * (N.zero, 'b, 'c) Raw.tel * 'c check located * 'c check located)
      -> defconst
  | Def_synth : (Constant.t * (N.zero, 'b, 'c) Raw.tel * 'c synth located) -> defconst

type t =
  | Axiom : Constant.t * (N.zero, 'b, 'c) Raw.tel * 'c check located -> t
  | Def : defconst list -> t

(* When checking a mutual "def", we first check all the parameter telescopes, making contexts, and also evaluate all the types, in the checking cases when they are provided.  Here are the outputs of that stage, saving the as-yet-unchecked raw term and also the context of parameters. *)
type defined_const =
  | Defined_check :
      (* In this case we save both the type *in* the context of the parameters, and the type as a Π-type over that context, since we need both. *)
      (Constant.t * ('a, 'b) Ctx.t * ('b, kinetic) term * (emp, kinetic) term * 'a check located)
      -> defined_const
  | Defined_synth :
      (Constant.t * ('a, 'b) Ctx.t * (emp, 'c, 'b) Telescope.t * 'a synth located)
      -> defined_const

(* Given such a thing, we can proceed to check or synthesize the term, producing the type and defined value for the constant, and then define it.  *)
let check_term : defined_const -> unit = function
  | Defined_check (const, ctx, cty, pi_cty, tm) ->
      (* It's essential that we evaluate the type at this point, rather than sooner, so that the evaluation uses the *definitions* of previous constants in the mutual block and not just their types.  *)
      let ety = Ctx.eval_term ctx cty in
      let tree = Ctx.lam ctx (check (Potential (const, Ctx.apps ctx, Ctx.lam ctx)) ctx tm ety) in
      Global.add const pi_cty (Defined tree)
  | Defined_synth (const, ctx, params, tm) ->
      let ctm, ety = synth ctx tm in
      let cty = readback_val ctx ety in
      Global.add const (Telescope.pis params cty) (Defined (Ctx.lam ctx (Realize ctm)))

(* When checking a "def", therefore, we first iterate through checking the parameters and types, and then go back and check all the terms.  Moreover, whenever we check a type, we temporarily define the corresponding constant as an axiom having that type, so that its type can be used recursively in typechecking its definition, as well as the types of later mutual constants and the definitions of any other mutual constants. *)
let check_defs (defs : defconst list) : unit =
  let rec go defs defineds =
    match defs with
    | [] -> List.iter check_term (Bwd.to_list defineds)
    | Def_check (const, params, ty, tm) :: defs ->
        let (Checked_tel (params, ctx)) = check_tel Ctx.empty params in
        let cty = check Kinetic ctx ty (universe D.zero) in
        let pi_cty = Telescope.pis params cty in
        (* This temporary definition will be overridden later. *)
        Global.add const pi_cty (Axiom `Parametric);
        go defs (Snoc (defineds, Defined_check (const, ctx, cty, pi_cty, tm)))
    | Def_synth (const, params, tm) :: defs ->
        Global.add_error const (Synthesizing_recursion (Reporter.PConstant const));
        let (Checked_tel (params, ctx)) = check_tel Ctx.empty params in
        go defs (Snoc (defineds, Defined_synth (const, ctx, params, tm))) in
  go defs Emp

let execute : t -> unit = function
  | Axiom (const, params, ty) ->
      let (Checked_tel (params, ctx)) = check_tel Ctx.empty params in
      let cty = check Kinetic ctx ty (universe D.zero) in
      let cty = Telescope.pis params cty in
      Global.add const cty (Axiom `Nonparametric)
  | Def defs -> check_defs defs
