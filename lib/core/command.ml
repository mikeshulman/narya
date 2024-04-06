open Util
open Dim
open Syntax
open Raw
open Inst
open Check
open Readback
open Asai.Range

type t =
  | Axiom : Constant.t * (N.zero, 'b, 'c) Raw.tel * 'c check located -> t
  | Def :
      Constant.t
      * (N.zero, 'b, 'c) Raw.tel
      * [ `Check of 'c check located * 'c check located | `Synth of 'c synth located ]
      -> t

let execute : t -> unit = function
  | Axiom (const, params, ty) ->
      let (Checked_tel (params, ctx)) = check_tel Ctx.empty params in
      let cty = check Kinetic ctx ty (universe D.zero) in
      let cty = Telescope.pis params cty in
      Global.add const cty Axiom
  | Def (const, params, `Check (ty, tm)) ->
      let (Checked_tel (params, ctx)) = check_tel Ctx.empty params in
      let cty = check Kinetic ctx ty (universe D.zero) in
      let ety = Ctx.eval_term ctx cty in
      let cty = Telescope.pis params cty in
      (* We temporarily define the constant as an axiom, so that its type can be used recursively in typechecking its definition.  This doesn't preclude some branches of the definition depending on the value of other branches (e.g. as in matching against a HIT), but it means that such dependence must be incorporated explicitly by the typechecker. *)
      let tree =
        Global.run_with const cty Axiom @@ fun () ->
        Ctx.lam ctx (check (Potential (const, Ctx.apps ctx, Ctx.lam ctx)) ctx tm ety) in
      Global.add const cty (Defined tree)
  | Def (const, params, `Synth tm) ->
      let (Checked_tel (params, ctx)) = check_tel Ctx.empty params in
      let ctm, ety = synth ctx tm in
      let cty = readback_val ctx ety in
      Global.add const (Telescope.pis params cty) (Defined (Ctx.lam ctx (Realize ctm)))
