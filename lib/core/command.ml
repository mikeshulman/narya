open Util
open Dim
open Syntax
open Raw
open Inst
open Check
open Asai.Range

type t =
  | Axiom : Constant.t * (N.zero, 'b, 'c) Raw.tel * 'c check located -> t
  | Def : Constant.t * (N.zero, 'b, 'c) Raw.tel * 'c check located * 'c check located -> t

let execute : t -> unit = function
  | Axiom (const, params, ty) ->
      let (Checked_tel (params, ctx)) = check_tel Ctx.empty params in
      let cty = check Kinetic ctx ty (universe D.zero) in
      let cty = Telescope.pis params cty in
      Hashtbl.add Global.types const cty;
      Hashtbl.add Global.constants const Axiom
  | Def (const, params, ty, tm) ->
      let (Checked_tel (params, ctx)) = check_tel Ctx.empty params in
      let cty = check Kinetic ctx ty (universe D.zero) in
      let ety = Ctx.eval_term ctx cty in
      let cty = Telescope.pis params cty in
      Hashtbl.add Global.types const cty;
      (* We temporarily define the constant as an axiom, so that its type can be used recursively in typechecking its definition.  This doesn't preclude some branches of the definition depending on the value of other branches (e.g. as in matching against a HIT), but it means that such dependence must be incorporated explicitly by the typechecker. *)
      Hashtbl.add Global.constants const Axiom;
      Reporter.try_with ~fatal:(fun d ->
          Hashtbl.remove Global.types const;
          Hashtbl.remove Global.constants const;
          Reporter.fatal_diagnostic d)
      @@ fun () ->
      let tree = Ctx.lam ctx (check Potential ctx tm ety) in
      Hashtbl.add Global.constants const (Defined tree)
