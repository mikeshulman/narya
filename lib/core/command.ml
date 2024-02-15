open Util
open Dim
open Norm
open Syntax
open Raw
open Value
open Inst
open Check
open Asai.Range

type t =
  | Axiom : Constant.t * (N.zero, 'b, 'c) Raw.tel * 'c check located -> t
  | Def : Constant.t * (N.zero, 'b, 'c) Raw.tel * 'c check located * 'c check located -> t

let execute : t -> unit = function
  | Axiom (const, params, ty) ->
      let (Checked_tel (params, ctx)) = check_tel Ctx.empty params in
      let cty = check ctx ty (universe D.zero) in
      let cty = Telescope.pis params cty in
      Hashtbl.add Global.types const cty;
      Hashtbl.add Global.constants const Axiom
  | Def (const, params, ty, tm) ->
      let (Checked_tel (params, ctx)) = check_tel Ctx.empty params in
      let cty = check ctx ty (universe D.zero) in
      let ety = Ctx.eval ctx cty in
      let cty = Telescope.pis params cty in
      Hashtbl.add Global.types const cty;
      let tree = ref Case.Empty in
      Hashtbl.add Global.constants const (Defined tree);
      let hd = eval (Emp D.zero) (Const const) in
      Reporter.try_with ~fatal:(fun d ->
          Hashtbl.remove Global.types const;
          Hashtbl.remove Global.constants const;
          Reporter.fatal_diagnostic d)
      @@ fun () -> check_tree ctx tm ety hd (Ctx.lam_tree ctx tree)
