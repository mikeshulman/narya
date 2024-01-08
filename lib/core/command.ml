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
  | Axiom of Constant.t * N.zero check located
  | Def of Constant.t * N.zero check located * N.zero check located

let execute : t -> unit = function
  | Axiom (const, ty) ->
      let cty = check Ctx.empty ty (universe D.zero) in
      Hashtbl.add Global.types const cty;
      Hashtbl.add Global.constants const Axiom
  | Def (const, ty, tm) ->
      let cty = check Ctx.empty ty (universe D.zero) in
      let ety = eval (Emp D.zero) cty in
      Hashtbl.add Global.types const cty;
      let tree = ref Case.Empty in
      Hashtbl.add Global.constants const (Defined tree);
      let hd = eval (Emp D.zero) (Const const) in
      Reporter.try_with ~fatal:(fun d ->
          Hashtbl.remove Global.types const;
          Hashtbl.remove Global.constants const;
          Reporter.fatal_diagnostic d)
      @@ fun () -> check_tree Ctx.empty tm ety hd tree
