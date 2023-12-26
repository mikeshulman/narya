open Util
open Dim
open Value
open Norm
open Raw
open Check
open Reporter

type t =
  | Axiom of Scope.Trie.path * N.zero check
  | Def of Scope.Trie.path * N.zero check * N.zero check

let execute : t -> unit = function
  | Axiom (name, ty) ->
      let const = Scope.define name in
      if Hashtbl.mem Global.types const then fatal (Constant_already_defined name)
      else
        let cty = check Ctx.empty ty (universe D.zero) in
        Hashtbl.add Global.types const cty;
        Hashtbl.add Global.constants const Axiom;
        emit (Constant_assumed name)
  | Def (name, ty, tm) ->
      let const = Scope.define name in
      if Hashtbl.mem Global.types const then fatal (Constant_already_defined name)
      else
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
        @@ fun () ->
        check_tree Ctx.empty tm ety hd tree;
        emit (Constant_defined name)
