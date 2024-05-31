open Dim
open Core
open Inst
open Norm
open Check
open Notation
open Postprocess

let const = Constant.make ()
let installed = ref false

let install () =
  if not !installed then (
    installed := true;
    let ctx = Ctx.empty in
    let (Term pty) =
      Parse.Term.final
        (Parse.Term.parse
           (`String { content = "(A : Type) (B : A -> Type) -> Type"; title = None })) in
    let rty = process Emp pty in
    let cty = check (Kinetic `Nolet) ctx rty (universe D.zero) in
    let ety = eval_term (Ctx.env ctx) cty in
    let (Term ptm) =
      Parse.Term.final
        (Parse.Term.parse (`String { content = "A B |-> (x : A) -> B x"; title = None })) in
    let rtm = process Emp ptm in
    let ctm = check (Potential (Constant const, Ctx.apps ctx, Ctx.lam ctx)) ctx rtm ety in
    Global.add const cty (Defined ctm);
    Scope.set [ "Π" ] const)
