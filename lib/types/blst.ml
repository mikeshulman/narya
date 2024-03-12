open Dim
open Util
open Core
open Syntax
open Term
open Parser

let emp = Constr.intern "emp"
let snoc = Constr.intern "snoc"

let install () =
  let bwd = Scope.define [ "Bwd" ] in
  Global.add bwd (pi None (UU D.zero) (UU D.zero))
    (Defined
       (Lam
          ( D.zero,
            `Cube (Some "A"),
            Canonical
              (Data
                 ( N.zero,
                   Constr.Map.empty
                   |> Constr.Map.add emp (Dataconstr { args = Emp; indices = Emp })
                   |> Constr.Map.add snoc
                        (Dataconstr
                           {
                             args =
                               Ext
                                 ( None,
                                   app (Const bwd) (Term.Var (Top (id_sface D.zero))),
                                   Ext (None, Var (Pop (Top (id_sface D.zero))), Emp) );
                             indices = Emp;
                           }) )) )))
