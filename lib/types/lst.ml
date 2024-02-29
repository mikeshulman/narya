open Dim
open Util
open Core
open Syntax
open Term
open Parser

let nil = Constr.intern "nil"
let cons = Constr.intern "cons"

let install () =
  let list = Scope.define [ "List" ] in
  Hashtbl.add Global.types list (pi None (UU D.zero) (UU D.zero));
  Hashtbl.add Global.constants list
    (Defined
       (Lam
          ( D.zero,
            `Cube (Some "A"),
            Canonical
              (Data
                 ( N.zero,
                   Constr.Map.empty
                   |> Constr.Map.add nil (Dataconstr { args = Emp; indices = Emp })
                   |> Constr.Map.add cons
                        (Dataconstr
                           {
                             args =
                               Ext
                                 ( None,
                                   Var (Top (id_sface D.zero)),
                                   Ext
                                     ( None,
                                       app (Const list) (Term.Var (Pop (Top (id_sface D.zero)))),
                                       Emp ) );
                             indices = Emp;
                           }) )) )))
