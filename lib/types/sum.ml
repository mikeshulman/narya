open Dim
open Util
open Core
open Syntax
open Term
open Parser

let inl = Constr.intern "inl"
let inr = Constr.intern "inr"

let install () =
  let sum = Scope.define [ "sum" ] in
  Global.add sum
    (pi None (UU D.zero) (pi None (UU D.zero) (UU D.zero)))
    (Defined
       (Lam
          ( D.zero,
            `Cube (Some "A"),
            Lam
              ( D.zero,
                `Cube (Some "B"),
                Canonical
                  (Data
                     ( N.zero,
                       Constr.Map.empty
                       |> Constr.Map.add inl
                            (Dataconstr
                               {
                                 args = Ext (None, Var (Pop (Top (id_sface D.zero))), Emp);
                                 indices = Emp;
                               })
                       |> Constr.Map.add inr
                            (Dataconstr
                               {
                                 args = Ext (None, Var (Top (id_sface D.zero)), Emp);
                                 indices = Emp;
                               }) )) ) )))
