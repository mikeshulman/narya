open Dim
open Core
open Term

let inl = Constr.intern "inl"
let inr = Constr.intern "inr"

let install () =
  let sum = Scope.define [ "sum" ] in
  Hashtbl.add Global.types sum (pi None (UU D.zero) (pi None (UU D.zero) (UU D.zero)));
  Hashtbl.add Global.constants sum
    (Data
       {
         params = Suc (Suc Zero);
         indices = Zero;
         constrs =
           Constr.Map.empty
           |> Constr.Map.add inl
                (Global.Constr
                   { args = Ext (None, Var (Pop (Top (id_sface D.zero))), Emp); indices = Emp })
           |> Constr.Map.add inr
                (Global.Constr
                   { args = Ext (None, Var (Top (id_sface D.zero)), Emp); indices = Emp });
       })
