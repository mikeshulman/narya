open Dim
open Core
open Util
open Term

let sum = Constant.intern "sum"
let ([ inl; inr ] : (Constr.t, N.two) Vec.t) = Vec.map Constr.intern [ "inl"; "inr" ]

let install () =
  Hashtbl.add Global.types sum (pi (UU D.zero) (pi (UU D.zero) (UU D.zero)));
  Hashtbl.add Global.constants sum
    (Data
       {
         params = N.two;
         indices = Zero;
         constrs =
           Constr.Map.empty
           |> Constr.Map.add inl (Global.Constr { args = Ext (Var (Pop Top), Emp); indices = Emp })
           |> Constr.Map.add inr (Global.Constr { args = Ext (Var Top, Emp); indices = Emp });
       })
