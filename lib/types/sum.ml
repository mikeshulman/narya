open Dim
open Core
open Util
open Term

let inl = Constr.intern "inl"
let inr = Constr.intern "inr"

let install () =
  let sum = Scope.define "sum" in
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
