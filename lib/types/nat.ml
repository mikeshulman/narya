open Util
open Dim
open Core
open Parser
open Syntax
open Term

let nn = Constant.make ()
let nnn = Constant.make ()
let zero = Constr.intern "zero"
let suc = Constr.intern "suc"

open Monad.Ops (Monad.Maybe)

let install () =
  Scope.set [ "ℕ" ] nn;
  Scope.set [ "Nat" ] nnn;
  Hashtbl.add Global.types nn (UU D.zero);
  Hashtbl.add Global.constants nn
    (Data
       {
         params = Zero;
         indices = Zero;
         constrs =
           Constr.Map.empty
           |> Constr.Map.add zero (Global.Constr { args = Emp; indices = Emp })
           |> Constr.Map.add suc (Global.Constr { args = Ext (None, Const nn, Emp); indices = Emp });
       });
  Hashtbl.add Global.types nnn (UU D.zero);
  Hashtbl.add Global.constants nnn (Defined (Realize (Const nn)));
  ()
