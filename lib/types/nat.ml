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
  Global.add nn (UU D.zero)
    (Defined
       (Canonical
          (Data
             ( N.zero,
               Constr.Map.empty
               |> Constr.Map.add zero (Dataconstr { args = Emp; indices = Emp })
               |> Constr.Map.add suc
                    (Dataconstr { args = Ext (None, Const nn, Emp); indices = Emp }) ))));
  Global.add nnn (UU D.zero) (Defined (Realize (Const nn)))
