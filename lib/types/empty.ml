open Dim
open Core
open Util
open Term

let install () =
  let empty = Scope.define "∅" in
  Hashtbl.add Global.types empty (UU D.zero);
  Hashtbl.add Global.constants empty
    (Data { params = N.zero; indices = Zero; constrs = Constr.Map.empty })
