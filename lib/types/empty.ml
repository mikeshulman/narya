open Dim
open Core
open Term

let install () =
  let empty = Scope.define [ "∅" ] in
  Hashtbl.add Global.types empty (UU D.zero);
  Hashtbl.add Global.constants empty
    (Data { params = Zero; indices = Zero; constrs = Constr.Map.empty })
