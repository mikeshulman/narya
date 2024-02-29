open Dim
open Util
open Core
open Parser

let install () =
  let empty = Scope.define [ "∅" ] in
  Hashtbl.add Global.types empty (UU D.zero);
  Hashtbl.add Global.constants empty (Defined (Canonical (Data (N.zero, Constr.Map.empty))))
