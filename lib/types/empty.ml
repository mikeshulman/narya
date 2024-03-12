open Dim
open Util
open Core
open Parser

let install () =
  let empty = Scope.define [ "∅" ] in
  Global.add empty (UU D.zero) (Defined (Canonical (Data (N.zero, Constr.Map.empty))))
