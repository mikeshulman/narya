open Dim
open Core
open Parser

let install () =
  let top = Scope.define [ "⊤" ] in
  Hashtbl.add Global.types top (UU D.zero);
  Hashtbl.add Global.constants top (Defined (Canonical (Codata (Eta, D.zero, Emp))))
