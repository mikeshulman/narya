open Dim
open Core
open Parser

let install () =
  let top = Scope.define [ "⊤" ] in
  Global.add top (UU D.zero) (Defined (Canonical (Codata (Eta, D.zero, Emp))))
