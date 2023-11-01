open Dim
open Core
open Term

let install () =
  let top = Scope.define "⊤" in
  Hashtbl.add Global.types top (UU D.zero);
  Hashtbl.add Global.constants top (Record { eta = true; params = Zero; dim = D.zero; fields = [] })
