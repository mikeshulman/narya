open Dim
open Core

let install () =
  let top = Scope.define [ "⊤" ] in
  Hashtbl.add Global.types top (UU D.zero);
  Hashtbl.add Global.constants top
    (Record { eta = `Eta; params = Zero; dim = D.zero; fields = Emp })
