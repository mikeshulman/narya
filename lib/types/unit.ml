open Dim
open Core
open Util
open Term

let install () =
  let top = Scope.define "⊤" in
  Hashtbl.add Global.types top (UU D.zero);
  Hashtbl.add Global.constants top
    (Record
       {
         eta = true;
         params = N.zero;
         dim = D.zero;
         dim_faces = faces_zero;
         params_plus = Suc Zero;
         fields = [];
       })
