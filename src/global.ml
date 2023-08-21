open Term

(* The global environment of constants *)

let types : (Constant.t, N.zero term) Hashtbl.t = Hashtbl.create 10
