open Value

(* The global environment of constants *)

let global : (Constant.t, value) Hashtbl.t = Hashtbl.create 10
