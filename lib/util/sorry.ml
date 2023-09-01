(* A way to leave holes in an incomplete function.  Writing "Sorry.e ()" has any type, and when executed throws an exception. *)

exception E

let e () = raise E
