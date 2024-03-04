(* A way to leave holes in an incomplete function.  Writing "Sorry.e ()" has any type, and when executed throws an exception.  You can also write "_", but while Tuareg is okay with that, the actual compiler is not. *)

exception E

let e () = raise E
