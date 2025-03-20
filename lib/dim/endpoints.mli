open Util

type 'l len
type wrapped = Wrap : 'l len -> wrapped
type 'l t = 'l len * 'l N.index

val run :
  arity:int -> refl_char:char -> refl_names:string list -> internal:bool -> (unit -> 'a) -> 'a

val wrapped : unit -> wrapped
val refl_string : unit -> string
val refl_names : unit -> string list
val internal : unit -> bool

(* *)
val uniq : 'l1 len -> 'l2 len -> ('l1, 'l2) Eq.t
val len : 'l len -> 'l N.t
val indices : 'l len -> ('l t, 'l) Bwv.t
val to_string : 'l t option -> string
val of_char : 'l len -> char -> ('l t option, unit) result
