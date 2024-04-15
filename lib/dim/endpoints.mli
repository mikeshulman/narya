open Util

type len
type t = len N.index

val len : len N.t
val indices : (t, len) Bwv.t
val to_string : t option -> string
val of_char : char -> (t option, unit) result
val refl_char : char
