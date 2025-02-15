open Util

module Field : sig
  type t

  val compare : t -> t -> int
end

type t = Field.t

val intern : string -> t

module Set : module type of Set.Make (Field)

module PbijSet : module type of Stdlib.Set.Make (struct
  type t = Field.t * string list

  let compare = compare
end)

val to_string : t -> string

type or_index = [ `Name of t | `Index of int ]

val to_string_ori : or_index -> string
val intern_ori : string -> or_index
val find : (Field.t, 'a) Abwd.t -> or_index -> (Field.t * 'a) option
