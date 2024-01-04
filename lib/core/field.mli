module Field : sig
  type t

  val compare : t -> t -> int
end

type t = Field.t

val intern : string -> t

module Set : module type of Set.Make (Field)

val to_string : t -> string
