module Field : sig
  type t

  val compare : t -> t -> int
end

type t = Field.t

val intern : string -> t

module Map : module type of Map.Make (Field)
