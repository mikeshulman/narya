module Constr : sig
  type t

  val compare : t -> t -> int
end

type t = Constr.t

val intern : string -> t

module Map : module type of Map.Make (Constr)

val to_string : t -> string
