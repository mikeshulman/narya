module Compunit : sig
  type t

  val compare : t -> t -> int
end

type t = Compunit.t

val basic : t
val make : string -> t
val get : string -> t

module IntArray : sig
  type t

  val make_basic : unit -> t
  val get : t -> Compunit.t -> int
  val inc : t -> Compunit.t -> int
end

module Map : module type of Map.Make (Compunit)
module Current : module type of Algaeff.Reader.Make (Compunit)
