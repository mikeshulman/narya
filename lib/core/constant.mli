module Constant : sig
  type t

  val compare : t -> t -> int
end

type t = Constant.t

val make : unit -> t

module Map : module type of Map.Make (Constant)
