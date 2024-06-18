module Constant : sig
  type t

  val compare : t -> t -> int
end

type t = Constant.t

val make : Compunit.t -> t

module Map : sig
  type 'a t

  val empty : 'a t
  val find_opt : Constant.t -> 'a t -> 'a option
  val mem : Constant.t -> 'a t -> bool
  val add : Constant.t -> 'a -> 'a t -> 'a t
  val update : Constant.t -> ('a option -> 'a option) -> 'a t -> 'a t
  val remove : Constant.t -> 'a t -> 'a t
end
