module Constant : sig
  type t

  val compare : t -> t -> int
end

type t = Constant.t

val make : Compunit.t -> t
val remake : (Compunit.t -> Compunit.t) -> t -> t

module Map : sig
  type 'a t

  val empty : 'a t
  val find_opt : Constant.t -> 'a t -> 'a option
  val mem : Constant.t -> 'a t -> bool
  val add : Constant.t -> 'a -> 'a t -> 'a t
  val update : Constant.t -> ('a option -> 'a option) -> 'a t -> 'a t
  val remove : Constant.t -> 'a t -> 'a t
  val iter : (Constant.t -> 'a -> unit) -> 'a t -> unit
  val cardinal : 'a t -> int
  val to_channel_unit : Out_channel.t -> Compunit.t -> 'a t -> Marshal.extern_flags list -> unit

  type 'a unit_entry

  val find_unit : Compunit.t -> 'a t -> 'a unit_entry
  val add_unit : Compunit.t -> 'a unit_entry -> 'a t -> 'a t
  val from_channel_unit : In_channel.t -> ('a -> 'a) -> Compunit.t -> 'a t -> 'a t * 'a unit_entry
end
