type t

val max : t
val min : t
val premax : t
val arrow : t
val make : string -> t
val exists : string -> bool
val add_prec : t -> t -> unit option
val get_opens : unit -> t list
val get_highers : t -> t list
val open_node : t -> unit
val close_node : t -> unit option

type 'a map

module Map : sig
  val make : 'a map
  val add : t -> 'a -> 'a map -> 'a map
  val get : t -> 'a map -> 'a list

  type 'a t = 'a map
end
