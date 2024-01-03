open Bwd
open Util

module Field : sig
  type t

  val compare : t -> t -> int
end

type t = Field.t

val intern : string -> t

module Map : sig
  type 'a t

  val empty : 'a t
  val map : ('a -> 'b) -> 'a t -> 'b t
  val mapi : (Field.t -> 'a -> 'b) -> 'a t -> 'b t
  val find_opt : Field.t -> 'a t -> 'a option
  val find : Field.t -> 'a t -> 'a
  val add : Field.t -> 'a -> 'a t -> 'a t
  val fold : (Field.t -> 'a -> 'acc -> 'acc) -> 'a t -> 'acc -> 'acc
  val of_abwd : (Field.t * 'a) Bwd.t -> 'a t
  val bindings : 'a t -> (Field.t * 'a) list

  module Monadic (M : Monad.Plain) : sig
    val mapiM : (Field.t -> 'a -> 'b M.t) -> 'a t -> 'b t M.t
  end
end

module Set : module type of Set.Make (Field)

val to_string : t -> string
