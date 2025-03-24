open Util
open Signatures
open Dimbwd
open Energy

type ('a, 'b, 's) t

val make_def : string -> string option -> 'a N.t -> 'b Dbwd.t -> 's energy -> ('a, 'b, 's) t
val make_hole : 'a N.t -> 'b Dbwd.t -> 's energy -> ('a, 'b, 's) t
val remake : (Compunit.t -> Compunit.t) -> ('a, 'b, 's) t -> ('a, 'b, 's) t
val name : ('a, 'b, 's) t -> string

val compare :
  ('a1, 'b1, 's1) t -> ('a2, 'b2, 's2) t -> ('a1 * 'b1 * 's1, 'a2 * 'b2 * 's2) Eq.compare

type wrapped = Wrap : ('a, 'b, 's) t -> wrapped

module Wrapped : sig
  type t = wrapped

  val compare : t -> t -> int
end

module WrapSet : module type of Set.Make (Wrapped)

val hole_number : ('a, 'b, 's) t -> int

module Map : sig
  type ('a, 'b, 's) key = ('a, 'b, 's) t

  module Make (F : Fam4) : sig
    type _ entry = Entry : ('a, 'b, 's) t * ('x, 'a, 'b, 's) F.t -> 'x entry
    type 'x t

    val empty : 'x t
    val find_opt : ('a, 'b, 's) key -> 'x t -> ('x, 'a, 'b, 's) F.t option
    val find_hole_opt : Compunit.t -> int -> 'x t -> 'x entry option

    val update :
      ('a, 'b, 's) key ->
      (('x, 'a, 'b, 's) F.t option -> ('x, 'a, 'b, 's) F.t option) ->
      'x t ->
      'x t

    val add : ('a, 'b, 's) key -> ('x, 'a, 'b, 's) F.t -> 'x t -> 'x t
    val remove : ('a, 'b, 's) key -> 'x t -> 'x t

    type 'x mapper = {
      map : 'a 'b 's. ('a, 'b, 's) key -> ('x, 'a, 'b, 's) F.t -> ('x, 'a, 'b, 's) F.t;
    }

    val map : 'x mapper -> 'x t -> 'x t

    type 'x iterator = { it : 'a 'b 's. ('a, 'b, 's) key -> ('x, 'a, 'b, 's) F.t -> unit }

    val iter : 'x iterator -> 'x t -> unit

    type ('x, 'acc) folder = {
      fold : 'a 'b 's. ('a, 'b, 's) key -> ('x, 'a, 'b, 's) F.t -> 'acc -> 'acc;
    }

    type 'x filterer = { filter : 'a 'b 's. ('a, 'b, 's) key -> ('x, 'a, 'b, 's) F.t -> bool }

    val filter : 'x filterer -> 'x t -> 'x t
    val fold : ('x, 'acc) folder -> 'x t -> 'acc -> 'acc
    val to_channel_unit : Out_channel.t -> Compunit.t -> 'x t -> Marshal.extern_flags list -> unit

    type 'x unit_entry

    val find_unit : Compunit.t -> 'x t -> 'x unit_entry
    val add_unit : Compunit.t -> 'a unit_entry -> 'a t -> 'a t
    val from_channel_unit : In_channel.t -> 'x mapper -> Compunit.t -> 'x t -> 'x t * 'x unit_entry
  end
end
