open Util
open Signatures
open Dimbwd
open Energy

type ('b, 's) t

val make_def : string -> string option -> 'b Dbwd.t -> 's energy -> ('b, 's) t
val make_hole : 'b Dbwd.t -> 's energy -> ('b, 's) t
val remake : (Compunit.t -> Compunit.t) -> ('b, 's) t -> ('b, 's) t
val name : ('b, 's) t -> string
val compare : ('b1, 's1) t -> ('b2, 's2) t -> ('b1 * 's1, 'b2 * 's2) Eq.compare

type wrapped = Wrap : ('b, 's) t -> wrapped

val hole_number : ('b, 's) t -> int

module Map : sig
  type ('b, 's) key = ('b, 's) t

  module Make (F : Fam3) : sig
    type _ entry = Entry : ('b, 's) t * ('x, 'b, 's) F.t -> 'x entry
    type 'x t

    val empty : 'x t
    val find_opt : ('b, 's) key -> 'x t -> ('x, 'b, 's) F.t option
    val find_hole_opt : Compunit.t -> int -> 'x t -> 'x entry option

    val update :
      ('b, 's) key -> (('x, 'b, 's) F.t option -> ('x, 'b, 's) F.t option) -> 'x t -> 'x t

    val add : ('b, 's) key -> ('x, 'b, 's) F.t -> 'x t -> 'x t
    val remove : ('b, 's) key -> 'x t -> 'x t

    type 'x mapper = { map : 'b 's. ('b, 's) key -> ('x, 'b, 's) F.t -> ('x, 'b, 's) F.t }

    val map : 'x mapper -> 'x t -> 'x t

    type 'x iterator = { it : 'b 's. ('b, 's) key -> ('x, 'b, 's) F.t -> unit }

    val iter : 'x iterator -> 'x t -> unit

    type ('x, 'acc) folder = { fold : 'b 's. ('b, 's) key -> ('x, 'b, 's) F.t -> 'acc -> 'acc }

    val fold : ('x, 'acc) folder -> 'x t -> 'acc -> 'acc
    val to_channel_unit : Out_channel.t -> Compunit.t -> 'x t -> Marshal.extern_flags list -> unit
    val from_channel_unit : In_channel.t -> 'x mapper -> Compunit.t -> 'x t -> 'x t
  end
end
