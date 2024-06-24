open Core
open Syntax
open Term

type data = { global : Global.data; scope : Scope.trie; discrete : bool Constant.Map.t }

val unsolved : unit -> bool
val run_empty : (unit -> 'a) -> 'a
val find : ('b, 's) Meta.t -> ('b, 's) Metadef.wrapped * data
val hole_of_number : int -> Meta.wrapped
val solve : ('b, 's) Meta.t -> ('b, 's) term -> unit
