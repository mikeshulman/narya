open Core
open Syntax
open Term

type data = { global : Global.data; scope : Scope.trie; discrete : bool Constant.Map.t }

val unsolved : unit -> bool
val run_empty : (unit -> 'a) -> 'a
val find : ('b, 's) Meta.t -> ('b, 's) Metadef.wrapped * data

type find_number = Find_number : ('b, 's) Meta.t * ('b, 's) Metadef.wrapped * data -> find_number

val find_number : int -> find_number
val all_holes : unit -> find_number list
val solve : ('b, 's) Meta.t -> ('b, 's) term -> unit
