open Core
open Syntax
open Term

type homewhen = { global : Global.data; scope : Scope.trie; discrete : bool Constant.Map.t }

val unsolved : unit -> bool
val find : ('b, 's) Meta.t -> ('b, 's) Metadef.wrapped * homewhen

type data

val empty : data
val run : init:data -> (unit -> 'a) -> 'a
val try_with : ?get:(unit -> data) -> ?set:(data -> unit) -> (unit -> 'a) -> 'a

type find_number =
  | Find_number : ('b, 's) Meta.t * ('b, 's) Metadef.wrapped * homewhen -> find_number

val find_number : int -> find_number
val all_holes : unit -> find_number list
val solve : ('b, 's) Meta.t -> ('b, 's) term -> unit
