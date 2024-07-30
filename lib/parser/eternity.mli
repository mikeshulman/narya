open Core
open Status
open Syntax
open Term

type ('b, 's) homewhen = {
  global : Global.data;
  scope : Scope.trie;
  discrete : bool Constant.Map.t;
  status : ('b, 's) status;
}

val unsolved : unit -> int
val find : ('b, 's) Meta.t -> ('b, 's) Metadef.wrapped * ('b, 's) homewhen

type data

val empty : data
val run : init:data -> (unit -> 'a) -> 'a
val try_with : ?get:(unit -> data) -> ?set:(data -> unit) -> (unit -> 'a) -> 'a

type find_number =
  | Find_number : ('b, 's) Meta.t * ('b, 's) Metadef.wrapped * ('b, 's) homewhen -> find_number

val find_number : int -> find_number
val all_holes : unit -> find_number list
val solve : ('b, 's) Meta.t -> ('b, 's) term -> unit
