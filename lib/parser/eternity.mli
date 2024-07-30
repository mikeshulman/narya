open Util
open Core
open Status
open Syntax
open Term

type ('a, 'b, 's) homewhen = {
  global : Global.data;
  scope : Scope.trie;
  discrete : bool Constant.Map.t;
  status : ('b, 's) status;
  vars : (string option, 'a) Bwv.t;
}

val unsolved : unit -> int
val find : ('a, 'b, 's) Meta.t -> ('a, 'b, 's) Metadef.t * ('a, 'b, 's) homewhen

type data

val empty : data
val run : init:data -> (unit -> 'a) -> 'a
val try_with : ?get:(unit -> data) -> ?set:(data -> unit) -> (unit -> 'a) -> 'a

type find_number =
  | Find_number :
      ('a, 'b, 's) Meta.t * ('a, 'b, 's) Metadef.t * ('a, 'b, 's) homewhen
      -> find_number

val find_number : int -> find_number
val all_holes : unit -> find_number list
val solve : ('a, 'b, 's) Meta.t -> ('b, 's) term -> unit
