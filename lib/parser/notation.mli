open Util
open Core.Raw
module TokMap : module type of Map.Make (Token)

type openness = Open | Closed
type associativity = Left | Right | Non
type flag = ..

type tree =
  | Inner : branch -> tree
  | Done : notation -> tree
  | Flag : flag * tree -> tree
  | Lazy : tree Lazy.t -> tree

and branch = {
  ops : tree TokMap.t;
  constr : tree option;
  field : tree option;
  ident : tree option;
  term : tree TokMap.t option;
}

and entry = tree TokMap.t

and observation =
  | Flagged of flag
  | Constr of string
  | Field of string
  | Ident of string option
  | Term of parse

and parse =
  | Notn of notation * observation list
  | App of parse * parse
  | Ident of string
  | Constr of string
  | Field of string
  | Numeral of Q.t
  | Abs of [ `Cube | `Normal ] * string option list * parse

and notation
and compiler = { compile : 'n. (string option, 'n) Bwv.t -> observation list -> 'n check }

val origname : notation -> string
val tightness : notation -> float
val left : notation -> openness
val right : notation -> openness
val assoc : notation -> associativity
val tree : notation -> entry
val set_tree : notation -> entry -> unit
val compiler : notation -> compiler
val set_compiler : notation -> compiler -> unit
val print : notation -> (Format.formatter -> observation list -> unit) option
val set_print : notation -> (Format.formatter -> observation list -> unit) -> unit
val print_as_case : notation -> (Format.formatter -> observation list -> unit) option
val set_print_as_case : notation -> (Format.formatter -> observation list -> unit) -> unit

val make :
  origname:string ->
  tightness:float ->
  left:openness ->
  right:openness ->
  assoc:associativity ->
  notation

val equal : notation -> notation -> bool

module Notation : sig
  type t = notation

  val compare : t -> t -> int
end

(*  *)
val op : TokMap.key -> tree -> tree
val ops : (TokMap.key * tree) list -> tree
val term : TokMap.key -> tree -> tree
val terms : (TokMap.key * tree) list -> tree
val constr : tree -> tree
val field : tree -> tree
val ident : tree -> tree
val of_entry : tree TokMap.t -> tree
val eop : TokMap.key -> 'a -> 'a TokMap.t
val eops : (TokMap.key * 'a) list -> 'a TokMap.t
val empty_entry : 'a TokMap.t

(*  *)
val merge : entry -> entry -> entry
