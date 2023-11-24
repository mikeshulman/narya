open Util
open Core.Raw
module TokMap : module type of Map.Make (Token)

type openness = Open | Closed
type associativity = Left | Right | Non
type fixity = Infix | Infixl | Infixr | Prefix | Prefixr | Postfix | Postfixl | Outfix
type flag = ..

type tree =
  | Inner : branch -> tree
  | Done : 'tight notation -> tree
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
  | Notn : 'tight notation * observation list -> parse
  | App of parse * parse
  | Ident of string
  | Constr of string
  | Field of string
  | Numeral of Q.t
  | Abs of [ `Cube | `Normal ] * string option list * parse

and 'tight notation
and compiler = { compile : 'n. (string option, 'n) Bwv.t -> observation list -> 'n check }

val name : 'tight notation -> string
val tightness : 'tight notation -> 'tight No.t
val left : 'tight notation -> openness
val right : 'tight notation -> openness
val assoc : 'tight notation -> associativity
val tree : 'tight notation -> entry
val set_tree : 'tight notation -> entry -> unit
val compiler : 'tight notation -> compiler
val set_compiler : 'tight notation -> compiler -> unit
val print : 'tight notation -> (Format.formatter -> observation list -> unit) option
val set_print : 'tight notation -> (Format.formatter -> observation list -> unit) -> unit
val print_as_case : 'tight notation -> (Format.formatter -> observation list -> unit) option
val set_print_as_case : 'tight notation -> (Format.formatter -> observation list -> unit) -> unit
val make : string -> fixity -> 'tight No.t -> 'tight notation
val equal : 't1 notation -> 't2 notation -> bool

module Notation : sig
  type t = Wrap : 'tight notation -> t

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
