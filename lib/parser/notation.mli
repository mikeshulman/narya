open Util
open Core.Raw
module TokMap : module type of Map.Make (Token)

type closed = Dummy_closed
type 's opn = Dummy_open
type _ openness = Open : 's No.strictness -> 's opn openness | Closed : closed openness

type (_, _) fixity =
  | Infix : (No.strict opn, No.strict opn) fixity
  | Infixl : (No.nonstrict opn, No.strict opn) fixity
  | Infixr : (No.strict opn, No.nonstrict opn) fixity
  | Prefix : (closed, No.strict opn) fixity
  | Prefixr : (closed, No.nonstrict opn) fixity
  | Postfix : (No.strict opn, closed) fixity
  | Postfixl : (No.nonstrict opn, closed) fixity
  | Outfix : (closed, closed) fixity

type flag = ..

type tree =
  | Inner : branch -> tree
  | Done : ('left, 'tight, 'right) notation -> tree
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
  | Notn : ('left, 'tight, 'right) notation * observation list -> parse
  | App of parse * parse
  | Ident of string
  | Constr of string
  | Field of string
  | Numeral of Q.t
  | Abs of [ `Cube | `Normal ] * string option list * parse

and ('left, 'tight, 'right) notation
and compiler = { compile : 'n. (string option, 'n) Bwv.t -> observation list -> 'n check }

val name : ('left, 'tight, 'right) notation -> string
val tightness : ('left, 'tight, 'right) notation -> 'tight No.t
val left : ('left, 'tight, 'right) notation -> 'left openness
val right : ('left, 'tight, 'right) notation -> 'right openness
val tree : ('left, 'tight, 'right) notation -> entry
val set_tree : ('left, 'tight, 'right) notation -> entry -> unit
val compiler : ('left, 'tight, 'right) notation -> compiler
val set_compiler : ('left, 'tight, 'right) notation -> compiler -> unit

val print :
  ('left, 'tight, 'right) notation -> (Format.formatter -> observation list -> unit) option

val set_print :
  ('left, 'tight, 'right) notation -> (Format.formatter -> observation list -> unit) -> unit

val print_as_case :
  ('left, 'tight, 'right) notation -> (Format.formatter -> observation list -> unit) option

val set_print_as_case :
  ('left, 'tight, 'right) notation -> (Format.formatter -> observation list -> unit) -> unit

val make : string -> ('left, 'right) fixity -> 'tight No.t -> ('left, 'tight, 'right) notation
val equal : ('l1, 't1, 'r1) notation -> ('l2, 't2, 'r2) notation -> bool

module Notation : sig
  type t = Wrap : ('left, 'tight, 'right) notation -> t

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
