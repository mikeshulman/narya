open Bwd
open Util
open Core.Raw
module TokMap : module type of Map.Make (Token)

type closed = Dummy_closed
type 's opn = Dummy_open
type _ openness = Open : 's No.strictness -> 's opn openness | Closed : closed openness

type (_, _, _) fixity =
  | Infix : 'tight No.t -> (No.strict opn, 'tight, No.strict opn) fixity
  | Infixl : 'tight No.t -> (No.nonstrict opn, 'tight, No.strict opn) fixity
  | Infixr : 'tight No.t -> (No.strict opn, 'tight, No.nonstrict opn) fixity
  | Prefix : 'tight No.t -> (closed, 'tight, No.strict opn) fixity
  | Prefixr : 'tight No.t -> (closed, 'tight, No.nonstrict opn) fixity
  | Postfix : 'tight No.t -> (No.strict opn, 'tight, closed) fixity
  | Postfixl : 'tight No.t -> (No.nonstrict opn, 'tight, closed) fixity
  | Outfix : (closed, No.plus_omega, closed) fixity

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
  | Infix : ('l opn, 'tight, 'r opn) notation * observation * observation Bwd.t -> parse
  | Prefix : (closed, 'tight, 'r opn) notation * observation Bwd.t -> parse
  | Postfix : ('l opn, 'tight, closed) notation * observation * observation Bwd.t -> parse
  | Outfix : (closed, 'tight, closed) notation * observation Bwd.t -> parse
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

val make : string -> ('left, 'tight, 'right) fixity -> ('left, 'tight, 'right) notation
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
