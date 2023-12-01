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
  | Term : ('lt, 'ls, 'rt, 'rs) parse -> observation

and (_, _, _, _) parse =
  | Infix : {
      notn : ('l opn, 'tight, 'r opn) notation;
      first : ('lt, 'ls, 'tight, 'l) parse;
      last : ('tight, 'r, 'rt, 'rs) parse;
      inner : observation Bwd.t;
      left_ok : ('lt, 'ls, 'tight) No.lt;
      right_ok : ('rt, 'rs, 'tight) No.lt;
    }
      -> ('lt, 'ls, 'rt, 'rs) parse
  | Prefix : {
      notn : (closed, 'tight, 'r opn) notation;
      last : ('tight, 'r, 'rt, 'rs) parse;
      inner : observation Bwd.t;
      right_ok : ('rt, 'rs, 'tight) No.lt;
    }
      -> ('lt, 'ls, 'rt, 'rs) parse
  | Postfix : {
      notn : ('l opn, 'tight, closed) notation;
      first : ('lt, 'ls, 'tight, 'l) parse;
      inner : observation Bwd.t;
      left_ok : ('lt, 'ls, 'tight) No.lt;
    }
      -> ('lt, 'ls, 'rt, 'rs) parse
  | Outfix : {
      notn : (closed, 'tight, closed) notation;
      inner : observation Bwd.t;
    }
      -> ('lt, 'ls, 'rt, 'rs) parse
  | App : {
      fn : ('lt, 'ls, No.plus_omega, No.nonstrict) parse;
      arg : (No.plus_omega, No.strict, 'rt, 'rs) parse;
      left_ok : ('lt, 'ls, No.plus_omega) No.lt;
      right_ok : ('rt, 'rs, No.plus_omega) No.lt;
    }
      -> ('lt, 'ls, 'rt, 'rs) parse
  | Ident : string -> ('lt, 'ls, 'rt, 'rs) parse
  | Constr : string -> ('lt, 'ls, 'rt, 'rs) parse
  | Field : string -> ('lt, 'ls, 'rt, 'rs) parse
  | Numeral : Q.t -> ('lt, 'ls, 'rt, 'rs) parse
  | Abs : {
      cube : [ `Cube | `Normal ];
      vars : string option list;
      body : (No.minus_omega, No.strict, 'rt, 'rs) parse;
      right_ok : ('rt, 'rs, No.minus_omega) No.lt;
    }
      -> ('lt, 'ls, 'rt, 'rs) parse

and ('left, 'tight, 'right) notation
and compiler = { compile : 'n. (string option, 'n) Bwv.t -> observation list -> 'n check }

type wrapped_parse = Wrap : ('lt, 'ls, 'rt, 'rs) parse -> wrapped_parse

type ('lt, 'ls) right_wrapped_parse = {
  get : 'rt 'rs. ('rt, 'rs) Interval.tt -> (('lt, 'ls, 'rt, 'rs) parse, string) Result.t;
}

val name : ('left, 'tight, 'right) notation -> string
val tightness : ('left, 'tight, 'right) notation -> 'tight No.t
val left : ('left, 'tight, 'right) notation -> 'left openness
val right : ('left, 'tight, 'right) notation -> 'right openness
val interval_left : ('s opn, 'tight, 'right) notation -> ('tight, 's) Interval.tt
val interval_right : ('left, 'tight, 's opn) notation -> ('tight, 's) Interval.tt
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
