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

and ('left, 'tight, 'right, 'lt, 'ls, 'rt, 'rs) parsed_notn = {
  notn : ('left, 'tight, 'right) notation;
  first : ('lt, 'ls, 'tight, 'left) first_arg;
  inner : observation Bwd.t;
  last : ('tight, 'right, 'rt, 'rs) last_arg;
  left_ok : ('lt, 'ls, 'tight, 'left) tighter_than;
  right_ok : ('rt, 'rs, 'tight, 'right) tighter_than;
}

and (_, _, _, _) first_arg =
  | Some_first : ('lt, 'ls, 'tight, 'l) parse -> ('lt, 'ls, 'tight, 'l opn) first_arg
  | No_first : ('lt, 'ls, 'tight, closed) first_arg

and (_, _, _, _) last_arg =
  | Some_last : ('tight, 'r, 'rt, 'rs) parse -> ('tight, 'r opn, 'rt, 'rs) last_arg
  | No_last : ('tight, closed, 'rt, 'rs) last_arg

and (_, _, _, _) tighter_than =
  | Open_ok : ('lt, 'ls, 'tight) No.lt -> ('lt, 'ls, 'tight, 'l opn) tighter_than
  | Closed_ok : ('lt, 'ls, 'tight, closed) tighter_than

and (_, _, _, _) parse =
  | Notn : ('left, 'tight, 'right, 'lt, 'ls, 'rt, 'rs) parsed_notn -> ('lt, 'ls, 'rt, 'rs) parse
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

val empty_branch : branch

val infix :
  notn:('a opn, 'b, 'c opn) notation ->
  first:('d, 'e, 'b, 'a) parse ->
  inner:observation Bwd.t ->
  last:('b, 'c, 'f, 'g) parse ->
  left_ok:('d, 'e, 'b) Util.No.lt ->
  right_ok:('f, 'g, 'b) Util.No.lt ->
  ('d, 'e, 'f, 'g) parse

val prefix :
  notn:(closed, 'a, 'b opn) notation ->
  inner:observation Bwd.t ->
  last:('a, 'b, 'c, 'd) parse ->
  right_ok:('c, 'd, 'a) Util.No.lt ->
  ('e, 'f, 'c, 'd) parse

val postfix :
  notn:('a opn, 'b, closed) notation ->
  first:('c, 'd, 'b, 'a) parse ->
  inner:observation Bwd.t ->
  left_ok:('c, 'd, 'b) Util.No.lt ->
  ('c, 'd, 'e, 'f) parse

val outfix : notn:(closed, 'a, closed) notation -> inner:observation Bwd.t -> ('b, 'c, 'd, 'e) parse
val args : ('left, 'tight, 'right, 'lt, 'ls, 'rt, 'rs) parsed_notn -> observation list

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
