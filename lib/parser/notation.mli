open Bwd
open Util
open Core
open Syntax.Raw
open Asai.Range
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

type wrapped_fixity = Fixity : ('left, 'tight, 'right) fixity -> wrapped_fixity

val fixprops : ('left, 'tight, 'right) fixity -> 'left openness * 'tight No.t * 'right openness

type space =
  [ `None | `Break | `Nobreak | `Custom of (string * int * string) * (string * int * string) ]

type (_, _) tree =
  | Inner : ('t, 's) branch -> ('t, 's) tree
  | Done_open : ('t, 's, 'tight) No.lt * ('left opn, 'tight, 'right) notation -> ('t, 's) tree
  | Done_closed : (closed, 'tight, 'right) notation -> ('t, 's) tree
  | Lazy : ('t, 's) tree Lazy.t -> ('t, 's) tree

and ('t, 's) branch = {
  ops : ('t, 's) tree TokMap.t;
  field : ('t, 's) tree option;
  term : ('t, 's) tree TokMap.t option;
}

and ('t, 's) entry = ('t, 's) tree TokMap.t
and observation = Term : ('lt, 'ls, 'rt, 'rs) parse located -> observation
and ('left, 'tight, 'right, 'lt, 'ls, 'rt, 'rs) parsed_notn

and (_, _, _, _) parse =
  | Notn : ('left, 'tight, 'right, 'lt, 'ls, 'rt, 'rs) parsed_notn -> ('lt, 'ls, 'rt, 'rs) parse
  | App : {
      fn : ('lt, 'ls, No.plus_omega, No.nonstrict) parse located;
      arg : (No.plus_omega, No.strict, 'rt, 'rs) parse located;
      left_ok : ('lt, 'ls, No.plus_omega) No.lt;
      right_ok : ('rt, 'rs, No.plus_omega) No.lt;
    }
      -> ('lt, 'ls, 'rt, 'rs) parse
  | Placeholder : Whitespace.t list -> ('lt, 'ls, 'rt, 'rs) parse
  | Ident : string list * Whitespace.t list -> ('lt, 'ls, 'rt, 'rs) parse
  | Constr : string * Whitespace.t list -> ('lt, 'ls, 'rt, 'rs) parse
  | Field : string * string list * Whitespace.t list -> ('lt, 'ls, 'rt, 'rs) parse
  | Superscript :
      ('lt, 'ls, No.plus_omega, No.strict) parse located option * string * Whitespace.t list
      -> ('lt, 'ls, 'rt, 'rs) parse

and ('left, 'tight) notation_entry =
  | Open_entry : ('tight, No.nonstrict) entry -> ('strict opn, 'tight) notation_entry
  | Closed_entry : (No.plus_omega, No.strict) entry -> (closed, 'tight) notation_entry

and ('left, 'tight, 'right) notation

and processor = {
  process :
    'n.
    (string option, 'n) Bwv.t ->
    observation list ->
    Asai.Range.t option ->
    Whitespace.alist ->
    'n check located;
}

and printer = space -> Format.formatter -> observation list -> Whitespace.alist -> unit

module Notation : sig
  type t = Wrap : ('left, 'tight, 'right) notation -> t
end

val empty_branch : ('left, 'tight) branch

val infix :
  notn:('a opn, 'b, 'c opn) notation ->
  ws:Whitespace.alist ->
  first:('d, 'e, 'b, 'a) parse located ->
  inner:observation Bwd.t ->
  last:('b, 'c, 'f, 'g) parse located ->
  left_ok:('d, 'e, 'b) Util.No.lt ->
  right_ok:('f, 'g, 'b) Util.No.lt ->
  ('d, 'e, 'f, 'g) parse

val prefix :
  notn:(closed, 'a, 'b opn) notation ->
  ws:Whitespace.alist ->
  inner:observation Bwd.t ->
  last:('a, 'b, 'c, 'd) parse located ->
  right_ok:('c, 'd, 'a) Util.No.lt ->
  ('e, 'f, 'c, 'd) parse

val postfix :
  notn:('a opn, 'b, closed) notation ->
  ws:Whitespace.alist ->
  first:('c, 'd, 'b, 'a) parse located ->
  inner:observation Bwd.t ->
  left_ok:('c, 'd, 'b) Util.No.lt ->
  ('c, 'd, 'e, 'f) parse

val outfix :
  notn:(closed, 'a, closed) notation ->
  ws:Whitespace.alist ->
  inner:observation Bwd.t ->
  ('b, 'c, 'd, 'e) parse

val args : ('left, 'tight, 'right, 'lt, 'ls, 'rt, 'rs) parsed_notn -> observation list
val whitespace : ('left, 'tight, 'right, 'lt, 'ls, 'rt, 'rs) parsed_notn -> Whitespace.alist

val notn :
  ('left, 'tight, 'right, 'lt, 'ls, 'rt, 'rs) parsed_notn -> ('left, 'tight, 'right) notation

type ('lt, 'ls) right_wrapped_parse = {
  get : 'rt 'rs. ('rt, 'rs) Interval.tt -> (('lt, 'ls, 'rt, 'rs) parse located, string) Result.t;
}

val name : ('left, 'tight, 'right) notation -> string
val tightness : ('left, 'tight, 'right) notation -> 'tight No.t
val left : ('left, 'tight, 'right) notation -> 'left openness
val right : ('left, 'tight, 'right) notation -> 'right openness
val interval_left : ('s opn, 'tight, 'right) notation -> ('tight, 's) Interval.tt
val interval_right : ('left, 'tight, 's opn) notation -> ('tight, 's) Interval.tt
val tree : ('left, 'tight, 'right) notation -> ('left, 'tight) notation_entry
val set_tree : ('left, 'tight, 'right) notation -> ('left, 'tight) notation_entry -> unit
val processor : ('left, 'tight, 'right) notation -> processor
val set_processor : ('left, 'tight, 'right) notation -> processor -> unit
val print : ('left, 'tight, 'right) notation -> printer option
val set_print : ('left, 'tight, 'right) notation -> printer -> unit
val print_as_case : ('left, 'tight, 'right) notation -> printer option
val set_print_as_case : ('left, 'tight, 'right) notation -> printer -> unit
val make : string -> ('left, 'tight, 'right) fixity -> ('left, 'tight, 'right) notation
val equal : ('l1, 't1, 'r1) notation -> ('l2, 't2, 'r2) notation -> bool

type (_, _) notation_in_interval =
  | Open_in_interval :
      ('lt, 'ls, 'tight) No.lt * ('left opn, 'tight, 'right) notation
      -> ('lt, 'ls) notation_in_interval
  | Closed_in_interval : (closed, 'tight, 'right) notation -> ('lt, 'ls) notation_in_interval

val split_ending_whitespace :
  ('lt, 'ls, 'rt, 'rs) parse located -> ('lt, 'ls, 'rt, 'rs) parse located * Whitespace.t list

(*  *)
val op : TokMap.key -> ('t, 's) tree -> ('t, 's) tree
val ops : (TokMap.key * ('t, 's) tree) list -> ('t, 's) tree
val term : TokMap.key -> ('t, 's) tree -> ('t, 's) tree
val terms : (TokMap.key * ('t, 's) tree) list -> ('t, 's) tree
val field : ('t, 's) tree -> ('t, 's) tree
val of_entry : ('t, 's) tree TokMap.t -> ('t, 's) tree
val done_open : ('left opn, 'tight, 'right) notation -> ('tight, No.nonstrict) tree
val eop : TokMap.key -> 'a -> 'a TokMap.t
val eops : (TokMap.key * 'a) list -> 'a TokMap.t
val empty_entry : 'a TokMap.t

(*  *)
val lower : ('t2, 's2, 't1, 's1) Interval.subset -> ('t2, 's2) entry -> ('t1, 's1) entry

val merge :
  ('t2, 's2, 't1, 's1) Interval.subset -> ('t1, 's1) entry -> ('t2, 's2) entry -> ('t1, 's1) entry
