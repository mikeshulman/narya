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
and observation = Term : ('lt, 'ls, 'rt, 'rs) parse -> observation
and ('left, 'tight, 'right, 'lt, 'ls, 'rt, 'rs) parsed_notn

and (_, _, _, _) parse =
  | Notn : ('left, 'tight, 'right, 'lt, 'ls, 'rt, 'rs) parsed_notn -> ('lt, 'ls, 'rt, 'rs) parse
  | App : {
      fn : ('lt, 'ls, No.plus_omega, No.nonstrict) parse;
      arg : (No.plus_omega, No.strict, 'rt, 'rs) parse;
      left_ok : ('lt, 'ls, No.plus_omega) No.lt;
      right_ok : ('rt, 'rs, No.plus_omega) No.lt;
    }
      -> ('lt, 'ls, 'rt, 'rs) parse
  | Placeholder : ('lt, 'ls, 'rt, 'rs) parse
  | Ident : string -> ('lt, 'ls, 'rt, 'rs) parse
  | Constr : string -> ('lt, 'ls, 'rt, 'rs) parse
  | Field : string -> ('lt, 'ls, 'rt, 'rs) parse
  | Numeral : Q.t -> ('lt, 'ls, 'rt, 'rs) parse

and ('left, 'tight) notation_entry =
  | Open_entry : ('tight, No.nonstrict) entry -> ('strict opn, 'tight) notation_entry
  | Closed_entry : (No.plus_omega, No.strict) entry -> (closed, 'tight) notation_entry

and ('left, 'tight, 'right) notation
and processor = { process : 'n. (string option, 'n) Bwv.t -> observation list -> 'n check }

val empty_branch : ('left, 'tight) branch

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

val notn :
  ('left, 'tight, 'right, 'lt, 'ls, 'rt, 'rs) parsed_notn -> ('left, 'tight, 'right) notation

type ('lt, 'ls) right_wrapped_parse = {
  get : 'rt 'rs. ('rt, 'rs) Interval.tt -> (('lt, 'ls, 'rt, 'rs) parse, string) Result.t;
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

type (_, _) notation_in_interval =
  | Open_in_interval :
      ('lt, 'ls, 'tight) No.lt * ('left opn, 'tight, 'right) notation
      -> ('lt, 'ls) notation_in_interval
  | Closed_in_interval : (closed, 'tight, 'right) notation -> ('lt, 'ls) notation_in_interval

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
