open Util
open Core

type 'n t

val empty : N.zero t
val ext : 'n t -> string option -> 'n N.suc t
val ext_fields : 'n t -> string option -> (string, Field.t) Abwd.t -> 'n N.suc t
val find : string -> 'n t -> [ `Var of 'n N.index | `Field of 'n N.index * Field.t | `None ]
val top : 'n N.suc t -> 'n t * string option

type _ bappend_plus =
  | Bappend_plus : ('n, 'm, 'nm) Fwn.bplus * (string option, 'm) Vec.t * 'nm t -> 'n bappend_plus

val bappend_plus : 'n t -> string option list -> 'n bappend_plus

type _ append_plus =
  | Append_plus : ('n, 'm, 'nm) N.plus * (string option, 'm) Bwv.t * 'nm t -> 'n append_plus

val append_plus : 'n t -> string option list -> 'n append_plus
