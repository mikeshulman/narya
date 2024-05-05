open Bwd
open Util
open Tbwd
open Dim
open Syntax
open Term
open Value

module Binding : sig
  type t

  val make : level option -> normal -> t
  val level : t -> level option
  val value : t -> normal
end

type (_, _) t

val vis :
  ('a, 'b) t ->
  'm D.t ->
  ('m, 'n, 'mn) D.plus ->
  ('a, 'f, 'af) N.plus ->
  (N.zero, 'n, string option, 'f) NICubeOf.t ->
  ('mn, Binding.t) CubeOf.t ->
  ('af, ('b, 'mn) snoc) t

val cube_vis :
  ('a, 'b) t -> string option -> ('n, Binding.t) CubeOf.t -> ('a N.suc, ('b, 'n) snoc) t

val invis : ('a, 'b) t -> ('n, Binding.t) CubeOf.t -> ('a, ('b, 'n) snoc) t
val lock : ('a, 'b) t -> ('a, 'b) t
val raw_length : ('a, 'b) t -> 'a N.t
val length : ('a, 'b) t -> int
val empty : (N.zero, emp) t
val apps : ('a, 'b) t -> app Bwd.t
val lookup : ('a, 'b) t -> 'a Raw.index -> level option * normal * 'b index
val find_level : ('a, 'b) t -> level -> 'b index option
val env : ('a, 'b) t -> (D.zero, 'b) env
val eval : ('a, 'b) t -> ('b, 's) Term.term -> 's evaluation
val eval_term : ('a, 'b) t -> ('b, kinetic) Term.term -> kinetic value
val ext : ('a, 'b) t -> string option -> kinetic value -> ('a N.suc, ('b, D.zero) snoc) t
val ext_let : ('a, 'b) t -> string option -> normal -> ('a N.suc, ('b, D.zero) snoc) t

type eval_readback = {
  nf : 'a 'b. oldctx:('a, 'b) t -> newctx:('a, 'b) t -> normal -> normal option;
  ty : 'a 'b. oldctx:('a, 'b) t -> newctx:('a, 'b) t -> kinetic value -> kinetic value option;
}

type (_, _) bind_some =
  | Bind_some : {
      checked_perm : ('c, 'b) Tbwd.permute;
      oldctx : ('a, 'c) t;
      newctx : ('a, 'c) t;
    }
      -> ('a, 'b) bind_some
  | None : ('a, 'b) bind_some

val bind_some : eval_readback -> (level -> normal option) -> ('a, 'e) t -> ('a, 'e) bind_some
val names : ('a, 'b) t -> 'b Names.t
val lookup_name : ('a, 'b) t -> 'b index -> string list
val lam : ('a, 'b) t -> ('b, potential) term -> (emp, potential) term
