open Util
open Dim
open Term
open Value

type 'a t

val level : 'a t -> int
val empty : N.zero t
val levels : 'a t -> (int option, 'a) Bwv.t
val lookup : 'a t -> 'a N.index -> int option * normal
val env : 'a t -> (D.zero, 'a) env
val eval : 'a t -> 'a term -> value
val ext : 'a t -> value -> 'a N.suc t
val ext_let : 'a t -> normal -> 'a N.suc t
val exts : 'a t -> ('a, 'b, 'ab) N.plus -> (int option * normal, 'b) Bwv.t -> 'ab t

val ext_tel :
  'a t ->
  (D.zero, 'b) env ->
  ('b, 'c, 'bc) Telescope.t ->
  ('a, 'c, 'ac) N.plus ->
  'ac t * (D.zero, 'bc) env * (value, 'c) Bwv.t

val bind_some : (int -> normal option) -> 'a t -> 'a t
