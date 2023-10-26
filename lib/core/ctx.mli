open Util

type (_, _) t

val level : ('a, 'b) t -> int
val empty : (N.zero, N.zero) t
val levels : ('a, 'b) t -> (int option, 'b) Bwv.t
val lookup : ('a, 'b) t -> 'a N.index -> int option * Value.normal * 'b N.index

(* val env : ('a, 'b) t -> (Dim.D.zero, 'b) Value.env *)
val eval : ('a, 'b) t -> 'b Term.term -> Value.value
val ext : ('a, 'b) t -> Value.value -> ('a N.suc, 'b N.suc) t
val ext_let : ('a, 'b) t -> Value.normal -> ('a N.suc, 'b N.suc) t

val exts :
  ('a, 'd) t ->
  ('a, 'b, 'ab) N.plus ->
  ('d, 'b, 'db) N.plus ->
  (int option * Value.normal, 'b) Bwv.t ->
  ('ab, 'db) t

val ext_tel :
  ('a, 'e) t ->
  (Dim.D.zero, 'b) Value.env ->
  ('b, 'c, 'bc) Telescope.t ->
  ('a, 'c, 'ac) N.plus ->
  ('e, 'c, 'ec) N.plus ->
  ('ac, 'ec) t * (Dim.D.zero, 'bc) Value.env * (Value.value, 'c) Bwv.t

val bind_some : (int -> Value.normal option) -> ('a, 'e) t -> ('a, 'e) t
