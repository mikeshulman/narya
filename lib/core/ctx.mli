open Bwd
open Util
open Tbwd
open Dim
open Syntax
open Term
open Value

type (_, _) t

val vis :
  ('a, 'b) t -> 'n variables -> ('n, level option * normal) CubeOf.t -> ('a N.suc, ('b, 'n) snoc) t

val invis : ('a, 'b) t -> ('n, level option * normal) CubeOf.t -> ('a, ('b, 'n) snoc) t

val split :
  ('a, 'b) t ->
  ('n, 'f) count_faces ->
  ('a, 'f, 'af) N.plus ->
  'n variables ->
  ('n, level option * normal) CubeOf.t ->
  ('af, ('b, 'n) snoc) t

val length : ('a, 'b) t -> int
val empty : (N.zero, emp) t
val lookup : ('a, 'b) t -> 'a Raw.index -> level option * normal * 'b index

val lookup_face :
  ('a, 'f, 'af) N.plus ->
  ('n sface_of, 'f) Bwv.t ->
  ('a, 'b) t ->
  ('n, level option * normal) CubeOf.t ->
  'af Raw.index ->
  level option * normal * ('b, 'n) snoc index

val lookup_invis : ('a, 'b) t -> 'b index -> level option * normal
val find_level : ('a, 'b) t -> level -> 'b index option
val env : ('a, 'b) t -> (D.zero, 'b) env
val eval : ('a, 'b) t -> ('b, 's) Term.term -> 's evaluation
val eval_term : ('a, 'b) t -> ('b, kinetic) Term.term -> kinetic value
val ext : ('a, 'b) t -> string option -> kinetic value -> ('a N.suc, ('b, D.zero) snoc) t
val ext_let : ('a, 'b) t -> string option -> normal -> ('a N.suc, ('b, D.zero) snoc) t

val ext_tel :
  ('a, 'e) t ->
  ('n, 'b) env ->
  (string option, 'c) Vec.t ->
  ('b, 'c, 'bc) Telescope.t ->
  ('a, 'c, 'ac) Fwn.bplus ->
  ('e, 'c, 'n, 'ec) Tbwd.snocs ->
  ('ac, 'ec) t * ('n, 'bc) env * ('n, kinetic value) CubeOf.t Bwd.t

val bind_some : (level -> normal option) -> ('a, 'e) t -> ('a, 'e) t
val map : (normal -> normal) -> ('a, 'b) t -> ('a, 'b) t
val names : ('a, 'b) t -> 'b Names.t
val lookup_name : ('a, 'b) t -> 'b index -> string list
val lam : ('a, 'b) t -> ('b, potential) term -> (emp, potential) term
val pp_ctx : Format.formatter -> ('a, 'b) t -> unit
