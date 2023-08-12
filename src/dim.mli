module Endpoints : sig
  type len
  type t

  val len : len N.t
  val indices : (t, len) Bwv.t
end

open Monoid
module D : MonoidPos

val compare : 'm D.t -> 'n D.t -> ('m, 'n) compare

type (_, _) factor = Factor : ('n, 'k, 'nk) D.plus -> ('nk, 'n) factor

val factor : 'nk D.t -> 'n D.t -> ('nk, 'n) factor option
val epi : 'k D.t -> ('k, 'm, 'l) D.plus -> ('k, 'n, 'l) D.plus -> ('m, 'n) Monoid.eq
val zero_uniq : 'm D.t -> ('m, 'z, 'm) D.plus -> ('z, D.zero) Monoid.eq

type (_, _) pushout = Pushout : ('a, 'c, 'p) D.plus * ('b, 'd, 'p) D.plus -> ('a, 'b) pushout

val pushout : 'a D.t -> 'b D.t -> ('a, 'b) pushout

type (_, _) deg

val dom_deg : ('m, 'n) deg -> 'm D.t
val cod_deg : ('m, 'n) deg -> 'n D.t
val id_deg : 'n D.t -> ('n, 'n) deg
val comp_deg : ('b, 'c) deg -> ('a, 'b) deg -> ('a, 'c) deg
val deg_plus : ('m, 'n) deg -> ('n, 'k, 'nk) D.plus -> ('m, 'k, 'mk) D.plus -> ('mk, 'nk) deg
val deg_plus_dom : ('m, 'n) deg -> ('m, 'k, 'mk) D.plus -> ('mk, 'n) deg

val deg_plus_deg :
  ('k, 'm) deg -> ('m, 'n, 'mn) D.plus -> ('k, 'l, 'kl) D.plus -> ('l, 'n) deg -> ('kl, 'mn) deg

val plus_deg :
  'm D.t -> ('m, 'n, 'mn) D.plus -> ('m, 'l, 'ml) D.plus -> ('l, 'n) deg -> ('ml, 'mn) deg

val is_id_deg : ('m, 'n) deg -> unit option
val pos_deg : 'n D.pos -> ('m, 'n) deg -> 'm D.pos
val deg_equiv : ('m, 'n) deg -> ('k, 'l) deg -> unit option

type 'n perm = ('n, 'n) deg

val dim_perm : 'n perm -> 'n D.t
val id_perm : 'n D.t -> 'n perm
val comp_perm : 'a perm -> 'a perm -> 'a perm
val perm_plus : 'm perm -> ('m, 'k, 'mk) D.plus -> 'mk perm
val perm_plus_perm : 'm perm -> ('m, 'n, 'mn) D.plus -> 'n perm -> 'mn perm
val plus_perm : 'm D.t -> ('m, 'n, 'mn) D.plus -> 'n perm -> 'mn perm
val is_id_perm : 'n perm -> unit option
val perm_equiv : 'm perm -> 'n perm -> unit option
val switch_perm : 'm D.t -> ('m, 'n, 'mn) D.plus -> 'mn perm
val perm_inv : 'm perm -> 'm perm

type _ deg_of = Of : ('m, 'n) deg -> 'n deg_of
type _ deg_of_plus = Of : ('n, 'k, 'nk) D.plus * ('m, 'nk) deg -> 'n deg_of_plus

val comp_deg_of_plus : ('m, 'n) deg -> 'm deg_of_plus -> 'n deg_of_plus
val reduce_deg_of_plus : 'n deg_of_plus -> 'n deg_of_plus

type (_, _) deg_extending =
  | DegExt : ('k, 'j, 'kj) D.plus * ('n, 'i, 'ni) D.plus * ('kj, 'ni) deg -> ('k, 'n) deg_extending

val comp_deg_extending : ('m, 'n) deg -> ('k, 'l) deg -> ('k, 'n) deg_extending

type any_deg = Any : ('m, 'n) deg -> any_deg

val comp_deg_of_plus_any : 'n deg_of_plus -> any_deg -> 'n deg_of_plus
val any_deg_plus : any_deg -> 'k D.t -> any_deg
val any_of_deg_of_plus : 'n deg_of_plus -> any_deg

type (_, _) sface

val id_sface : 'n D.t -> ('n, 'n) sface
val dom_sface : ('m, 'n) sface -> 'm D.t
val cod_sface : ('m, 'n) sface -> 'n D.t
val comp_sface : ('n, 'k) sface -> ('m, 'n) sface -> ('m, 'k) sface
val sface_zero : ('n, D.zero) sface -> ('n, D.zero) Monoid.eq

val sface_plus_sface :
  ('k, 'm) sface ->
  ('m, 'n, 'mn) D.plus ->
  ('k, 'p, 'kp) D.plus ->
  ('p, 'n) sface ->
  ('kp, 'mn) sface

type _ sface_of = SFace_of : ('m, 'n) sface -> 'n sface_of

val sface_plus : ('k, 'm) sface -> ('m, 'n, 'mn) D.plus -> ('k, 'n, 'kn) D.plus -> ('kn, 'mn) sface

val plus_sface :
  'n D.t -> ('n, 'm, 'nm) D.plus -> ('n, 'k, 'nk) D.plus -> ('k, 'm) sface -> ('nk, 'nm) sface

type (_, _, _) sface_of_plus =
  | SFace_of_plus :
      ('m, 'l, 'ml) D.plus * ('m, 'n) sface * ('l, 'k) sface
      -> ('ml, 'n, 'k) sface_of_plus

val sface_of_plus : ('n, 'k, 'nk) D.plus -> ('ml, 'nk) sface -> ('ml, 'n, 'k) sface_of_plus

type ('n, 'f) count_faces
type _ has_faces = Faces : ('n, 'f) count_faces -> 'n has_faces

val count_faces : 'n D.t -> 'n has_faces
val faces_zero : (D.zero, N.one) count_faces
val dim_faces : ('n, 'f) count_faces -> 'n D.t
val faces_pos : ('n, 'f) count_faces -> 'f N.pos
val faces_out : ('n, 'f) count_faces -> 'f N.t
val faces_uniq : ('n, 'f1) count_faces -> ('n, 'f2) count_faces -> ('f1, 'f2) Monoid.eq
val sfaces : ('n, 'f) count_faces -> ('n sface_of, 'f) Bwv.t
(* val sface_int : ('n, 'f) count_faces -> 'n sface_of -> int *)

type _ dbl_sfaces_of =
  | DblOf : ('m, 'f) count_faces * ('m sface_of, 'f) Bwv.t * ('m, 'n) sface -> 'n dbl_sfaces_of

val dbl_sfaces : ('n, 'f) count_faces -> ('n dbl_sfaces_of, 'f) Bwv.t

val sfaces_plus :
  ('m, 'n, 'mn) D.plus ->
  ('m, 'fm) count_faces ->
  ('n, 'fn) count_faces ->
  ('mn, 'fmn) count_faces ->
  ('a -> 'b -> 'c) ->
  ('a, 'fm) Bwv.t ->
  ('b, 'fn) Bwv.t ->
  ('c, 'fmn) Bwv.t

module Tree : sig
  type ('f, 'n) t

  val nth : ('f, 'n) t -> ('k, 'n) sface -> ('f, 'k) Appl.ied

  type ('f, 'n) builder = { leaf : 'm. ('m, 'n) sface -> ('f, 'm) Appl.ied }

  val build : 'n D.t -> ('f, 'n) builder -> ('f, 'n) t

  type ('f1, 'f2, 'n) mapper = {
    map : 'm. ('m, 'n) sface -> ('f1, 'm) Appl.ied -> ('f2, 'm) Appl.ied;
  }

  val map : 'n D.t -> ('f1, 'f2, 'n) mapper -> ('f1, 'n) t -> ('f2, 'n) t

  type ('f, 'n) iterator = { it : 'm. ('m, 'n) sface -> ('f, 'm) Appl.ied -> unit }

  val iter : 'n D.t -> ('f, 'n) iterator -> ('f, 'n) t -> unit

  type ('f, 'n) iteratorOpt = { it : 'm. ('m, 'n) sface -> ('f, 'm) Appl.ied -> unit option }

  val iterOpt : 'n D.t -> ('f, 'n) iteratorOpt -> ('f, 'n) t -> unit option

  type ('f1, 'f2, 'n) iteratorOpt2 = {
    it : 'm. ('m, 'n) sface -> ('f1, 'm) Appl.ied -> ('f2, 'm) Appl.ied -> unit option;
  }

  val iterOpt2 : 'n D.t -> ('f1, 'f2, 'n) iteratorOpt2 -> ('f1, 'n) t -> ('f2, 'n) t -> unit option
end

type (_, _, _) count_tube =
  | Tube : {
      plus_dim : ('m, 'n, 'mn) D.plus;
      total_faces : ('mn, 'mnf) count_faces;
      missing_faces : ('m, 'mf) count_faces;
      plus_faces : ('f, 'mf, 'mnf) N.plus;
    }
      -> ('m, 'n, 'f) count_tube

val tube_uninst : ('m, 'n, 'f) count_tube -> 'm D.t
val tube_inst : ('m, 'n, 'f) count_tube -> 'n D.t
val tube_zero : (D.zero, D.zero, N.zero) count_tube

type (_, _) has_tube = Has_tube : ('m, 'n, 'f) count_tube -> ('m, 'n) has_tube

val has_tube : 'm D.t -> 'n D.t -> ('m, 'n) has_tube

type (_, _, _, _, _, _) tube_plus_tube =
  | Tube_plus_tube :
      ('n, 'k, 'nk) D.plus * ('m, 'nk, 'fm) count_tube * ('fmnk, 'fmn, 'fm) N.plus * ('a, 'fm) Bwv.t
      -> ('m, 'n, 'k, 'fmnk, 'fmn, 'a) tube_plus_tube

val tube_plus_tube :
  ('m, 'n, 'mn) D.plus ->
  ('mn, 'k, 'fmnk) count_tube ->
  ('m, 'n, 'fmn) count_tube ->
  ('a, 'fmnk) Bwv.t ->
  ('a, 'fmn) Bwv.t ->
  ('m, 'n, 'k, 'fmnk, 'fmn, 'a) tube_plus_tube

type (_, _, _) take_tube =
  | Take :
      ('m, 'n, 'mn) D.plus
      * ('m, 'mf) count_faces
      * ('f, 'mf, 'mnf) N.plus
      * ('a, 'f) Bwv.t
      * 'a list
      -> ('a, 'mn, 'mnf) take_tube

val take_tube : ('n, 'f) count_faces -> 'a list -> ('a, 'n, 'f) take_tube

type (_, _) face = Face : ('m, 'n) sface * 'm perm -> ('m, 'n) face

val id_face : 'n D.t -> ('n, 'n) face
val perm_sface : 'n perm -> ('m, 'n) sface -> ('m, 'n) face
val comp_face : ('n, 'k) face -> ('m, 'n) face -> ('m, 'k) face
val dom_face : ('m, 'n) face -> 'm D.t
val cod_face : ('m, 'n) face -> 'n D.t
val face_of_sface : ('m, 'n) sface -> ('m, 'n) face
val face_of_perm : 'm perm -> ('m, 'm) face

val face_plus_face :
  ('k, 'm) face -> ('m, 'n, 'mn) D.plus -> ('k, 'l, 'kl) D.plus -> ('l, 'n) face -> ('kl, 'mn) face

type _ face_of = Face_of : ('m, 'n) face -> 'n face_of
type (_, _) op = Op : ('n, 'k) sface * ('m, 'n) deg -> ('m, 'k) op

val id_op : 'n D.t -> ('n, 'n) op
val deg_sface : ('n, 'k) deg -> ('m, 'n) sface -> ('m, 'k) op
val comp_op : ('n, 'k) op -> ('m, 'n) op -> ('m, 'k) op
val dom_op : ('m, 'n) op -> 'm D.t
val cod_op : ('m, 'n) op -> 'n D.t
val op_of_deg : ('m, 'n) deg -> ('m, 'n) op
val op_of_sface : ('m, 'n) sface -> ('m, 'n) op

val op_plus_op :
  ('k, 'm) op -> ('m, 'n, 'mn) D.plus -> ('k, 'l, 'kl) D.plus -> ('l, 'n) op -> ('kl, 'mn) op

type _ op_of = Of : ('m, 'n) op -> 'n op_of
type _ op_of_plus = Of : ('m, 'n) sface * 'm deg_of_plus -> 'n op_of_plus

val comp_op_of : ('m, 'n) op -> 'm op_of -> 'n op_of
val comp_op_deg_of_plus : ('m, 'n) op -> 'm deg_of_plus -> 'n op_of_plus

type (_, _, _) insertion

val zero_ins : 'a D.t -> ('a, 'a, D.zero) insertion
val dom_ins : ('a, 'b, 'c) insertion -> 'a D.t
val plus_of_ins : ('a, 'b, 'c) insertion -> ('b, 'c, 'a) D.plus
val deg_of_ins : ('a, 'b, 'c) insertion -> ('b, 'c, 'bc) D.plus -> ('a, 'bc) deg
val perm_of_ins : ('a, 'b, 'c) insertion -> 'a perm
val deg_of_plus_of_ins : ('a, 'b, 'c) insertion -> 'b deg_of_plus

type (_, _, _) insfact = Insfact : ('a, 'b) deg * ('ac, 'a, 'c) insertion -> ('ac, 'b, 'c) insfact

val comp_insfact : ('ac, 'b, 'c) insfact -> ('b, 'c, 'bc) D.plus -> ('ac, 'bc) deg
val insfact : ('ac, 'bc) deg -> ('b, 'c, 'bc) D.plus -> ('ac, 'b, 'c) insfact

type one

val one : one D.t
val pos_one : one D.pos
val faces_one : (one, N.three) count_faces
val tube_one : (D.zero, one, N.two) count_tube
val refl : (one, D.zero) deg

type two

val two : two D.t
val sym : (two, two) deg
