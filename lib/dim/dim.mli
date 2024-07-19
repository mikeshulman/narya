open Bwd
open Util
open Signatures
open Tlist
open Tbwd
open Monoid
module D : MonoidPos
module Dmap : MAP_MAKER with module Key := D

type dim_wrapped = Wrap : 'n D.t -> dim_wrapped

module Endpoints : sig
  type 'l len
  type wrapped = Wrap : 'l len -> wrapped

  val run :
    arity:int -> refl_char:char -> refl_names:string list -> internal:bool -> (unit -> 'a) -> 'a

  val wrapped : unit -> wrapped
  val internal : unit -> bool
end

type any_dim = Any : 'n D.t -> any_dim

val dim_of_string : string -> any_dim option
val string_of_dim : 'n D.t -> string
val is_pos : 'a D.t -> bool

type (_, _) factor = Factor : ('n, 'k, 'nk) D.plus -> ('nk, 'n) factor

val factor : 'nk D.t -> 'n D.t -> ('nk, 'n) factor option

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

val is_id_deg : ('m, 'n) deg -> ('m, 'n) Eq.t option
val pos_deg : 'n D.pos -> ('m, 'n) deg -> 'm D.pos
val deg_equiv : ('m, 'n) deg -> ('k, 'l) deg -> unit option
val deg_zero : 'a D.t -> ('a, D.zero) deg

type (_, _) perm

val deg_of_perm : ('m, 'n) perm -> ('m, 'n) deg
val perm_of_deg : ('m, 'n) deg -> ('m, 'n) perm option
val perm_inv : ('m, 'n) perm -> ('n, 'm) perm

type (_, _, _) deg_perm_of_plus =
  | Deg_perm_of_plus :
      ('m, 'k, 'mk) D.plus * ('m, 'n) deg * ('k, 'l) perm
      -> ('mk, 'n, 'l) deg_perm_of_plus
  | None_deg_perm_of_plus : ('mk, 'n, 'k) deg_perm_of_plus

val deg_perm_of_plus : ('n, 'k, 'nk) D.plus -> ('mk, 'nk) deg -> ('mk, 'n, 'k) deg_perm_of_plus

type _ perm_to = Perm_to : ('a, 'b) perm -> 'a perm_to
type _ deg_of = Of : ('m, 'n) deg -> 'n deg_of
type _ deg_of_plus = Of : ('n, 'k, 'nk) D.plus * ('m, 'nk) deg -> 'n deg_of_plus

val comp_deg_of_plus : ('m, 'n) deg -> 'm deg_of_plus -> 'n deg_of_plus

type (_, _) deg_extending =
  | DegExt : ('k, 'j, 'kj) D.plus * ('n, 'i, 'ni) D.plus * ('kj, 'ni) deg -> ('k, 'n) deg_extending

val comp_deg_extending : ('m, 'n) deg -> ('k, 'l) deg -> ('k, 'n) deg_extending

type any_deg = Any_deg : ('m, 'n) deg -> any_deg
type _ deg_to = To : ('m, 'n) deg -> 'm deg_to

val string_of_deg : ('a, 'b) deg -> string
val deg_of_string : string -> any_deg option

type (_, _) sface

val id_sface : 'n D.t -> ('n, 'n) sface
val dom_sface : ('m, 'n) sface -> 'm D.t
val cod_sface : ('m, 'n) sface -> 'n D.t
val is_id_sface : ('m, 'n) sface -> ('m, 'n) Eq.t option
val comp_sface : ('n, 'k) sface -> ('m, 'n) sface -> ('m, 'k) sface
val sface_zero : ('n, D.zero) sface -> ('n, D.zero) Eq.t

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

type any_sface = Any_sface : ('n, 'k) sface -> any_sface

val string_of_sface : ('n, 'k) sface -> string
val sface_of_string : string -> any_sface option

module Cube (F : Fam2) : sig
  type ('m, 'n, 'b) gt
  type ('n, 'b) t = ('n, 'n, 'b) gt

  val dim : ('n, 'b) t -> 'n D.t
  val singleton : (D.zero, 'b) F.t -> (D.zero, 'b) t
  val find : ('n, 'b) t -> ('k, 'n) sface -> ('k, 'b) F.t
  val find_top : ('n, 'b) t -> ('n, 'b) F.t

  module Heter : sig
    type (_, _) hft =
      | [] : ('n, nil) hft
      | ( :: ) : ('n, 'x) F.t * ('n, 'xs) hft -> ('n, ('x, 'xs) cons) hft

    type (_, _, _) hgt =
      | [] : ('m, 'n, nil) hgt
      | ( :: ) : ('m, 'n, 'x) gt * ('m, 'n, 'xs) hgt -> ('m, 'n, ('x, 'xs) cons) hgt

    (* val hft_nil : ('n, Hlist.nil) hft *)
    (* val hft_cons : ('n, 'x) F.t -> ('n, 'xs) hft -> ('n, ('x, 'xs) Hlist.cons) hft *)
  end

  module Infix : sig
    val hnil : ('n, nil) Heter.hft
    val ( @: ) : ('n, 'x) F.t -> ('n, 'xs) Heter.hft -> ('n, ('x, 'xs) cons) Heter.hft
  end

  module Applicatic (M : Applicative.Plain) : sig
    type ('n, 'bs, 'cs) pmapperM = {
      map : 'm. ('m, 'n) sface -> ('m, 'bs) Heter.hft -> ('m, 'cs) Heter.hft M.t;
    }

    val pmapM :
      ('n, ('b, 'bs) cons, 'cs) pmapperM ->
      ('n, 'n, ('b, 'bs) cons) Heter.hgt ->
      'cs Tlist.t ->
      ('n, 'n, 'cs) Heter.hgt M.t

    type ('n, 'bs, 'c) mmapperM = {
      map : 'm. ('m, 'n) sface -> ('m, 'bs) Heter.hft -> ('m, 'c) F.t M.t;
    }

    val mmapM :
      ('n, ('b, 'bs) cons, 'c) mmapperM -> ('n, 'n, ('b, 'bs) cons) Heter.hgt -> ('n, 'c) t M.t

    type ('n, 'bs) miteratorM = { it : 'm. ('m, 'n) sface -> ('m, 'bs) Heter.hft -> unit M.t }

    val miterM : ('n, ('b, 'bs) cons) miteratorM -> ('n, 'n, ('b, 'bs) cons) Heter.hgt -> unit M.t

    type ('n, 'b) builderM = { build : 'm. ('m, 'n) sface -> ('m, 'b) F.t M.t }

    val buildM : 'n D.t -> ('n, 'b) builderM -> ('n, 'b) t M.t
  end

  module Monadic (M : Monad.Plain) : sig
    module A : module type of Applicative.OfMonad (M)
    include module type of Applicatic (A)
  end

  module IdM : module type of Monadic (Monad.Identity)

  val pmap :
    ('n, ('b, 'bs) cons, 'cs) IdM.pmapperM ->
    ('n, 'n, ('b, 'bs) cons) Heter.hgt ->
    'cs Tlist.t ->
    ('n, 'n, 'cs) Heter.hgt

  val mmap :
    ('n, ('b, 'bs) cons, 'c) IdM.mmapperM -> ('n, 'n, ('b, 'bs) cons) Heter.hgt -> ('n, 'c) t

  val miter : ('n, ('b, 'bs) cons) IdM.miteratorM -> ('n, 'n, ('b, 'bs) cons) Heter.hgt -> unit
  val build : 'n D.t -> ('n, 'b) IdM.builderM -> ('n, 'b) t
  val subcube : ('m, 'n) sface -> ('n, 'b) t -> ('m, 'b) t
end

module FamOf : sig
  type ('a, 'b) t = 'b
end

module CubeOf : module type of Cube (FamOf)

type (_, _, _, _) tface

val sface_of_tface : ('m, 'n, 'k, 'nk) tface -> ('m, 'nk) sface
val cod_plus_of_tface : ('m, 'n, 'k, 'nk) tface -> ('n, 'k, 'nk) D.plus
val dom_tface : ('m, 'n, 'k, 'nk) tface -> 'm D.t
val codl_tface : ('m, 'n, 'k, 'nk) tface -> 'n D.t
val codr_tface : ('m, 'n, 'k, 'nk) tface -> 'k D.t
val cod_tface : ('m, 'n, 'k, 'nk) tface -> 'nk D.t

val tface_plus :
  ('m, 'n, 'k, 'nk) tface ->
  ('k, 'l, 'kl) D.plus ->
  ('nk, 'l, 'nkl) D.plus ->
  ('m, 'l, 'ml) D.plus ->
  ('ml, 'n, 'kl, 'nkl) tface

type ('m, 'n) pface = ('m, D.zero, 'n, 'n) tface

val pface_of_sface : ('m, 'n) sface -> [ `Proper of ('m, 'n) pface | `Id of ('m, 'n) Eq.t ]

val sface_plus_tface :
  ('k, 'm) sface ->
  ('m, 'n, 'mn) D.plus ->
  ('m, 'nl, 'mnl) D.plus ->
  ('k, 'p, 'kp) D.plus ->
  ('p, 'n, 'l, 'nl) tface ->
  ('kp, 'mn, 'l, 'mnl) tface

val sface_plus_pface :
  ('k, 'm) sface ->
  ('m, 'n, 'mn) D.plus ->
  ('k, 'p, 'kp) D.plus ->
  ('p, 'n) pface ->
  ('kp, 'm, 'n, 'mn) tface

type (_, _, _, _) tface_of_plus =
  | TFace_of_plus :
      ('p, 'q, 'pq) D.plus * ('p, 'n) sface * ('q, 'k, 'l, 'kl) tface
      -> ('pq, 'n, 'k, 'l) tface_of_plus

val tface_of_plus :
  ('n, 'k, 'nk) D.plus -> ('m, 'nk, 'l, 'nkl) tface -> ('m, 'n, 'k, 'l) tface_of_plus

type (_, _, _) pface_of_plus =
  | PFace_of_plus :
      ('p, 'q, 'pq) D.plus * ('p, 'n) sface * ('q, 'k) pface
      -> ('pq, 'n, 'k) pface_of_plus

val pface_of_plus : ('m, 'n, 'k, 'nk) tface -> ('m, 'n, 'k) pface_of_plus

module Tube (F : Fam2) : sig
  module C : module type of Cube (F)

  type ('n, 'k, 'nk, 'm, 'b) gt
  type ('n, 'k, 'nk, 'b) t = ('n, 'k, 'nk, 'nk, 'b) gt

  val find : ('n, 'k, 'nk, 'b) t -> ('m, 'n, 'k, 'nk) tface -> ('m, 'b) F.t
  val boundary : ('n, 'b) C.t -> (D.zero, 'n, 'n, 'b) t

  val pboundary :
    ('m, 'k, 'mk) D.plus -> ('k, 'l, 'kl) D.plus -> ('m, 'kl, 'mkl, 'b) t -> ('mk, 'l, 'mkl, 'b) t

  val plus : ('m, 'k, 'mk, 'b) t -> ('m, 'k, 'mk) D.plus
  val inst : ('m, 'k, 'mk, 'b) t -> 'k D.t
  val uninst : ('m, 'k, 'mk, 'b) t -> 'm D.t
  val out : ('m, 'k, 'mk, 'b) t -> 'mk D.t
  val empty : 'n D.t -> ('n, D.zero, 'n, 'b) t

  module Heter : sig
    type (_, _, _, _, _) hgt =
      | [] : ('m, 'k, 'mk, 'nk, nil) hgt
      | ( :: ) :
          ('m, 'k, 'mk, 'nk, 'x) gt * ('m, 'k, 'mk, 'nk, 'xs) hgt
          -> ('m, 'k, 'mk, 'nk, ('x, 'xs) cons) hgt
  end

  module Infix : module type of C.Infix

  module Applicatic (M : Applicative.Plain) : sig
    type ('n, 'k, 'nk, 'bs, 'cs) pmapperM = {
      map : 'm. ('m, 'n, 'k, 'nk) tface -> ('m, 'bs) C.Heter.hft -> ('m, 'cs) C.Heter.hft M.t;
    }

    val pmapM :
      ('n, 'k, 'nk, ('b, 'bs) cons, 'cs) pmapperM ->
      ('n, 'k, 'nk, 'nk, ('b, 'bs) cons) Heter.hgt ->
      'cs Tlist.t ->
      ('n, 'k, 'nk, 'nk, 'cs) Heter.hgt M.t

    type ('n, 'k, 'nk, 'bs, 'c) mmapperM = {
      map : 'm. ('m, 'n, 'k, 'nk) tface -> ('m, 'bs) C.Heter.hft -> ('m, 'c) F.t M.t;
    }

    val mmapM :
      ('n, 'k, 'nk, ('b, 'bs) cons, 'c) mmapperM ->
      ('n, 'k, 'nk, 'nk, ('b, 'bs) cons) Heter.hgt ->
      ('n, 'k, 'nk, 'c) t M.t

    type ('n, 'k, 'nk, 'bs) miteratorM = {
      it : 'm. ('m, 'n, 'k, 'nk) tface -> ('m, 'bs) C.Heter.hft -> unit M.t;
    }

    val miterM :
      ('n, 'k, 'nk, ('b, 'bs) cons) miteratorM ->
      ('n, 'k, 'nk, 'nk, ('b, 'bs) cons) Heter.hgt ->
      unit M.t

    type ('n, 'k, 'nk, 'b) builderM = { build : 'm. ('m, 'n, 'k, 'nk) tface -> ('m, 'b) F.t M.t }

    val buildM :
      'n D.t -> ('n, 'k, 'nk) D.plus -> ('n, 'k, 'nk, 'b) builderM -> ('n, 'k, 'nk, 'b) t M.t
  end

  module Monadic (M : Monad.Plain) : sig
    module A : module type of Applicative.OfMonad (M)
    include module type of Applicatic (A)
  end

  module IdM : module type of Monadic (Monad.Identity)

  val pmap :
    ('n, 'k, 'nk, ('b, 'bs) cons, 'cs) IdM.pmapperM ->
    ('n, 'k, 'nk, 'nk, ('b, 'bs) cons) Heter.hgt ->
    'cs Tlist.t ->
    ('n, 'k, 'nk, 'nk, 'cs) Heter.hgt

  val mmap :
    ('n, 'k, 'nk, ('b, 'bs) cons, 'c) IdM.mmapperM ->
    ('n, 'k, 'nk, 'nk, ('b, 'bs) cons) Heter.hgt ->
    ('n, 'k, 'nk, 'c) t

  val miter :
    ('n, 'k, 'nk, ('b, 'bs) cons) IdM.miteratorM ->
    ('n, 'k, 'nk, 'nk, ('b, 'bs) cons) Heter.hgt ->
    unit

  val build :
    'n D.t -> ('n, 'k, 'nk) D.plus -> ('n, 'k, 'nk, 'b) IdM.builderM -> ('n, 'k, 'nk, 'b) t
end

module TubeOf : sig
  include module type of Tube (FamOf)

  val plus_cube : ('mk, 'l, 'mkl, 'b) t -> ('mk, 'b) C.t -> ('mkl, 'b) C.t

  val plus_tube :
    ('k, 'l, 'kl) D.plus -> ('mk, 'l, 'mkl, 'b) t -> ('m, 'k, 'mk, 'b) t -> ('m, 'kl, 'mkl, 'b) t

  val middle :
    ('m, 'k, 'mk) D.plus -> ('k, 'l, 'kl) D.plus -> ('m, 'kl, 'mkl, 'b) t -> ('m, 'k, 'mk, 'b) t

  val append_bwd : 'a Bwd.t -> ('m, 'n, 'mn, 'a) t -> 'a Bwd.t
end

module Icube (F : Fam4) : sig
  type (_, _, _, _, _) gt
  type ('left, 'n, 'b, 'right) t = ('left, 'n, 'n, 'b, 'right) gt

  val dim : ('left, 'n, 'b, 'right) t -> 'n D.t

  module Applicatic (M : Util.Applicative.Plain) : sig
    type ('n, 'b, 'c) mapperM = {
      map :
        'left 'right 'm.
        ('m, 'n) sface -> ('left, 'm, 'b, 'right) F.t -> ('left, 'm, 'c, 'right) F.t M.t;
    }

    val mapM : ('n, 'b, 'c) mapperM -> ('left, 'n, 'b, 'right) t -> ('left, 'n, 'c, 'right) t M.t
  end

  module IdM : module type of Applicatic (Applicative.OfMonad (Monad.Identity))

  val map : ('n, 'b, 'c) IdM.mapperM -> ('left, 'n, 'b, 'right) t -> ('left, 'n, 'c, 'right) t

  module Traverse : functor (Acc : Util.Signatures.Fam) -> sig
    type ('n, 'b, 'c) left_folder = {
      foldmap :
        'left 'right 'm.
        ('m, 'n) sface ->
        'left Acc.t ->
        ('left, 'm, 'b, 'right) F.t ->
        ('left, 'm, 'c, 'right) F.t * 'right Acc.t;
    }

    val fold_map_left :
      ('n, 'b, 'c) left_folder ->
      'left Acc.t ->
      ('left, 'n, 'b, 'right) t ->
      ('left, 'n, 'c, 'right) t * 'right Acc.t

    type ('n, 'b, 'c) right_folder = {
      foldmap :
        'left 'right 'm.
        ('m, 'n) sface ->
        ('left, 'm, 'b, 'right) F.t ->
        'right Acc.t ->
        'left Acc.t * ('left, 'm, 'c, 'right) F.t;
    }

    val fold_map_right :
      ('n, 'b, 'c) right_folder ->
      ('left, 'n, 'b, 'right) t ->
      'right Acc.t ->
      'left Acc.t * ('left, 'n, 'c, 'right) t

    type (_, _, _) fwrap_left =
      | Fwrap : ('left, 'm, 'b, 'right) F.t * 'right Acc.t -> ('left, 'm, 'b) fwrap_left

    type (_, _, _, _) gwrap_left =
      | Wrap : ('left, 'm, 'mk, 'b, 'right) gt * 'right Acc.t -> ('left, 'm, 'mk, 'b) gwrap_left

    type ('left, 'm, 'b) wrap_left = ('left, 'm, 'm, 'b) gwrap_left

    type ('n, 'b) builder_leftM = {
      build : 'left 'm. ('m, 'n) sface -> 'left Acc.t -> ('left, 'm, 'b) fwrap_left;
    }

    val build_left : 'n D.t -> ('n, 'b) builder_leftM -> 'left Acc.t -> ('left, 'n, 'b) wrap_left

    type (_, _, _) fwrap_right =
      | Fwrap : 'left Acc.t * ('left, 'm, 'b, 'right) F.t -> ('m, 'b, 'right) fwrap_right

    type (_, _, _, _) gwrap_right =
      | Wrap : 'left Acc.t * ('left, 'm, 'mk, 'b, 'right) gt -> ('m, 'mk, 'b, 'right) gwrap_right

    type ('m, 'b, 'right) wrap_right = ('m, 'm, 'b, 'right) gwrap_right

    type ('n, 'b) builder_rightM = {
      build : 'right 'm. ('m, 'n) sface -> 'right Acc.t -> ('m, 'b, 'right) fwrap_right;
    }

    val build_right :
      'n D.t -> ('n, 'b) builder_rightM -> 'right Acc.t -> ('n, 'b, 'right) wrap_right
  end

  type (_, _) fbiwrap = Fbiwrap : ('left, 'n, 'b, 'right) F.t -> ('n, 'b) fbiwrap

  val find : ('left, 'n, 'b, 'right) t -> ('k, 'n) sface -> ('k, 'b) fbiwrap
  val find_top : ('left, 'n, 'b, 'right) t -> ('n, 'b) fbiwrap
end

module NFamOf : sig
  type (_, _, _, _) t = NFamOf : 'b -> ('left, 'n, 'b, 'left N.suc) t
end

module NICubeOf : sig
  include module type of Icube (NFamOf)

  val singleton : 'b -> ('left, D.zero, 'b, 'left N.suc) t
  val out : 'left N.t -> ('left, 'm, 'b, 'right) t -> 'right N.t
  val find : ('left, 'n, 'b, 'right) t -> ('k, 'n) sface -> 'b
  val find_top : ('left, 'n, 'b, 'right) t -> 'b
end

type (_, _) face = Face : ('m, 'n) sface * ('k, 'm) perm -> ('k, 'n) face

val id_face : 'n D.t -> ('n, 'n) face
val perm_sface : ('n, 'k) perm -> ('m, 'n) sface -> ('m, 'k) face
val comp_face : ('n, 'k) face -> ('m, 'n) face -> ('m, 'k) face
val dom_face : ('m, 'n) face -> 'm D.t
val cod_face : ('m, 'n) face -> 'n D.t
val face_of_sface : ('m, 'n) sface -> ('m, 'n) face
val face_of_perm : ('m, 'n) perm -> ('m, 'n) face

type _ face_of = Face_of : ('m, 'n) face -> 'n face_of
type (_, _) op = Op : ('n, 'k) sface * ('m, 'n) deg -> ('m, 'k) op

val id_op : 'n D.t -> ('n, 'n) op
val deg_sface : ('n, 'k) deg -> ('m, 'n) sface -> ('m, 'k) op
val comp_op : ('n, 'k) op -> ('m, 'n) op -> ('m, 'k) op
val dom_op : ('m, 'n) op -> 'm D.t
val cod_op : ('m, 'n) op -> 'n D.t
val is_id_op : ('m, 'n) op -> ('m, 'n) Eq.t option
val op_of_deg : ('m, 'n) deg -> ('m, 'n) op
val op_of_sface : ('m, 'n) sface -> ('m, 'n) op

val op_plus_op :
  ('k, 'm) op -> ('m, 'n, 'mn) D.plus -> ('k, 'l, 'kl) D.plus -> ('l, 'n) op -> ('kl, 'mn) op

val plus_op : 'm D.t -> ('m, 'n, 'mn) D.plus -> ('m, 'l, 'ml) D.plus -> ('l, 'n) op -> ('ml, 'mn) op
val op_plus : ('k, 'm) op -> ('m, 'n, 'mn) D.plus -> ('k, 'n, 'kn) D.plus -> ('kn, 'mn) op

type _ op_of = Of : ('m, 'n) op -> 'n op_of
type _ op_of_plus = Of : ('m, 'n) sface * 'm deg_of_plus -> 'n op_of_plus

val comp_op_of : ('m, 'n) op -> 'm op_of -> 'n op_of
val comp_op_deg_of_plus : ('m, 'n) op -> 'm deg_of_plus -> 'n op_of_plus

type (_, _, _) insertion

val ins_zero : 'a D.t -> ('a, 'a, D.zero) insertion
val zero_ins : 'a D.t -> ('a, D.zero, 'a) insertion
val id_ins : 'a D.t -> ('a, 'b, 'ab) D.plus -> ('ab, 'a, 'b) insertion
val dom_ins : ('a, 'b, 'c) insertion -> 'a D.t
val cod_left_ins : ('a, 'b, 'c) insertion -> 'b D.t
val cod_right_ins : ('a, 'b, 'c) insertion -> 'c D.t
val equal_ins : ('a1, 'b1, 'c1) insertion -> ('a2, 'b2, 'c2) insertion -> unit option

val plus_ins :
  'a D.t ->
  ('a, 'b, 'ab) D.plus ->
  ('a, 'c, 'ac) D.plus ->
  ('b, 'c, 'd) insertion ->
  ('ab, 'ac, 'd) insertion

val deg_of_ins_plus : ('a, 'b, 'c) insertion -> ('b, 'c, 'bc) D.plus -> ('a, 'bc) deg
val deg_of_ins : ('a, 'b, 'c) insertion -> 'a deg_to
val perm_of_ins_plus : ('a, 'b, 'c) insertion -> ('b, 'c, 'bc) D.plus -> ('a, 'bc) perm
val perm_of_ins : ('a, 'b, 'c) insertion -> 'a perm_to
val is_id_ins : ('a, 'b, 'c) insertion -> ('b, 'c, 'a) D.plus option
val deg_of_plus_of_ins : ('a, 'b, 'c) insertion -> 'b deg_of_plus

type (_, _, _) insfact = Insfact : ('a, 'b) deg * ('ac, 'a, 'c) insertion -> ('ac, 'b, 'c) insfact

val insfact : ('ac, 'bc) deg -> ('b, 'c, 'bc) D.plus -> ('ac, 'b, 'c) insfact

type (_, _, _) insfact_comp =
  | Insfact_comp :
      ('m, 'n) deg * ('ml, 'm, 'l) insertion * ('k, 'j, 'l) D.plus * ('a, 'i, 'ml) D.plus
      -> ('n, 'k, 'a) insfact_comp

val insfact_comp : ('nk, 'n, 'k) insertion -> ('a, 'b) deg -> ('n, 'k, 'a) insfact_comp

type (_, _, _) deg_lift_ins =
  | Deg_lift_ins : ('mk, 'm, 'k) insertion * ('mk, 'nk) deg -> ('m, 'k, 'nk) deg_lift_ins

val deg_lift_ins : ('m, 'n) deg -> ('nk, 'n, 'k) insertion -> ('m, 'k, 'nk) deg_lift_ins

type (_, _, _) sface_lift_ins =
  | Sface_lift_ins : ('mk, 'm, 'k) insertion * ('mk, 'nk) sface -> ('m, 'k, 'nk) sface_lift_ins

val sface_lift_ins : ('m, 'n) sface -> ('nk, 'n, 'k) insertion -> ('m, 'k, 'nk) sface_lift_ins

type (_, _, _) pface_lift_ins =
  | Pface_lift_ins : ('mk, 'm, 'k) insertion * ('mk, 'nk) pface -> ('m, 'k, 'nk) pface_lift_ins

val pface_lift_ins : ('m, 'n) pface -> ('nk, 'n, 'k) insertion -> ('m, 'k, 'nk) pface_lift_ins

type _ ins_of = Ins_of : ('ab, 'a, 'b) insertion -> 'ab ins_of

val ins_of_ints : 'ab D.t -> int Bwd.t -> 'ab ins_of option
val ints_of_ins : ('ab, 'a, 'b) insertion -> int Bwd.t
val string_of_ins_ints : int Bwd.t -> string
val string_of_ins : ('ab, 'a, 'b) insertion -> string

type any_ins = Any_ins : ('a, 'b, 'c) insertion -> any_ins

val all_ins_of : 'ab D.t -> 'ab ins_of Seq.t

type (_, _, _) shuffle

val plus_of_shuffle : ('a, 'b, 'c) shuffle -> ('a, 'b, 'c) D.plus
val deg_of_shuffle : ('a, 'b, 'c) shuffle -> ('a, 'b, 'ab) D.plus -> ('c, 'ab) deg
val perm_of_shuffle : ('a, 'b, 'c) shuffle -> ('a, 'b, 'ab) D.plus -> ('c, 'ab) perm
val left_shuffle : ('a, 'b, 'c) shuffle -> 'a D.t
val right_shuffle : ('a, 'b, 'c) shuffle -> 'b D.t
val out_shuffle : ('a, 'b, 'c) shuffle -> 'c D.t
val shuffle_zero : 'a D.t -> ('a, D.zero, 'a) shuffle

type (_, _) shuffle_right = Of_right : ('a, 'b, 'c) shuffle -> ('b, 'c) shuffle_right

val all_shuffles_right : 'b D.t -> 'c D.t -> ('b, 'c) shuffle_right Seq.t

type (_, _) pbij

val dom_pbij : ('e, 'i) pbij -> 'e D.t
val cod_pbij : ('e, 'i) pbij -> 'i D.t
val pbij_of_ins : ('a, 'b, 'c) insertion -> ('a, 'c) pbij

type _ pbij_of = Pbij_of : ('evaluation, 'intrinsic) pbij -> 'evaluation pbij_of

val pbij_of_strings : 'e D.t -> string Bwd.t -> 'e pbij_of option
val strings_of_pbij : ('n, 'i) pbij -> string Bwd.t
val string_of_pbij : ('n, 'i) pbij -> string
val all_pbij_between : 'evaluation D.t -> 'intrinsic D.t -> ('evaluation, 'intrinsic) pbij Seq.t

type (_, _) deg_comp_pbij =
  | Deg_comp_pbij :
      ('evaluation, 'intrinsic) pbij * ('old_result, 'result) deg
      -> ('evaluation, 'intrinsic) deg_comp_pbij

val deg_comp_pbij : ('m, 'n) deg -> ('m, 'i) pbij -> ('n, 'i) deg_comp_pbij

module Pbijmap : sig
  type (_, _, _) t

  val intrinsic : ('evaluation, 'intrinsic, 'v) t -> 'intrinsic D.t

  type (_, _) wrapped = Wrap : ('evaluation, 'intrinsic, 'v) t -> ('evaluation, 'v) wrapped

  val find : ('evaluation, 'intrinsic) pbij -> ('evaluation, 'intrinsic, 'v) t -> 'v
  val find_singleton : ('evaluation, 'intrinsic, 'v) t -> 'v option

  val set :
    ('evaluation, 'intrinsic) pbij ->
    'v ->
    ('evaluation, 'intrinsic, 'v) t ->
    ('evaluation, 'intrinsic, 'v) t

  val build :
    'evaluation D.t ->
    'intrinsic D.t ->
    (('evaluation, 'intrinsic) pbij -> 'v) ->
    ('evaluation, 'intrinsic, 'v) t

  val singleton : 'v -> ('evaluation, D.zero, 'v) t
  val map : ('v -> 'w) -> ('evaluation, 'intrinsic, 'v) t -> ('evaluation, 'intrinsic, 'w) t

  val iter :
    'evaluation D.t ->
    (('evaluation, 'intrinsic) pbij -> 'v -> unit) ->
    ('evaluation, 'intrinsic, 'v) t ->
    unit

  val fold :
    'evaluation D.t ->
    (('evaluation, 'intrinsic) pbij -> 'v -> 'acc -> 'acc) ->
    ('evaluation, 'intrinsic, 'v) t ->
    'acc ->
    'acc
end

module Plusmap : sig
  module OfDom : module type of Tbwd.Of (D)
  module OfCod : module type of Tbwd.Of (D) with type 'a t = 'a OfDom.t

  type ('a, 'b, 'c) t =
    | Map_emp : ('p, emp, emp) t
    | Map_snoc : ('p, 'xs, 'ys) t * ('p, 'x, 'y) D.plus -> ('p, ('xs, 'x) snoc, ('ys, 'y) snoc) t

  type ('a, 'b) exists = Exists : 'ys OfCod.t * ('p, 'xs, 'ys) t -> ('p, 'xs) exists

  val exists : 'p D.t -> 'xs OfDom.t -> ('p, 'xs) exists
  val out : 'p D.t -> 'xs OfDom.t -> ('p, 'xs, 'ys) t -> 'ys OfCod.t
  val uniq : ('p, 'xs, 'ys) t -> ('p, 'xs, 'zs) t -> ('ys, 'zs) Eq.t

  type (_, _, _, _) map_insert =
    | Map_insert : ('zs, 'fx, 'ws) Tbwd.insert * ('p, 'ys, 'ws) t -> ('p, 'fx, 'ys, 'zs) map_insert

  val insert :
    ('p, 'x, 'z) D.plus ->
    ('xs, 'x, 'ys) Tbwd.insert ->
    ('p, 'xs, 'zs) t ->
    ('p, 'z, 'ys, 'zs) map_insert

  type (_, _, _, _) unmap_insert =
    | Unmap_insert :
        ('p, 'x, 'z) D.plus * ('xs, 'x, 'ys) Tbwd.insert * ('p, 'xs, 'zs) t
        -> ('p, 'z, 'ys, 'zs) unmap_insert

  val unmap_insert :
    ('zs, 'z, 'ws) Tbwd.insert -> ('p, 'ys, 'ws) t -> ('p, 'z, 'ys, 'zs) unmap_insert

  type (_, _, _) map_permute =
    | Map_permute : ('p, 'zs, 'ws) t * ('ys, 'ws) Tbwd.permute -> ('p, 'zs, 'ys) map_permute

  val permute : ('p, 'xs, 'ys) t -> ('xs, 'zs) Tbwd.permute -> ('p, 'zs, 'ys) map_permute

  val assocl :
    ('a, 'b, 'ab) D.plus -> ('b, 'cs, 'bcs) t -> ('a, 'bcs, 'abcs) t -> ('ab, 'cs, 'abcs) t

  val zerol : 'bs OfDom.t -> (D.zero, 'bs, 'bs) t
  end

(*  *)
type one

val one : one D.t

type _ is_suc = Is_suc : 'n D.t * ('n, one, 'm) D.plus -> 'm is_suc

val suc_pos : 'n D.pos -> 'n is_suc
val deg_of_name : string -> any_deg option
val name_of_deg : ('a, 'b) deg -> string option

(*  *)
val locking : ('a, 'b) deg -> bool
