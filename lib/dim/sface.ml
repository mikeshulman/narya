open Util

(* ********** Strict faces ********** *)

(* A strict face is an order-preserving partial map that is surjective and with an endpoint index assigned to each element not mapping to the codomain. *)

type (_, _) sface =
  | Zero : (D.zero, D.zero) sface
  | End : ('m, 'n) sface * Endpoints.t -> ('m, 'n D.suc) sface
  | Mid : ('m, 'n) sface -> ('m D.suc, 'n D.suc) sface

let rec id_sface : type n. n D.t -> (n, n) sface = function
  | Nat Zero -> Zero
  | Nat (Suc n) -> Mid (id_sface (Nat n))

let rec dom_sface : type m n. (m, n) sface -> m D.t = function
  | Zero -> Nat Zero
  | End (f, _) ->
      let (Nat s) = dom_sface f in
      Nat s
  | Mid f ->
      let (Nat s) = dom_sface f in
      Nat (Suc s)

let rec cod_sface : type m n. (m, n) sface -> n D.t = function
  | Zero -> Nat Zero
  | End (f, _) ->
      let (Nat s) = cod_sface f in
      Nat (Suc s)
  | Mid f ->
      let (Nat s) = cod_sface f in
      Nat (Suc s)

let rec is_id_sface : type m n. (m, n) sface -> unit option = function
  | Zero -> Some ()
  | End _ -> None
  | Mid f -> is_id_sface f

let rec comp_sface : type m n k. (n, k) sface -> (m, n) sface -> (m, k) sface =
 fun a b ->
  match (a, b) with
  | Zero, Zero -> Zero
  | End (a', e), _ -> End (comp_sface a' b, e)
  | Mid a', End (b', e) -> End (comp_sface a' b', e)
  | Mid a', Mid b' -> Mid (comp_sface a' b')

(* Zero has only the trivial strict face *)
let sface_zero : type n. (n, D.zero) sface -> (n, D.zero) Monoid.eq = function
  | Zero -> Eq

(* Concatenate two strict faces left-to-right. *)
let rec sface_plus_sface :
    type m n mn k p kp.
    (k, m) sface -> (m, n, mn) D.plus -> (k, p, kp) D.plus -> (p, n) sface -> (kp, mn) sface =
 fun fkm mn kp fpn ->
  match (fpn, mn, kp) with
  | Zero, Zero, Zero -> fkm
  | End (fpn, e), Suc mn, kp -> End (sface_plus_sface fkm mn kp fpn, e)
  | Mid fpn, Suc mn, Suc kp -> Mid (sface_plus_sface fkm mn kp fpn)

(* In particular, we can extend by identities on the right or left. *)

type _ sface_of = SFace_of : ('m, 'n) sface -> 'n sface_of

let sface_plus :
    type m n mn k kn. (k, m) sface -> (m, n, mn) D.plus -> (k, n, kn) D.plus -> (kn, mn) sface =
 fun f mn kn -> sface_plus_sface f mn kn (id_sface (Nat mn))

let plus_sface :
    type m n nm k nk.
    n D.t -> (n, m, nm) D.plus -> (n, k, nk) D.plus -> (k, m) sface -> (nk, nm) sface =
 fun n nm nk f -> sface_plus_sface (id_sface n) nm nk f

(* Conversely, any strict face of a sum decomposes as a sum. *)

type (_, _, _) sface_of_plus =
  | SFace_of_plus :
      ('m, 'l, 'ml) D.plus * ('m, 'n) sface * ('l, 'k) sface
      -> ('ml, 'n, 'k) sface_of_plus

let rec sface_of_plus :
    type ml n k nk. (n, k, nk) D.plus -> (ml, nk) sface -> (ml, n, k) sface_of_plus =
 fun nk f ->
  match nk with
  | Zero -> SFace_of_plus (D.Zero, f, Zero)
  | Suc nk -> (
      match f with
      | End (f, e) ->
          let (SFace_of_plus (ml, f1, f2)) = sface_of_plus nk f in
          SFace_of_plus (ml, f1, End (f2, e))
      | Mid f ->
          let (SFace_of_plus (ml, f1, f2)) = sface_of_plus nk f in
          SFace_of_plus (Suc ml, f1, Mid f2))

(* The strict faces of any dimension can be enumerated.  For efficiency, this could be memoized. *)

type ('n, 'f) count_faces = (Endpoints.len D.suc, 'n, 'f) D.pow
type _ has_faces = Faces : ('n, 'f) count_faces -> 'n has_faces

let count_faces : type n. n D.t -> n has_faces =
 fun n ->
  let (Has_pow f) = D.pow (D.suc Endpoints.len) n in
  Faces f

let faces_zero : (D.zero, N.one) count_faces = Zero
let dim_faces : type n f. (n, f) count_faces -> n D.t = fun c -> D.pow_right c
let faces_pos : type n f. (n, f) count_faces -> f N.pos = fun c -> D.pow_pos (Pos Endpoints.len) c
let faces_out : type n f. (n, f) count_faces -> f N.t = fun c -> D.pow_out c

let faces_uniq : type n f1 f2. (n, f1) count_faces -> (n, f2) count_faces -> (f1, f2) Monoid.eq =
 fun f1 f2 -> N.pow_uniq f1 f2

let rec sfaces : type n f. (n, f) count_faces -> (n sface_of, f) Bwv.t = function
  | Zero -> Snoc (Emp, SFace_of Zero)
  | Suc (mn, mnm) ->
      let fmn = sfaces mn in
      Bwv.bind mnm
        (Snoc
           ( Bwv.map (fun e (SFace_of f) -> SFace_of (End (f, e))) Endpoints.indices,
             fun (SFace_of f) -> SFace_of (Mid f) ))
        (fun g -> Bwv.map g fmn)

(* This is very inefficient!  But at least it is correct. *)
(* let sface_int : type n f. (n, f) count_faces -> n sface_of -> int = *)
(*  fun nf f -> N.to_int (faces_out nf) - N.int_index (Option.get (Bwv.index f (sfaces nf))) - 1 *)

type _ dbl_sfaces_of =
  | DblOf : ('m, 'f) count_faces * ('m sface_of, 'f) Bwv.t * ('m, 'n) sface -> 'n dbl_sfaces_of

let dbl_sfaces : type n f. (n, f) count_faces -> (n dbl_sfaces_of, f) Bwv.t =
 fun nf ->
  Bwv.map
    (fun (SFace_of f) ->
      let (Faces mf) = count_faces (dom_sface f) in
      DblOf (mf, sfaces mf, f))
    (sfaces nf)

(* The strict faces of a sum of dimensions are the pairs of strict faces of the summands.  We implement this as an assembly function on backwards vectors, so that its interface doesn't depend on the ordering. *)

let sfaces_plus :
    type m n mn fm fn fmn a b c.
    (m, n, mn) D.plus ->
    (m, fm) count_faces ->
    (n, fn) count_faces ->
    (mn, fmn) count_faces ->
    (a -> b -> c) ->
    (a, fm) Bwv.t ->
    (b, fn) Bwv.t ->
    (c, fmn) Bwv.t =
 fun mn fm fn fmn g xs ys ->
  let fm_times_fn = N.pow_plus (D.suc Endpoints.len) fm fn mn fmn in
  (* However, its implementation for this dimension theory does depend on the ternary ordering of strict faces of cubes. *)
  Bwv.bind fm_times_fn ys (fun y -> Bwv.map (fun x -> g x y) xs)

type (_, _) d_le = Le : ('m, 'n, 'mn) D.plus -> ('m, 'mn) d_le

let rec plus_of_sface : type m mn. (m, mn) sface -> (m, mn) d_le = function
  | Zero -> Le Zero
  | End (d, _) ->
      let (Le mn) = plus_of_sface d in
      Le (Suc mn)
  | Mid d ->
      let (Le mn) = plus_of_sface d in
      Le (N.suc_plus_eq_suc mn)

type any_sface = Any_sface : ('n, 'k) sface -> any_sface

let rec string_of_sface : type n k. (n, k) sface -> string = function
  | Zero -> ""
  | End (fa, e) -> Endpoints.to_string (Some e) ^ string_of_sface fa
  | Mid fa -> Endpoints.to_string None ^ string_of_sface fa

let sface_of_string : string -> any_sface option =
 fun str ->
  String.fold_right
    (fun x fa ->
      match (fa, Endpoints.of_char x) with
      | None, _ | _, Error _ -> None
      | Some (Any_sface fa), Ok (Some e) -> Some (Any_sface (End (fa, e)))
      | Some (Any_sface fa), Ok None -> Some (Any_sface (Mid fa)))
    str (Some (Any_sface Zero))
