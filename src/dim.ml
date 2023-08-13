(* ********** Endpoints ********** *)

(* We parametrize over an abstract module specifying how many endpoints our cubes have. *)

module Endpoints = struct
  type len = N.two
  type t = len N.index

  let len : len N.t = N.two
  let indices : (t, len) Bwv.t = Snoc (Snoc (Emp, Pop Top), Top)
end

(* ********** Dimensions ********** *)

(* In this file we define "dimensions" to be type-level natural numbers.  However, in the interface we expose only that they are a type-level monoid with some extra structure.  Thus, the implementation is parametric over a specification of dimensions and their operators.  In addition, this file itself is parametric over Endpoints, which abstractly specifies a finite number of endpoints for each dimension. *)

module D = N

(* We consider the addition in D to represent composition in the delooping of the dimension category, in diagrammatic order. *)

let compare : type m n. m D.t -> n D.t -> (m, n) Monoid.compare =
 fun m n ->
  match N.compare m n with
  | Eq -> Eq
  | _ -> Neq

(* Since dimensions are epimorphisms, given n and nk there is at most one k such that (n,k,nk) D.plus.  This function finds it if it exists. *)

type (_, _) factor = Factor : ('n, 'k, 'nk) D.plus -> ('nk, 'n) factor

let rec factor : type nk n. nk D.t -> n D.t -> (nk, n) factor option =
 fun nk n ->
  let open Monad.Ops (Monad.Maybe) in
  match compare nk n with
  | Eq -> Some (Factor Zero)
  | Neq -> (
      match nk with
      | Nat Zero -> None
      | Nat (Suc nk) ->
          let* (Factor n_k) = factor (Nat nk) n in
          return (Factor (Suc n_k)))

(* And we prove that it is unique. *)
let rec zero_uniq : type m z. m D.t -> (m, z, m) D.plus -> (z, D.zero) Monoid.eq =
 fun m mz ->
  match m with
  | Nat Zero ->
      let Zero = mz in
      Eq
  | Nat (Suc m) ->
      let (Suc mz) = D.suc_plus mz in
      let Eq = zero_uniq (Nat m) mz in
      Eq

let rec epi : type m n k l. k D.t -> (k, m, l) D.plus -> (k, n, l) D.plus -> (m, n) Monoid.eq =
 fun k km kn ->
  match (km, kn) with
  | Zero, _ ->
      let Eq = zero_uniq k kn in
      Eq
  | _, Zero ->
      let Eq = zero_uniq k km in
      Eq
  | Suc km, Suc kn ->
      let Eq = epi k km kn in
      Eq

(* Compute the pushout of a span of dimensions, if it exists.  In practice we only need pushouts of spans that can be completed to some commutative square (equivalently, pushouts in slice categories), but in our primary examples all pushouts exist, so we don't bother putting an option on it yet. *)

type (_, _) pushout = Pushout : ('a, 'c, 'p) D.plus * ('b, 'd, 'p) D.plus -> ('a, 'b) pushout

let pushout : type a b. a D.t -> b D.t -> (a, b) pushout =
 fun a b ->
  match D.compare a b with
  | Eq -> Pushout (Zero, Zero)
  | Lt ab -> Pushout (ab, Zero)
  | Gt ba -> Pushout (Zero, ba)

(* ********** Operators ********** *)

(* If m and n are dimensions, (m,n) op is the type of dimensional operators m => n, which act on types and terms contravariantly.  We define these in an intrinsically correct way, using a strict factorization system consisting of degeneracies and strict faces.  *)

(* ********** Degeneracies ********** *)

(* Degeneracies are defined inductively by insertion: a degeneracy of 0 is given by adding any dimension, and a degeneracy of n+1 is one of length n together with a location at which to insert the n+1st (rightmost) element. *)

type (_, _) deg =
  | Zero : 'a D.t -> ('a, D.zero) deg
  | Suc : ('a, 'b) deg * 'a D.suc D.index -> ('a D.suc, 'b D.suc) deg

let rec dom_deg : type m n. (m, n) deg -> m D.t = function
  | Zero a -> a
  | Suc (s, _) -> D.suc (dom_deg s)

let rec cod_deg : type m n. (m, n) deg -> n D.t = function
  | Zero _ -> D.zero
  | Suc (s, _) -> D.suc (cod_deg s)

let rec id_deg : type n. n D.t -> (n, n) deg = function
  | Nat Zero -> Zero D.zero
  | Nat (Suc n) -> Suc (id_deg (Nat n), Top)

(* By "residual" of a degeneracy, given an element of its codomain, we mean the image of that element together with the degeneracy obtained by removing that element from the domain and its image from the codomain. *)

type (_, _) deg_residual =
  | Residual : ('m, 'n) deg * 'm D.suc D.index -> ('m D.suc, 'n D.suc) deg_residual

let rec deg_residual : type m n. (m, n) deg -> n D.index -> (m, n) deg_residual =
 fun s k ->
  match (k, s) with
  | Top, Suc (s, i) -> Residual (s, i)
  | Pop k, Suc (s, i) ->
      let (Residual (s, j)) = deg_residual s k in
      let i, j = N.swap_indices i j in
      Residual (Suc (s, j), i)

(* Using residuals, we can compose degeneracies. *)
let rec comp_deg : type a b c. (b, c) deg -> (a, b) deg -> (a, c) deg =
 fun a b ->
  match a with
  | Zero _ -> Zero (dom_deg b)
  | Suc (s, k) ->
      let (Residual (t, i)) = deg_residual b k in
      Suc (comp_deg s t, i)

(* Extend a degeneracy by the identity on the right. *)
let rec deg_plus :
    type m n k mk nk. (m, n) deg -> (n, k, nk) D.plus -> (m, k, mk) D.plus -> (mk, nk) deg =
 fun s nk mk ->
  match (nk, mk) with
  | Zero, Zero -> s
  | Suc nk, Suc mk -> Suc (deg_plus s nk mk, Top)

(* Extend the domain of a codegeneracy by a number of degenerate points, leaving the codomain fixed. *)
let rec deg_plus_dom : type m n k mk. (m, n) deg -> (m, k, mk) D.plus -> (mk, n) deg =
 fun s mk ->
  match s with
  | Zero m -> Zero (D.plus_out m mk)
  | Suc (s, i) ->
      let (Suc mk') = D.suc_plus mk in
      Suc (deg_plus_dom s mk', D.index_plus i mk)

(* Add together two degeneracies. *)
let rec deg_plus_deg :
    type m n mn k l kl.
    (k, m) deg -> (m, n, mn) D.plus -> (k, l, kl) D.plus -> (l, n) deg -> (kl, mn) deg =
 fun skm mn kl sln ->
  match (mn, sln) with
  | Zero, Zero _ -> deg_plus_dom skm kl
  | Suc mn', Suc (sln', i) ->
      let (Suc kl') = kl in
      Suc (deg_plus_deg skm mn' kl' sln', D.plus_index kl i)

(* Extend a degeneracy by the identity on the left. *)
let plus_deg :
    type m n mn l ml. m D.t -> (m, n, mn) D.plus -> (m, l, ml) D.plus -> (l, n) deg -> (ml, mn) deg
    =
 fun m mn ml s -> deg_plus_deg (id_deg m) mn ml s

(* Check whether a degeneracy is an identity *)
let rec is_id_deg : type m n. (m, n) deg -> unit option = function
  | Zero _ -> Some ()
  | Suc (p, Top) -> is_id_deg p
  | Suc (_, Pop _) -> None

(* A degeneracy of a positive dimension is still positive *)
let pos_deg : type m n. n D.pos -> (m, n) deg -> m D.pos =
 fun n s ->
  match (n, s) with
  | Pos _, Suc (s, _) -> Pos (dom_deg s)

(* We consider two degeneracies "equivalent" if they differ by an identity extension on the right (i.e. post-whiskering with an identity). *)
let rec deg_equiv : type m n k l. (m, n) deg -> (k, l) deg -> unit option =
 fun s1 s2 ->
  let open Monad.Ops (Monad.Maybe) in
  match (s1, s2) with
  | Zero _, Zero _ -> Some ()
  | Suc (p1, i1), Suc (p2, i2) ->
      let* () = N.index_equiv i1 i2 in
      deg_equiv p1 p2
  | Zero _, _ -> is_id_deg s2
  | _, Zero _ -> is_id_deg s1

(* ********** Permutations ********** *)

(* A permutation is just an endo-degeneracy.  *)
type 'n perm = ('n, 'n) deg

(* All the operations on degeneracies specialize immediately to permutations. *)

let dim_perm : type n. n perm -> n D.t = fun p -> dom_deg p
let id_perm : type n. n D.t -> n perm = fun n -> id_deg n
let comp_perm : type a. a perm -> a perm -> a perm = fun a b -> comp_deg a b
let perm_plus : type m k mk. m perm -> (m, k, mk) D.plus -> mk perm = fun s mk -> deg_plus s mk mk

let perm_plus_perm : type m n mn. m perm -> (m, n, mn) D.plus -> n perm -> mn perm =
 fun s mn t -> deg_plus_deg s mn mn t

let plus_perm : type m n mn. m D.t -> (m, n, mn) D.plus -> n perm -> mn perm =
 fun m mn s -> plus_deg m mn mn s

let is_id_perm : type n. n perm -> unit option = fun p -> is_id_deg p
let perm_equiv : type m n. m perm -> n perm -> unit option = fun s t -> deg_equiv s t

(* The permutation that switches m and n side by side. *)
let rec switch_perm : type m n mn. m D.t -> (m, n, mn) D.plus -> mn perm =
 fun m -> function
  | Zero -> id_perm m
  | Suc mn -> Suc (switch_perm m mn, D.switch_index m (Suc mn))

(* The inverse of a permutation *)

let rec coinsert : type m. m perm -> m D.suc D.index -> m D.suc perm =
 fun p -> function
  | Top -> Suc (p, Top)
  | Pop i -> (
      match p with
      | Zero _ -> (
          match i with
          | _ -> .)
      | Suc (p, j) -> Suc (coinsert p i, Pop j))

let rec perm_inv : type m. m perm -> m perm = function
  | Zero z -> Zero z
  | Suc (p, i) -> coinsert (perm_inv p) i

(* ********** Variable degeneracies ********** *)

type _ deg_of = Of : ('m, 'n) deg -> 'n deg_of
type _ deg_of_plus = Of : ('n, 'k, 'nk) D.plus * ('m, 'nk) deg -> 'n deg_of_plus

let comp_deg_of_plus : type m n. (m, n) deg -> m deg_of_plus -> n deg_of_plus =
 fun s2 (Of (mk, s1)) ->
  let (Plus nk) = D.plus (Nat mk) in
  let s2k = deg_plus s2 nk mk in
  Of (nk, comp_deg s2k s1)

let rec reduce_deg_of_plus : type n. n deg_of_plus -> n deg_of_plus =
 fun s ->
  match s with
  | Of (Zero, _) -> s
  | Of (Suc nk, Suc (s', Top)) -> reduce_deg_of_plus (Of (nk, s'))
  | Of (Suc _, Suc (_, Pop _)) -> s

type (_, _) deg_extending =
  | DegExt : ('k, 'j, 'kj) D.plus * ('n, 'i, 'ni) D.plus * ('kj, 'ni) deg -> ('k, 'n) deg_extending

let comp_deg_extending : type m n l k. (m, n) deg -> (k, l) deg -> (k, n) deg_extending =
 fun a b ->
  (* let k = dom_deg b in *)
  let l = cod_deg b in
  let m = dom_deg a in
  (* let n = cod_deg a in *)
  let (Pushout (mi, lj)) = pushout m l in
  let (Plus kj) = D.plus (Nat lj) in
  let (Plus ni) = D.plus (Nat mi) in
  DegExt (kj, ni, comp_deg (deg_plus a ni mi) (deg_plus b lj kj))

type any_deg = Any : ('m, 'n) deg -> any_deg

let comp_deg_any : type m n. (m, n) deg -> any_deg -> n deg_of_plus =
 fun a (Any b) ->
  (* let k = dom_deg b in *)
  let l = cod_deg b in
  let m = dom_deg a in
  (* let n = cod_deg a in *)
  let (Pushout (mi, lj)) = pushout m l in
  let (Plus kj) = D.plus (Nat lj) in
  let (Plus ni) = D.plus (Nat mi) in
  Of (ni, comp_deg (deg_plus a ni mi) (deg_plus b lj kj))

let comp_deg_of_plus_any : type n. n deg_of_plus -> any_deg -> n deg_of_plus =
 fun (Of (nk, a)) b ->
  let (Of (nk_l, s)) = comp_deg_any a b in
  let (Plus kl) = D.plus (D.plus_right nk_l) in
  let n_kl = D.plus_assocr nk kl nk_l in
  Of (n_kl, s)

let any_deg_plus : type k. any_deg -> k D.t -> any_deg =
 fun (Any deg) k ->
  let (Plus mk) = D.plus k in
  let (Plus nk) = D.plus k in
  Any (deg_plus deg mk nk)

let any_of_deg_of_plus : type n. n deg_of_plus -> any_deg = function
  | Of (_, s) -> Any s

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
 fun fkn mn kp fpn ->
  match (fpn, mn, kp) with
  | Zero, Zero, Zero -> fkn
  | End (fpn, e), Suc mn, kp -> End (sface_plus_sface fkn mn kp fpn, e)
  | Mid fpn, Suc mn, Suc kp -> Mid (sface_plus_sface fkn mn kp fpn)

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
      Le (N.suc_plus' mn)

(* ********** Backwards faces ********** *)

type (_, _) bwsface =
  | Zero : (D.zero, D.zero) bwsface
  | End : Endpoints.t * ('m, 'n) bwsface -> ('m, 'n D.suc) bwsface
  | Mid : ('m, 'n) bwsface -> ('m D.suc, 'n D.suc) bwsface

let rec dom_bwsface : type m n. (m, n) bwsface -> m D.t = function
  | Zero -> Nat Zero
  | End (_, f) ->
      let (Nat s) = dom_bwsface f in
      Nat s
  | Mid f ->
      let (Nat s) = dom_bwsface f in
      Nat (Suc s)

let rec cod_bwsface : type m n. (m, n) bwsface -> n D.t = function
  | Zero -> Nat Zero
  | End (_, f) ->
      let (Nat s) = cod_bwsface f in
      Nat (Suc s)
  | Mid f ->
      let (Nat s) = cod_bwsface f in
      Nat (Suc s)

let sface_of_bw : type m n. (m, n) bwsface -> (m, n) sface =
 fun bf ->
  let rec sface_of_bw_onto :
      type k l m n km ln.
      (k, m, km) D.plus -> (l, n, ln) D.plus -> (k, l) sface -> (m, n) bwsface -> (km, ln) sface =
   fun km ln f bf ->
    match bf with
    | Zero ->
        let Zero, Zero = (km, ln) in
        f
    | End (e, bf) -> sface_of_bw_onto km (D.suc_plus'' ln) (End (f, e)) bf
    | Mid bf -> sface_of_bw_onto (D.suc_plus'' km) (D.suc_plus'' ln) (Mid f) bf in
  sface_of_bw_onto
    (D.zero_plus (dom_bwsface bf))
    (D.zero_plus (cod_bwsface bf))
    (id_sface D.zero) bf

(* ********** Face Trees ********** *)

(* A "face tree" of a dimension 'm records one object for each strict face of 'm, in a ternary tree so that they can be accessed randomly by strict face as well as sequentially.  In addition, we allow the *type* of each object to depend on the *domain* of the strict face, by parametrizing the notion with a functor. *)

module type Fam = sig
  type ('a, 'b) t
end

module Tree (F : Fam) = struct
  (* An ('m, 'n, 'b) gt is a ternary tree of height 'm whose interior nodes have their third branch special, and whose leaves are labeled by an element of F(n-k,b) , where k is the number of non-special branches taken to lead to the leaf.  Thus there is exactly one element of type F(n,b), 2*m elements of type F(n-1,b), down to 2^m elements of type F(n-m,b).  *)
  type (_, _, _) gt =
    | Leaf : ('n, 'b) F.t -> (D.zero, 'n, 'b) gt
    | Branch :
        (('m, 'n, 'b) gt, Endpoints.len) Bwv.t * ('m, 'n D.suc, 'b) gt
        -> ('m D.suc, 'n D.suc, 'b) gt

  type ('n, 'b) t = ('n, 'n, 'b) gt

  let rec gdim : type m n b. (m, n, b) gt -> m D.t = function
    | Leaf _ -> D.zero
    | Branch (_, br) -> D.suc (gdim br)

  let dim : type n b. (n, b) t -> n D.t = fun tr -> gdim tr

  (* A strict face is an index into a face tree.  *)

  let rec gnth :
      type m n k mk nm b.
      (mk, nm, b) gt -> (k, m, mk) D.plus -> (n, m, nm) D.plus -> (k, mk) sface -> (n, b) F.t =
   fun tr mk nm d ->
    match (tr, d) with
    | Leaf x, Zero ->
        let Zero = mk in
        let Zero = nm in
        x
    | Branch (br, _), End (d, e) ->
        let (Le mk') = plus_of_sface d in
        let Eq = D.minus_uniq' (dom_sface d) (Suc mk') mk in
        let (Suc nm') = nm in
        gnth (Bwv.nth e br) mk' nm' d
    | Branch (_, br), Mid d ->
        let (Suc mk) = N.suc_plus mk in
        gnth br mk nm d

  let nth : type n k b. (n, b) t -> (k, n) sface -> (k, b) F.t =
   fun tr d ->
    let (Le mk) = plus_of_sface d in
    gnth tr mk mk d

  (* We can build a face tree from a function that takes each face of 'n to something of the appropriate type. *)

  type ('n, 'b) builder = { leaf : 'm. ('m, 'n) sface -> ('m, 'b) F.t }

  let rec gbuild :
      type k m km n b l.
      m D.t ->
      (k, m, km) D.plus ->
      (l, m, n) D.plus ->
      (k, l) bwsface ->
      (n, b) builder ->
      (m, km, b) gt =
   fun m km lm d g ->
    match m with
    | Nat Zero ->
        let Zero, Zero = (km, lm) in
        Leaf (g.leaf (sface_of_bw d))
    | Nat (Suc m) ->
        let (Suc km') = km in
        Branch
          ( Bwv.map (fun e -> gbuild (Nat m) km' (D.suc_plus'' lm) (End (e, d)) g) Endpoints.indices,
            gbuild (Nat m) (D.suc_plus'' km) (D.suc_plus'' lm) (Mid d) g )

  let build : type n b. n D.t -> (n, b) builder -> (n, b) t =
   fun n g -> gbuild n (D.zero_plus n) (D.zero_plus n) Zero g

  (* Similarly, we can iterate over a face tree with a function that uses both a face and an input value. *)

  type ('n, 'b) iterator = { it : 'm. ('m, 'n) sface -> ('m, 'b) F.t -> unit }

  let rec giter :
      type k m km n b l.
      (k, m, km) D.plus ->
      (l, m, n) D.plus ->
      (k, l) bwsface ->
      (n, b) iterator ->
      (m, km, b) gt ->
      unit =
   fun km lm d g tr ->
    match tr with
    | Leaf x ->
        let Zero, Zero = (km, lm) in
        g.it (sface_of_bw d) x
    | Branch (ends, mid) ->
        let (Suc km') = km in
        Bwv.iter2 (fun e br -> giter km' (D.suc_plus'' lm) (End (e, d)) g br) Endpoints.indices ends;
        giter (D.suc_plus'' km) (D.suc_plus'' lm) (Mid d) g mid

  let iter : type n b. (n, b) iterator -> (n, b) t -> unit =
   fun g tr ->
    let n = dim tr in
    giter (D.zero_plus n) (D.zero_plus n) Zero g tr

  (* Monadic iteration over Maybe *)

  type ('n, 'b) iteratorOpt = { it : 'm. ('m, 'n) sface -> ('m, 'b) F.t -> unit option }

  let rec giterOpt :
      type k m km n b l.
      (k, m, km) D.plus ->
      (l, m, n) D.plus ->
      (k, l) bwsface ->
      (n, b) iteratorOpt ->
      (m, km, b) gt ->
      unit option =
   fun km lm d g tr ->
    let open Monad.Ops (Monad.Maybe) in
    match tr with
    | Leaf x ->
        let Zero, Zero = (km, lm) in
        g.it (sface_of_bw d) x
    | Branch (ends, mid) ->
        let (Suc km') = km in
        let* () =
          bwv_iterM2
            (fun e br -> giterOpt km' (D.suc_plus'' lm) (End (e, d)) g br)
            Endpoints.indices ends in
        giterOpt (D.suc_plus'' km) (D.suc_plus'' lm) (Mid d) g mid

  let iterOpt : type n b. (n, b) iteratorOpt -> (n, b) t -> unit option =
   fun g tr ->
    let n = dim tr in
    giterOpt (D.zero_plus n) (D.zero_plus n) Zero g tr

  (* Two-variable monadic iteration over Maybe *)

  type ('n, 'b) iteratorOpt2 = {
    it : 'm. ('m, 'n) sface -> ('m, 'b) F.t -> ('m, 'b) F.t -> unit option;
  }

  let rec giterOpt2 :
      type k m km n b l.
      (k, m, km) D.plus ->
      (l, m, n) D.plus ->
      (k, l) bwsface ->
      (n, b) iteratorOpt2 ->
      (m, km, b) gt ->
      (m, km, b) gt ->
      unit option =
   fun km lm d g tr1 tr2 ->
    let open Monad.Ops (Monad.Maybe) in
    match (tr1, tr2) with
    | Leaf x1, Leaf x2 ->
        let Zero, Zero = (km, lm) in
        g.it (sface_of_bw d) x1 x2
    | Branch (ends1, mid1), Branch (ends2, mid2) ->
        let (Suc km') = km in
        let* () =
          bwv_iterM3
            (fun e br1 br2 -> giterOpt2 km' (D.suc_plus'' lm) (End (e, d)) g br1 br2)
            Endpoints.indices ends1 ends2 in
        giterOpt2 (D.suc_plus'' km) (D.suc_plus'' lm) (Mid d) g mid1 mid2

  let iterOpt2 : type f2 n b. (n, b) iteratorOpt2 -> (n, b) t -> (n, b) t -> unit option =
   fun g tr1 tr2 ->
    let n = dim tr1 in
    giterOpt2 (D.zero_plus n) (D.zero_plus n) Zero g tr1 tr2
end

module TreeMap (F1 : Fam) (F2 : Fam) = struct
  module T1 = Tree (F1)
  module T2 = Tree (F2)

  type ('n, 'b, 'c) mapper = { map : 'm. ('m, 'n) sface -> ('m, 'b) F1.t -> ('m, 'c) F2.t }

  let rec gmap :
      type k m km n b c l.
      (k, m, km) D.plus ->
      (l, m, n) D.plus ->
      (k, l) bwsface ->
      (n, b, c) mapper ->
      (m, km, b) T1.gt ->
      (m, km, c) T2.gt =
   fun km lm d g tr ->
    match tr with
    | Leaf x ->
        let Zero, Zero = (km, lm) in
        Leaf (g.map (sface_of_bw d) x)
    | Branch (ends, mid) ->
        let (Suc km') = km in
        Branch
          ( Bwv.map2
              (fun e br -> gmap km' (D.suc_plus'' lm) (End (e, d)) g br)
              Endpoints.indices ends,
            gmap (D.suc_plus'' km) (D.suc_plus'' lm) (Mid d) g mid )

  let map : type n b c. (n, b, c) mapper -> (n, b) T1.t -> (n, c) T2.t =
   fun g tr ->
    let n = T1.dim tr in
    gmap (D.zero_plus n) (D.zero_plus n) Zero g tr
end

(* ********** Tubes ********** *)

(* A "tube" represents the arguments of a perhaps-partial instantiation of a higher-dimensional type.  Note that even if it is fully instantiated, it has one fewer arguments that count_faces: it's missing the top filler. *)
type (_, _, _) count_tube =
  | Tube : {
      (* The type is (m+n)-dimensional. *)
      plus_dim : ('m, 'n, 'mn) D.plus;
      (* If we fully instantiated it, it would take this many faces (including the top) *)
      total_faces : ('mn, 'mnf) count_faces;
      (* But since the result is only m-dimensional, we leave off this many faces (also including the top) *)
      missing_faces : ('m, 'mf) count_faces;
      (* So we need the difference between those two. *)
      plus_faces : ('f, 'mf, 'mnf) N.plus;
    }
      -> ('m, 'n, 'f) count_tube

let tube_uninst : type m n f. (m, n, f) count_tube -> m D.t =
 fun (Tube tube) -> N.pow_right tube.missing_faces

let tube_inst : type m n f. (m, n, f) count_tube -> n D.t =
 fun (Tube tube) -> D.plus_right tube.plus_dim

let tube_zero : (D.zero, D.zero, N.zero) count_tube =
  Tube { plus_dim = Zero; total_faces = Zero; missing_faces = Zero; plus_faces = Suc Zero }

(*
let tube_zero' : type m. m D.t -> (m, D.zero, N.zero) count_tube =
 fun m ->
  let (Faces mf) = count_faces m in
  Tube
    {
      plus_dim = Zero;
      total_faces = mf;
      missing_faces = mf;
      plus_faces = D.zero_plus (faces_out mf);
    }
*)

type (_, _) has_tube = Has_tube : ('m, 'n, 'f) count_tube -> ('m, 'n) has_tube

let has_tube : type m n mn. m D.t -> n D.t -> (m, n) has_tube =
 fun m n ->
  let (Plus plus_dim) = D.plus n in
  let (Faces total_faces) = count_faces (D.plus_out m plus_dim) in
  let (Faces missing_faces) = count_faces m in
  let (Faces n_faces) = count_faces (D.plus_right plus_dim) in
  let emen = N.pow_plus (N.suc Endpoints.len) missing_faces n_faces plus_dim total_faces in
  let (Pos _) = N.pow_pos (Pos Endpoints.len) n_faces in
  let (Suc (_, plus_faces)) = emen in
  Has_tube (Tube { plus_dim; total_faces; missing_faces; plus_faces })

(* Two tubes in succession combine to a larger one. *)

type (_, _, _, _, _, _) tube_plus_tube =
  | Tube_plus_tube :
      ('n, 'k, 'nk) D.plus * ('m, 'nk, 'fm) count_tube * ('fmnk, 'fmn, 'fm) N.plus * ('a, 'fm) Bwv.t
      -> ('m, 'n, 'k, 'fmnk, 'fmn, 'a) tube_plus_tube

let tube_plus_tube :
    type m n mn k fmnk fmn a.
    (m, n, mn) D.plus ->
    (mn, k, fmnk) count_tube ->
    (m, n, fmn) count_tube ->
    (a, fmnk) Bwv.t ->
    (a, fmn) Bwv.t ->
    (m, n, k, fmnk, fmn, a) tube_plus_tube =
 fun mn (Tube fmnk) (Tube fmn) argsk argsn ->
  let (Plus nk) = D.plus (D.plus_right fmnk.plus_dim) in
  let Eq = N.plus_uniq mn fmn.plus_dim in
  let Eq = N.pow_uniq fmnk.missing_faces fmn.total_faces in
  let (Plus ff) = N.plus (N.plus_left fmn.plus_faces (faces_out fmn.total_faces)) in
  Tube_plus_tube
    ( nk,
      Tube
        {
          plus_dim = D.plus_assocr mn nk fmnk.plus_dim;
          total_faces = fmnk.total_faces;
          missing_faces = fmn.missing_faces;
          plus_faces = D.plus_assocl ff fmn.plus_faces fmnk.plus_faces;
        },
      ff,
      Bwv.append ff argsk argsn )

type (_, _, _) take_tube =
  | Take :
      ('m, 'n, 'mn) D.plus
      * ('m, 'mf) count_faces
      * ('f, 'mf, 'mnf) N.plus
      * ('a, 'f) Bwv.t
      * 'a list
      -> ('a, 'mn, 'mnf) take_tube

let rec take_tube : type a n f. (n, f) count_faces -> a list -> (a, n, f) take_tube =
 fun nf xs ->
  let n = dim_faces nf in
  match n with
  | Nat Zero -> Take (Zero, nf, N.zero_plus (faces_out nf), Emp, xs)
  | Nat (Suc _) -> (
      let (Suc (pnf, Suc (pnf_times_e, pnf_times_e__plus_pnf))) = nf in
      match Bwv.of_list (N.times_out pnf_times_e) xs with
      | None -> Take (Zero, nf, N.zero_plus (faces_out nf), Emp, xs)
      | Some (args1, rest1) ->
          let (Take (kl, missing_faces, plus_faces, args2, rest2)) = take_tube pnf rest1 in
          let (Plus pnf_times_e__plus_f) = N.plus (Bwv.length args2) in
          let pnf_times_e__plus_f___plus_kf =
            N.plus_assocl pnf_times_e__plus_f plus_faces pnf_times_e__plus_pnf in
          Take
            ( Suc kl,
              missing_faces,
              pnf_times_e__plus_f___plus_kf,
              Bwv.append pnf_times_e__plus_f args1 args2,
              rest2 ))

(* ********** Faces ********** *)

(* A face is a permutation followed by a strict face, hence a map as for a strict face that need not be order-preserving. *)

type (_, _) face = Face : ('m, 'n) sface * 'm perm -> ('m, 'n) face

let id_face : type n. n D.t -> (n, n) face = fun n -> Face (id_sface n, id_perm n)

(* Faces are closed under composition, by way of a distributive law between permutations and strict faces.  To define this we need a similar sort of "residual" of a strict face and an index, which picks out the image of that index and the strict face with that index and its image (if any) removed. *)

type (_, _) sface_residual =
  | End : ('m, 'n) sface * Endpoints.t -> ('m, 'n D.suc) sface_residual
  | Mid : ('m, 'n) sface * 'm D.suc D.index -> ('m D.suc, 'n D.suc) sface_residual

let rec sface_residual : type m n. (m, n) sface -> n D.index -> (m, n) sface_residual =
 fun f k ->
  match (k, f) with
  | Top, End (f', e) -> End (f', e)
  | Top, Mid f' -> Mid (f', Top)
  | Pop k', End (f', e) -> (
      match sface_residual f' k' with
      | End (f'', e') -> End (End (f'', e), e')
      | Mid (f'', l) -> Mid (End (f'', e), l))
  | Pop k', Mid f' -> (
      match sface_residual f' k' with
      | End (f'', e') -> End (Mid f'', e')
      | Mid (f'', l) -> Mid (Mid f'', Pop l))

let rec perm_sface : type m n. n perm -> (m, n) sface -> (m, n) face =
 fun a b ->
  match a with
  | Zero _ -> Face (b, id_perm (dom_sface b))
  | Suc (p, k) -> (
      match sface_residual b k with
      | End (f, e) ->
          let (Face (f', p')) = perm_sface p f in
          Face (End (f', e), p')
      | Mid (f, l) ->
          let (Face (f', p')) = perm_sface p f in
          Face (Mid f', Suc (p', l)))

let comp_face : type m n k. (n, k) face -> (m, n) face -> (m, k) face =
 fun (Face (a, b)) (Face (c, d)) ->
  let (Face (c', b')) = perm_sface b c in
  Face (comp_sface a c', comp_perm b' d)

let dom_face : type m n. (m, n) face -> m D.t = function
  | Face (_, p) -> dim_perm p

let cod_face : type m n. (m, n) face -> n D.t = function
  | Face (f, _) -> cod_sface f

let face_of_sface : type m n. (m, n) sface -> (m, n) face = fun f -> Face (f, id_perm (dom_sface f))
let face_of_perm : type m. m perm -> (m, m) face = fun p -> Face (id_sface (dim_perm p), p)

(* Concatenate two faces left-to-right. *)
let face_plus_face :
    type m n mn k l kl.
    (k, m) face -> (m, n, mn) D.plus -> (k, l, kl) D.plus -> (l, n) face -> (kl, mn) face =
 fun (Face (fkm, pk)) mn kl (Face (fln, pl)) ->
  Face (sface_plus_sface fkm mn kl fln, perm_plus_perm pk kl pl)

type _ face_of = Face_of : ('m, 'n) face -> 'n face_of

module FaceFam = struct
  type ('n, 'm) t = 'm face_of
end

module FaceTree = Tree (FaceFam)

(* ********** Operators ********** *)

(* Finally, a general operator is a degeneracy followed by a strict face. *)

type (_, _) op = Op : ('n, 'k) sface * ('m, 'n) deg -> ('m, 'k) op

let id_op : type n. n D.t -> (n, n) op = fun n -> Op (id_sface n, id_deg n)

(* To compose operators, we use another distributive law. *)

let rec deg_sface : type m n k. (n, k) deg -> (m, n) sface -> (m, k) op =
 fun a b ->
  match a with
  | Zero _ ->
      let m = dom_sface b in
      Op (Zero, Zero m)
  | Suc (p, k) -> (
      match sface_residual b k with
      | End (f, e) ->
          let (Op (f', p')) = deg_sface p f in
          Op (End (f', e), p')
      | Mid (f, l) ->
          let (Op (f', p')) = deg_sface p f in
          Op (Mid f', Suc (p', l)))

let comp_op : type m n k. (n, k) op -> (m, n) op -> (m, k) op =
 fun (Op (a, b)) (Op (c, d)) ->
  let (Op (c', b')) = deg_sface b c in
  Op (comp_sface a c', comp_deg b' d)

let dom_op : type m n. (m, n) op -> m D.t = function
  | Op (_, s) -> dom_deg s

let cod_op : type m n. (m, n) op -> n D.t = function
  | Op (f, _) -> cod_sface f

let op_of_deg : type m n. (m, n) deg -> (m, n) op = fun s -> Op (id_sface (cod_deg s), s)
let op_of_sface : type m n. (m, n) sface -> (m, n) op = fun f -> Op (f, id_deg (dom_sface f))

let op_plus_op :
    type m n mn k l kl.
    (k, m) op -> (m, n, mn) D.plus -> (k, l, kl) D.plus -> (l, n) op -> (kl, mn) op =
 fun (Op (d1, s1)) mn kl (Op (d2, s2)) ->
  let (Plus middle) = D.plus (dom_sface d2) in
  Op (sface_plus_sface d1 mn middle d2, deg_plus_deg s1 middle kl s2)

type _ op_of = Of : ('m, 'n) op -> 'n op_of
type _ op_of_plus = Of : ('m, 'n) sface * 'm deg_of_plus -> 'n op_of_plus

let comp_op_of : type m n. (m, n) op -> m op_of -> n op_of = fun op (Of op') -> Of (comp_op op op')

let comp_op_deg_of_plus : type m n. (m, n) op -> m deg_of_plus -> n op_of_plus =
 fun (Op (f, s2)) s1 -> Of (f, comp_deg_of_plus s2 s1)

(* ********** Insertions ********** *)

(* An insertion of 'c into 'b is a permutation that maintains the relative order of 'b. *)
type (_, _, _) insertion =
  | Zero : 'a D.t -> ('a, 'a, D.zero) insertion
  | Suc : ('a, 'b, 'c) insertion * 'a D.suc D.index -> ('a D.suc, 'b, 'c D.suc) insertion

let zero_ins : type a. a D.t -> (a, a, D.zero) insertion = fun a -> Zero a

let rec dom_ins : type a b c. (a, b, c) insertion -> a D.t = function
  | Zero a -> a
  | Suc (ins, _) -> N.suc (dom_ins ins)

(* The domain of an insertion is the sum of the two pieces of its codomain. *)
let rec plus_of_ins : type a b c. (a, b, c) insertion -> (b, c, a) D.plus = function
  | Zero _ -> Zero
  | Suc (i, _) -> Suc (plus_of_ins i)

(* It induces a degeneracy, which is in fact a permutation. *)
let rec deg_of_ins : type a b c bc. (a, b, c) insertion -> (b, c, bc) D.plus -> (a, bc) deg =
 fun i bc ->
  match (i, bc) with
  | Zero a, Zero -> id_deg a
  | Suc (i, e), Suc bc -> Suc (deg_of_ins i bc, e)

let rec perm_of_ins : type a b c bc. (a, b, c) insertion -> a perm =
  (* fun i -> deg_of_ins i (plus_of_ins i) *)
  function
  | Zero a -> id_perm a
  | Suc (i, e) -> Suc (perm_of_ins i, e)

let deg_of_plus_of_ins : type a b c bc. (a, b, c) insertion -> b deg_of_plus =
 fun ins -> Of (plus_of_ins ins, perm_of_ins ins)

(* Any degeneracy with a decomposition of its codomain factors as an insertion followed by a whiskered degeneracy. *)

type (_, _, _) insfact = Insfact : ('a, 'b) deg * ('ac, 'a, 'c) insertion -> ('ac, 'b, 'c) insfact

let comp_insfact : type a b c ac bc. (ac, b, c) insfact -> (b, c, bc) D.plus -> (ac, bc) deg =
 fun (Insfact (s, i)) bc ->
  let ip = plus_of_ins i in
  comp_deg (deg_plus s bc ip) (deg_of_ins i ip)

let rec insfact : type ac b c bc. (ac, bc) deg -> (b, c, bc) D.plus -> (ac, b, c) insfact =
 fun s bc ->
  match bc with
  | Zero -> Insfact (s, Zero (dom_deg s))
  | Suc bc ->
      let (Suc (s, e)) = s in
      let (Insfact (s, i)) = insfact s bc in
      Insfact (s, Suc (i, e))

(* ********** Special generators ********** *)

type one = D.one

let one = D.one
let pos_one : one D.pos = Pos D.zero
let faces_one : (one, N.three) count_faces = Suc (Zero, N.one_times N.three)

let tube_one : (D.zero, one, N.two) count_tube =
  Tube
    {
      plus_dim = Suc Zero;
      total_faces = faces_one;
      missing_faces = faces_zero;
      plus_faces = Suc Zero;
    }

let refl : (one, D.zero) deg = Zero D.one

type two = D.two

let two = D.two
let sym : (two, two) deg = Suc (Suc (Zero D.zero, Top), Pop Top)
