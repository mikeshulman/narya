open Util

(* ********** Endpoints ********** *)

(* We parametrize over an abstract module specifying how many endpoints our cubes have. *)

module Endpoints = struct
  type len = N.two
  type t = len N.index

  let len : len N.t = N.two
  let indices : (t, len) Bwv.t = Snoc (Snoc (Emp, Pop Top), Top)

  let to_string : t option -> string = function
    | Some Top -> "1"
    | Some (Pop x) ->
        let Top = x in
        "0"
    | None -> "2"

  let of_char : char -> (t option, unit) result = function
    | '0' -> Ok (Some (Pop Top))
    | '1' -> Ok (Some Top)
    | '2' -> Ok None
    | _ -> Error ()
end

(* ********** Dimensions ********** *)

(* In this file we define "dimensions" to be type-level natural numbers.  However, in the interface we expose only that they are a type-level monoid with some extra structure.  Thus, the implementation is parametric over a specification of dimensions and their operators.  In addition, this file itself is parametric over Endpoints, which abstractly specifies a finite number of endpoints for each dimension. *)

module D = N

let to_int (n : 'a D.t) : int = N.to_int n

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

(* Another possible definition, "inductive on the other side", is:

   type (_, _) deg =
     | Zero : (D.zero, D.zero) deg
     | Deg : ('a, 'b) deg -> ('a D.suc, 'b) deg
     | Perm : ('a, 'b) deg * 'b D.suc D.index -> ('a D.suc, 'b D.suc) deg
*)

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
  | Zero n -> (
      match compare n D.zero with
      | Eq -> Some ()
      | Neq -> None)
  | Suc (p, Top) -> is_id_deg p
  | Suc (_, Pop _) -> None

(* A degeneracy of a positive dimension is still positive *)
let pos_deg : type m n. n D.pos -> (m, n) deg -> m D.pos =
 fun n s ->
  match (n, s) with
  | Pos _, Suc (s, _) -> Pos (dom_deg s)

(* Are two degeneracies exactly equal? *)
let deg_equal : type m n k l. (m, n) deg -> (k, l) deg -> unit option =
 fun s1 s2 ->
  match (N.compare (dom_deg s1) (dom_deg s2), N.compare (cod_deg s1) (cod_deg s2)) with
  | Eq, Eq ->
      (* Degeneracies with the same domain *and* codomain can be compared with simple structural equality. *)
      if s1 = s2 then Some () else None
  | _ -> None

(* Is one degeneracy, with greater codomain, an identity extension of another? *)
let rec deg_is_idext :
    type n l nl m k. (n, l, nl) D.plus -> (m, n) deg -> (k, nl) deg -> unit option =
 fun nl s1 s2 ->
  match (nl, s2) with
  | Zero, _ -> deg_equal s1 s2
  | Suc nl, Suc (s2, Top) -> deg_is_idext nl s1 s2
  | _ -> None

(* We consider two degeneracies "equivalent" if they differ by an identity extension on the right (i.e. post-whiskering with an identity). *)
let deg_equiv : type m n k l. (m, n) deg -> (k, l) deg -> unit option =
 fun s1 s2 ->
  match N.compare (cod_deg s1) (cod_deg s2) with
  | Eq -> deg_equal s1 s2
  | Lt nl -> deg_is_idext nl s1 s2
  | Gt nl -> deg_is_idext nl s2 s1

(* Every dimension is a degeneracy of zero. *)
let deg_zero : type a. a D.t -> (a, D.zero) deg = fun a -> Zero a

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

let is_id_any_deg : any_deg -> unit option = function
  | Any s -> is_id_deg s

(* Converting to and from strings. *)
let rec ints_of_deg : type a b. (a, b) deg -> (int, a) Bwv.t = function
  | Zero a -> Bwv.init a (fun _ -> 0)
  | Suc (s, k) -> Bwv.insert k (D.to_int (cod_deg s) + 1) (ints_of_deg s)

let string_of_deg : type a b. (a, b) deg -> string =
 fun s ->
  String.concat
    (if D.to_int (cod_deg s) > 9 then "_" else "")
    (Bwv.to_list_map string_of_int (ints_of_deg s))

type _ deg_to = To : ('m, 'n) deg -> 'm deg_to

let rec deg_of_ints : type n. (int, n) Bwv.t -> int -> n deg_to option =
 fun xs i ->
  if i <= 0 then
    if Bwv.fold_right (fun x b -> x = 0 && b) xs true then Some (To (Zero (Bwv.length xs)))
    else None
  else
    match xs with
    | Emp -> None
    | Snoc _ -> (
        match Bwv.find_remove i xs with
        | None -> None
        | Some (xs, j) -> (
            match deg_of_ints xs (i - 1) with
            | None -> None
            | Some (To s) -> Some (To (Suc (s, j)))))

let deg_of_string : string -> any_deg option =
 fun str ->
  let (Wrap ints) =
    if String.contains str '_' then Bwv.of_list_map int_of_string (String.split_on_char '_' str)
    else
      String.fold_left
        (fun (Bwv.Wrap l) c -> Wrap (Snoc (l, int_of_string (String.make 1 c))))
        (Wrap Emp) str in
  match deg_of_ints ints (Bwv.fold_left (fun x y -> max x y) 0 ints) with
  | None -> None
  | Some (To s) -> Some (Any s)

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
      Le (N.suc_plus' mn)

type any_sface = Any_sface : ('n, 'k) sface -> any_sface

let rec string_of_sface : type n k. (n, k) sface -> string = function
  | Zero -> ""
  | End (fa, e) -> string_of_sface fa ^ Endpoints.to_string (Some e)
  | Mid fa -> string_of_sface fa ^ Endpoints.to_string None

let sface_of_string : string -> any_sface option =
 fun str ->
  String.fold_left
    (fun fa x ->
      match (fa, Endpoints.of_char x) with
      | None, _ | _, Error _ -> None
      | Some (Any_sface fa), Ok (Some e) -> Some (Any_sface (End (fa, e)))
      | Some (Any_sface fa), Ok None -> Some (Any_sface (Mid fa)))
    (Some (Any_sface Zero)) str

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

(* ********** Cubes ********** *)

(* A cube of dimension 'm is a data structure that records one object for each strict face of 'm, in a ternary tree so that they can be accessed randomly by strict face as well as sequentially.  We allow the *type* of each object to depend on the *domain* of the strict face that indexes it, by parametrizing the notion with a functor.  We also allow an extra dependence on some additional type, so that an individual functor application can be parametric. *)

module type Fam = sig
  (* 'a is the domain of the strict face, 'b is an extra parameter. *)
  type ('a, 'b) t
end

module Cube (F : Fam) = struct
  (* First we define an auxiliary data structure.  An ('m, 'n, 'b) gt is a ternary tree of height 'm whose interior nodes have their last branch special, and whose leaves are labeled by an element of F(n-k,b) , where k is the number of non-special branches taken to lead to the leaf.  Thus there is exactly one element of type F(n,b), 2*m elements of type F(n-1,b), down to 2^m elements of type F(n-m,b).  *)
  type (_, _, _) gt =
    | Leaf : ('n, 'b) F.t -> (D.zero, 'n, 'b) gt
    | Branch :
        (('m, 'n, 'b) gt, Endpoints.len) Bwv.t * ('m, 'n D.suc, 'b) gt
        -> ('m D.suc, 'n D.suc, 'b) gt

  (* Now a cube of dimension 'n with parameter 'b is obtained by coinciding the labeling dimension and the height. *)
  type ('n, 'b) t = ('n, 'n, 'b) gt

  (* This two-step data definition means that all the functions that act on them must also be defined in terms of a gt version.  However, in the interface we expose only the t versions. *)

  (* For instance, we can compute the dimension of a cube. *)
  let rec gdim : type m n b. (m, n, b) gt -> m D.t = function
    | Leaf _ -> D.zero
    | Branch (_, br) -> D.suc (gdim br)

  let dim : type n b. (n, b) t -> n D.t = fun tr -> gdim tr

  (* A cube of dimension zero is just an element. *)

  let singleton : type b. (D.zero, b) F.t -> (D.zero, b) t = fun x -> Leaf x

  (* A strict face is an index into a face tree.  *)

  let rec gfind :
      type m n k km nm b.
      (km, nm, b) gt -> (k, m, km) D.plus -> (n, m, nm) D.plus -> (k, km) sface -> (n, b) F.t =
   fun tr km nm d ->
    match (tr, d) with
    | Leaf x, Zero ->
        let Zero = km in
        let Zero = nm in
        x
    | Branch (br, _), End (d, e) ->
        let (Le km') = plus_of_sface d in
        let Eq = D.minus_uniq' (dom_sface d) (Suc km') km in
        let (Suc nm') = nm in
        gfind (Bwv.nth e br) km' nm' d
    | Branch (_, br), Mid d ->
        let (Suc km) = N.suc_plus km in
        gfind br km nm d

  let find : type n k b. (n, b) t -> (k, n) sface -> (k, b) F.t =
   fun tr d ->
    let (Le km) = plus_of_sface d in
    gfind tr km km d

  let rec gfind_top : type k n b. (k, n, b) gt -> (n, b) F.t = function
    | Leaf x -> x
    | Branch (_, br) -> gfind_top br

  let find_top : type n b. (n, b) t -> (n, b) F.t = fun tr -> gfind_top tr

  (* Heterogeneous lists and multimaps, which take the current face as input everywhere in addition to the values in the data structure.  We use the technique of heteregeneous generic traversal, which is a much more significant win here in terms of coding because we only have to descend into gt's once, and all the other operations can be derived from the simpler t version. *)

  module Heter = struct
    open Hlist

    (* An hlist of elements of F.t, with the first parameter fixed but the second varying along the list. *)
    type (_, _) hft =
      | [] : ('n, nil) hft
      | ( :: ) : ('n, 'x) F.t * ('n, 'xs) hft -> ('n, ('x, 'xs) cons) hft

    (* An hlist of gt's, with the first two parameters (dimensions) fixed but the third varying along the list.  *)
    type (_, _, _) hgt =
      | [] : ('m, 'n, nil) hgt
      | ( :: ) : ('m, 'n, 'x) gt * ('m, 'n, 'xs) hgt -> ('m, 'n, ('x, 'xs) cons) hgt

    (* A relational function constructing, for any tlist of value types, the corresponding tlist of gt types.  *)
    type (_, _, _, _) hgts =
      | Nil : ('m, 'n, nil, nil) hgts
      | Cons : ('m, 'n, 'xs, 'ys) hgts -> ('m, 'n, ('x, 'xs) cons, (('m, 'n, 'x) gt, 'ys) cons) hgts

    (* The next two functions are inverse isomorphisms. *)
    let rec hlist_of_hgt : type m n xs ys. (m, n, xs, ys) hgts -> (m, n, xs) hgt -> ys hlist =
     fun hs xs ->
      match (hs, xs) with
      | Nil, [] -> []
      | Cons hs, x :: xs -> x :: hlist_of_hgt hs xs

    let rec hgt_of_hlist : type m n xs ys. (m, n, xs, ys) hgts -> ys hlist -> (m, n, xs) hgt =
     fun hs xs ->
      match (hs, xs) with
      | Nil, [] -> []
      | Cons hs, x :: xs -> x :: hgt_of_hlist hs xs

    (* hgts preserves validity of tlists. *)
    let rec tlist_hgts : type m n xs ys. (m, n, xs, ys) hgts -> xs tlist -> ys tlist =
     fun hs xs ->
      match (hs, xs) with
      | Nil, Nil -> Nil
      | Cons hs, Cons xs -> Cons (tlist_hgts hs xs)

    (* And any tlist of value types has some corresponding list of gts. *)
    type (_, _, _) has_hgts = Hgts : ('m, 'n, 'xs, 'xss) hgts -> ('m, 'n, 'xs) has_hgts

    let rec hgts_of_tlist : type m n xs. xs tlist -> (m, n, xs) has_hgts = function
      | Nil -> Hgts Nil
      | Cons xs ->
          let (Hgts xss) = hgts_of_tlist xs in
          Hgts (Cons xss)

    (* Extract the pieces of an hlist of gt's. *)
    let rec lab : type n bs. (D.zero, n, bs) hgt -> (n, bs) hft = function
      | [] -> []
      | Leaf x :: xs -> x :: lab xs

    type (_, _, _) ends =
      | Ends : ('m, 'n, 'bs, 'hs) hgts * ('hs, Endpoints.len) Bwv.Heter.ht -> ('m, 'n, 'bs) ends

    let rec ends : type m n bs. (m D.suc, n D.suc, bs) hgt -> (m, n, bs) ends =
     fun xss ->
      match xss with
      | [] -> Ends (Nil, [])
      | Branch (es, _) :: xs ->
          let (Ends (hs, ess)) = ends xs in
          Ends (Cons hs, es :: ess)

    let rec mid : type m n bs. (m D.suc, n D.suc, bs) hgt -> (m, n D.suc, bs) hgt = function
      | [] -> []
      | Branch (_, m) :: xs -> m :: mid xs

    (* Construct an hlist of gt's as leaves or branches.  *)
    let rec leaf : type n bs. (n, bs) hft -> (D.zero, n, bs) hgt = function
      | [] -> []
      | x :: xs -> Leaf x :: leaf xs

    let rec branch :
        type m n bs hs.
        (m, n, bs, hs) hgts ->
        (hs, Endpoints.len) Bwv.Heter.ht ->
        (m, n D.suc, bs) hgt ->
        (m D.suc, n D.suc, bs) hgt =
     fun hs endss mids ->
      match (hs, endss, mids) with
      | Nil, [], [] -> []
      | Cons hs, ends :: endss, mid :: mids -> Branch (ends, mid) :: branch hs endss mids
  end

  (* OCaml can't always tell from context what [x ; xs] should be; in particular it often fails to notice hfts.  So we also give a different syntax that is unambiguous.  *)
  module Infix = struct
    let hnil : type n. (n, Hlist.nil) Heter.hft = []

    let ( @: ) : type n x xs. (n, x) F.t -> (n, xs) Heter.hft -> (n, (x, xs) Hlist.cons) Heter.hft =
     fun x xs -> x :: xs
  end

  open Infix

  module Monadic (M : Monad.Plain) = struct
    open Monad.Ops (M)
    module BwvM = Bwv.Monadic (M)

    (* The function that we apply on a generic traversal must be polymorphic over the domain dimension of the face, so we wrap it in a record. *)
    type ('n, 'bs, 'cs) pmapperM = {
      map : 'm. ('m, 'n) sface -> ('m, 'bs) Heter.hft -> ('m, 'cs) Heter.hft M.t;
    }

    (* Finally, here is the generic monadic traversal of a gt. *)
    let rec gpmapM :
        type k m km n b bs cs l.
        (k, m, km) D.plus ->
        (l, m, n) D.plus ->
        (k, l) bwsface ->
        (n, (b, bs) Hlist.cons, cs) pmapperM ->
        (m, km, (b, bs) Hlist.cons) Heter.hgt ->
        cs Hlist.tlist ->
        (m, km, cs) Heter.hgt M.t =
     fun km lm d g trs cst ->
      match trs with
      | Leaf _ :: _ ->
          let Zero, Zero = (km, lm) in
          let* x = g.map (sface_of_bw d) (Heter.lab trs) in
          return (Heter.leaf x)
      | Branch (_, _) :: _ ->
          let (Suc km') = km in
          let (Ends (hs, ends)) = Heter.ends trs in
          let mid = Heter.mid trs in
          let (Hgts newhs) = Heter.hgts_of_tlist cst in
          let* newends =
            BwvM.pmapM
              (fun (e :: brs) ->
                let* xs =
                  gpmapM km' (D.suc_plus'' lm) (End (e, d)) g (Heter.hgt_of_hlist hs brs) cst in
                return (Heter.hlist_of_hgt newhs xs))
              (Endpoints.indices :: ends) (Heter.tlist_hgts newhs cst) in
          let* newmid = gpmapM (D.suc_plus'' km) (D.suc_plus'' lm) (Mid d) g mid cst in
          return (Heter.branch newhs newends newmid)

    (* And the actual one for a t, which we can henceforth restrict our attention to. *)
    let pmapM :
        type n b bs cs.
        (n, (b, bs) Hlist.cons, cs) pmapperM ->
        (n, n, (b, bs) Hlist.cons) Heter.hgt ->
        cs Hlist.tlist ->
        (n, n, cs) Heter.hgt M.t =
     fun g xs cs ->
      let (x :: _) = xs in
      let n = dim x in
      gpmapM (D.zero_plus n) (D.zero_plus n) Zero g xs cs

    type ('n, 'bs, 'c) mmapperM = {
      map : 'm. ('m, 'n) sface -> ('m, 'bs) Heter.hft -> ('m, 'c) F.t M.t;
    }

    let mmapM :
        type n b bs c.
        (n, (b, bs) Hlist.cons, c) mmapperM -> (n, n, (b, bs) Hlist.cons) Heter.hgt -> (n, c) t M.t
        =
     fun g xs ->
      let* [ ys ] =
        pmapM
          {
            map =
              (fun fa x ->
                let* y = g.map fa x in
                (* Apparently writing [y] is insufficiently polymorphic *)
                return (y @: []));
          }
          xs (Cons Nil) in
      return ys

    type ('n, 'bs) miteratorM = { it : 'm. ('m, 'n) sface -> ('m, 'bs) Heter.hft -> unit M.t }

    let miterM :
        type n b bs.
        (n, (b, bs) Hlist.cons) miteratorM -> (n, n, (b, bs) Hlist.cons) Heter.hgt -> unit M.t =
     fun g xs ->
      let* [] =
        pmapM
          {
            map =
              (fun fa x ->
                let* () = g.it fa x in
                return hnil);
          }
          xs Nil in
      return ()

    (* The builder function isn't quite a special case of the generic traversal, since it needs to maintain different information when constructing a cube from scratch. *)

    type ('n, 'b) builderM = { build : 'm. ('m, 'n) sface -> ('m, 'b) F.t M.t }

    let rec gbuildM :
        type k m mk l ml b.
        m D.t ->
        (m, k, mk) D.plus ->
        (m, l, ml) D.plus ->
        (k, l) bwsface ->
        (ml, b) builderM ->
        (m, mk, b) gt M.t =
     fun m mk ml d g ->
      match m with
      | Nat Zero ->
          let Eq = D.plus_uniq mk (D.zero_plus (dom_bwsface d)) in
          let Eq = D.plus_uniq ml (D.zero_plus (cod_bwsface d)) in
          let* x = g.build (sface_of_bw d) in
          return (Leaf x)
      | Nat (Suc m) ->
          let (Suc mk') = D.suc_plus mk in
          let* ends =
            BwvM.mapM
              (fun e -> gbuildM (Nat m) mk' (D.suc_plus ml) (End (e, d)) g)
              Endpoints.indices in
          let* mid = gbuildM (Nat m) (D.suc_plus mk) (D.suc_plus ml) (Mid d) g in
          return (Branch (ends, mid))

    let buildM : type n b. n D.t -> (n, b) builderM -> (n, b) t M.t =
     fun n g -> gbuildM n (D.plus_zero n) (D.plus_zero n) Zero g
  end

  (* Now we can specialize all of them to the identity modality. *)

  module IdM = Monadic (Monad.Identity)

  let pmap :
      type n b bs cs.
      (n, (b, bs) Hlist.cons, cs) IdM.pmapperM ->
      (n, n, (b, bs) Hlist.cons) Heter.hgt ->
      cs Hlist.tlist ->
      (n, n, cs) Heter.hgt =
   fun g xs ys -> IdM.pmapM { map = (fun fa x -> g.map fa x) } xs ys

  let mmap :
      type n b bs c.
      (n, (b, bs) Hlist.cons, c) IdM.mmapperM -> (n, n, (b, bs) Hlist.cons) Heter.hgt -> (n, c) t =
   fun g xs -> IdM.mmapM { map = (fun fa x -> g.map fa x) } xs

  let miter :
      type n b bs.
      (n, (b, bs) Hlist.cons) IdM.miteratorM -> (n, n, (b, bs) Hlist.cons) Heter.hgt -> unit =
   fun g xs -> IdM.miterM { it = (fun fa x -> g.it fa x) } xs

  let build : type n b. n D.t -> (n, b) IdM.builderM -> (n, b) t =
   fun n g -> IdM.buildM n { build = (fun fa -> g.build fa) }

  (* Folds.  As with lists and bwvs, the ordinary left fold can be defined as a special case of the generic traversal. *)

  type ('n, 'c, 'b) fold_lefter = { fold : 'm. 'c -> ('m, 'n) sface -> ('m, 'b) F.t -> 'c }

  let fold_left : type n b c. (n, c, b) fold_lefter -> c -> (n, b) t -> c =
   fun g acc tr ->
    let open Monadic (Monad.State (struct
      type t = c
    end)) in
    snd (miterM { it = (fun fa [ x ] c -> ((), g.fold c fa x)) } [ tr ] acc)

  (* A "subcube" of a cube of dimension n, determined by a face of n with dimension k, is the cube of dimension k consisting of the elements indexed by faces that factor through the given one. *)
  let subcube : type m n b. (m, n) sface -> (n, b) t -> (m, b) t =
   fun fa tr -> build (dom_sface fa) { build = (fun fb -> find tr (comp_sface fa fb)) }
end

(* In the vast majority of cases, the second type parameter 'b in a Fam can just *be* the type of the elements.  The only case when this doesn't work is when the type has to also depend on the dimension 'a. *)
module FamOf = struct
  type ('a, 'b) t = 'b
end

module CubeOf = struct
  include Cube (FamOf)

  (* In this special case, we can change the indexing dimension fairly arbitrarily, although it takes a bit of work to convince OCaml.  (Of course, semantically these are identity functions.) *)

  let rec lift : type m n1 n2 n12 b. (n1, n2, n12) D.plus -> (m, n1, b) gt -> (m, n12, b) gt =
   fun n12 tr ->
    match tr with
    | Leaf x -> Leaf x
    | Branch (ends, mid) ->
        let (Suc n12') = N.suc_plus n12 in
        Branch (Bwv.map (fun t -> lift n12' t) ends, lift n12 mid)

  let rec lower :
      type m k n1 n2 n12 b.
      (m, k, n1) D.plus -> (n1, n2, n12) D.plus -> (m, n12, b) gt -> (m, n1, b) gt =
   fun mk n12 tr ->
    match (tr, n12) with
    | Leaf x, _ -> Leaf x
    | _, Zero -> tr
    | Branch (ends, mid), Suc n12' ->
        let mk' = N.suc_plus mk in
        let (Suc mk'') = mk' in
        Branch (Bwv.map (fun t -> lower mk'' (N.suc_plus n12') t) ends, lower mk' n12 mid)

  (* We can also extract the elements of a cube and append them to a Bwv. *)

  let rec gflatten_append :
      type k m km n b l len f lenf.
      (k, m, km) D.plus ->
      (l, m, n) D.plus ->
      (k, l) bwsface ->
      (b, len) Bwv.t ->
      (m, km, b) gt ->
      (m, f) count_faces ->
      (len, f, lenf) N.plus ->
      (b, lenf) Bwv.t =
   fun km lm d acc tr mf lenf ->
    match tr with
    | Leaf x ->
        let Zero, Zero = (km, lm) in
        let Eq = faces_uniq faces_zero mf in
        let (Suc Zero) = lenf in
        Snoc (acc, x)
    | Branch (ends, mid) ->
        let (Suc km') = km in
        let (Suc (mf', Suc (ft, pq))) = mf in
        let (Plus lenf') = N.plus (N.times_out ft) in
        let lenff = N.plus_assocl lenf' pq lenf in
        let acc =
          Bwv.fold_left2_bind_append ft lenf' acc Endpoints.indices ends
            {
              append =
                (fun pq cx e br -> gflatten_append km' (D.suc_plus'' lm) (End (e, d)) cx br mf' pq);
            } in
        gflatten_append (D.suc_plus'' km) (D.suc_plus'' lm) (Mid d) acc mid mf' lenff

  let flatten_append :
      type n b len f lenf.
      (b, len) Bwv.t -> (n, b) t -> (n, f) count_faces -> (len, f, lenf) N.plus -> (b, lenf) Bwv.t =
   fun acc tr mf lenf ->
    let n = dim tr in
    gflatten_append (D.zero_plus n) (D.zero_plus n) Zero acc tr mf lenf

  let flatten : type n b f. (n, b) t -> (n, f) count_faces -> (b, f) Bwv.t =
   fun tr mf ->
    let n = dim tr in
    gflatten_append (D.zero_plus n) (D.zero_plus n) Zero Emp tr mf (N.zero_plus (faces_out mf))
end

(* ********** Tube faces ********** *)

type (_, _, _, _) tface =
  | End :
      ('m, 'nk) sface * ('n, 'k, 'nk) D.plus * Endpoints.t
      -> ('m, 'n, 'k D.suc, 'nk D.suc) tface
  | Mid : ('m, 'n, 'k, 'nk) tface -> ('m D.suc, 'n, 'k D.suc, 'nk D.suc) tface

let rec sface_of_tface : type m n k nk. (m, n, k, nk) tface -> (m, nk) sface = function
  | End (d, _, e) -> End (d, e)
  | Mid d -> Mid (sface_of_tface d)

let rec plus_of_tface : type m n k nk. (m, n, k, nk) tface -> (m, nk) d_le = function
  | End (d, _, _) ->
      let (Le mn) = plus_of_sface d in
      Le (Suc mn)
  | Mid d ->
      let (Le mn) = plus_of_tface d in
      Le (N.suc_plus' mn)

let rec cod_plus_of_tface : type m n k nk. (m, n, k, nk) tface -> (n, k, nk) D.plus = function
  | End (_, p, _) -> Suc p
  | Mid d -> Suc (cod_plus_of_tface d)

let rec dom_tface : type m n k nk. (m, n, k, nk) tface -> m D.t = function
  | End (d, _, _) -> dom_sface d
  | Mid d -> D.suc (dom_tface d)

let rec codl_tface : type m n k nk. (m, n, k, nk) tface -> n D.t = function
  | End (d, p, _) -> D.minus (cod_sface d) p
  | Mid d -> codl_tface d

let rec codr_tface : type m n k nk. (m, n, k, nk) tface -> k D.t = function
  | End (_, nk, _) -> D.suc (D.plus_right nk)
  | Mid d -> D.suc (codr_tface d)

let cod_tface : type m n k nk. (m, n, k, nk) tface -> nk D.t =
 fun d -> D.plus_out (codl_tface d) (cod_plus_of_tface d)

let tface_end : type m n k nk. (m, n, k, nk) tface -> Endpoints.t -> (m, n, k D.suc, nk D.suc) tface
    =
 fun d e -> End (sface_of_tface d, cod_plus_of_tface d, e)

let rec tface_plus :
    type m n k nk l ml kl nkl.
    (m, n, k, nk) tface ->
    (k, l, kl) D.plus ->
    (nk, l, nkl) D.plus ->
    (m, l, ml) D.plus ->
    (ml, n, kl, nkl) tface =
 fun d kl nkl ml ->
  match (kl, nkl, ml) with
  | Zero, Zero, Zero -> d
  | Suc kl, Suc nkl, Suc ml -> Mid (tface_plus d kl nkl ml)

(* A "proper face" is a fully instantiated tube face. *)

type ('m, 'n) pface = ('m, D.zero, 'n, 'n) tface

(* Any strict face is either a proper face or the top face. *)
(*
let rec pface_of_sface : type m n. (m, n) sface -> (m, n) pface option = function
  | Zero -> None
  | End (fa, e) -> Some (End (fa, D.zero_plus (cod_sface fa), e))
  | Mid fa -> (
      match pface_of_sface fa with
      | Some fb -> Some (Mid fb)
      | None -> None)
*)

(* Any strict face can be added to a tube face on the left to get another tube face. *)

let rec sface_plus_tface :
    type m n mn l nl mnl k p kp.
    (k, m) sface ->
    (m, n, mn) D.plus ->
    (m, nl, mnl) D.plus ->
    (k, p, kp) D.plus ->
    (p, n, l, nl) tface ->
    (kp, mn, l, mnl) tface =
 fun fkm mn m_nl kp fpnl ->
  match (fpnl, m_nl, kp) with
  | End (fpn, nl, e), Suc m_nl, kp ->
      let mn_l = D.plus_assocl mn nl m_nl in
      End (sface_plus_sface fkm m_nl kp fpn, mn_l, e)
  | Mid fpn, Suc m_nl, Suc kp -> Mid (sface_plus_tface fkm mn m_nl kp fpn)

let sface_plus_pface :
    type m n mn k p kp.
    (k, m) sface -> (m, n, mn) D.plus -> (k, p, kp) D.plus -> (p, n) pface -> (kp, m, n, mn) tface =
 fun fkm mn kp fpn -> sface_plus_tface fkm Zero mn kp fpn

(* Conversely, every tube face decomposes as an ordinary strict face added to a tube face along a decomposition of its uninstantiated dimensions. *)

type (_, _, _, _) tface_of_plus =
  | TFace_of_plus :
      ('p, 'q, 'pq) D.plus * ('p, 'n) sface * ('q, 'k, 'l, 'kl) tface
      -> ('pq, 'n, 'k, 'l) tface_of_plus

let rec tface_of_plus :
    type m n k nk l nkl. (n, k, nk) D.plus -> (m, nk, l, nkl) tface -> (m, n, k, l) tface_of_plus =
 fun nk d ->
  match d with
  | End (d, nk_l, e) ->
      let (Plus kl) = D.plus (D.plus_right nk_l) in
      let n_kl = D.plus_assocr nk kl nk_l in
      let (SFace_of_plus (pq, d1, d2)) = sface_of_plus n_kl d in
      TFace_of_plus (pq, d1, End (d2, kl, e))
  | Mid d ->
      let (TFace_of_plus (pq, d1, d2)) = tface_of_plus nk d in
      TFace_of_plus (Suc pq, d1, Mid d2)

(* In particular, any tube face decomposes as a strict face plus a proper face. *)

type (_, _, _) pface_of_plus =
  | PFace_of_plus :
      ('p, 'q, 'pq) D.plus * ('p, 'n) sface * ('q, 'k) pface
      -> ('pq, 'n, 'k) pface_of_plus

let pface_of_plus : type m n k nk. (m, n, k, nk) tface -> (m, n, k) pface_of_plus =
 fun d ->
  let (TFace_of_plus (pq, s, d)) = tface_of_plus Zero d in
  let Eq = D.plus_uniq (cod_plus_of_tface d) (D.zero_plus (codr_tface d)) in
  PFace_of_plus (pq, s, d)

(* Backwards tube faces *)

type (_, _, _, _) bwtface =
  | LEnd : Endpoints.t * ('m, 'n, 'k, 'nk) bwtface -> ('m, 'n D.suc, 'k, 'nk D.suc) bwtface
  | LMid : ('m, 'n, 'k, 'nk) bwtface -> ('m D.suc, 'n D.suc, 'k, 'nk D.suc) bwtface
  | REnd : Endpoints.t * ('m, 'k) bwsface -> ('m, D.zero, 'k D.suc, 'k D.suc) bwtface
  | RMid : ('m, D.zero, 'k, 'k) bwtface -> ('m D.suc, D.zero, 'k D.suc, 'k D.suc) bwtface

let rec dom_bwtface : type m n k nk. (m, n, k, nk) bwtface -> m D.t = function
  | LEnd (_, d) -> dom_bwtface d
  | LMid d -> D.suc (dom_bwtface d)
  | REnd (_, d) -> dom_bwsface d
  | RMid d -> D.suc (dom_bwtface d)

let rec codl_bwtface : type m n k nk. (m, n, k, nk) bwtface -> n D.t = function
  | LEnd (_, d) -> D.suc (codl_bwtface d)
  | LMid d -> D.suc (codl_bwtface d)
  | REnd (_, _) -> D.zero
  | RMid _ -> D.zero

(*
let rec codr_bwtface : type m n k nk. (m, n, k, nk) bwtface -> k D.t = function
  | LEnd (_, d) -> codr_bwtface d
  | LMid d -> codr_bwtface d
  | REnd (_, d) -> D.suc (cod_bwsface d)
  | RMid d -> D.suc (codr_bwtface d)
*)

let rec cod_bwtface : type m n k nk. (m, n, k, nk) bwtface -> nk D.t = function
  | LEnd (_, d) -> D.suc (cod_bwtface d)
  | LMid d -> D.suc (cod_bwtface d)
  | REnd (_, d) -> D.suc (cod_bwsface d)
  | RMid d -> D.suc (cod_bwtface d)

let rec bwsface_of_bwtface : type m n k nk. (m, n, k, nk) bwtface -> (m, nk) bwsface = function
  | LEnd (e, d) -> End (e, bwsface_of_bwtface d)
  | LMid d -> Mid (bwsface_of_bwtface d)
  | REnd (e, d) -> End (e, d)
  | RMid d -> Mid (bwsface_of_bwtface d)

let bwtface_rend :
    type m k. Endpoints.t -> (m, D.zero, k, k) bwtface -> (m, D.zero, k D.suc, k D.suc) bwtface =
 fun e d -> REnd (e, bwsface_of_bwtface d)

(* Converting a backwards tube face to a forwards one.  This requires three helper functions. *)

let rec tface_of_bw_r :
    type m1 m2 m n k1 k2 k nk1 nk.
    (m1, m2, m) D.plus ->
    (k1, k2, k) D.plus ->
    (nk1, k2, nk) D.plus ->
    (m1, n, k1, nk1) tface ->
    (m2, k2) bwsface ->
    (m, n, k, nk) tface =
 fun m12 k12 nk12 f bf ->
  match bf with
  | Zero ->
      let m1, k1, nk1 = (dom_tface f, codr_tface f, cod_tface f) in
      let Eq = D.plus_uniq m12 (D.plus_zero m1) in
      let Eq = D.plus_uniq k12 (D.plus_zero k1) in
      let Eq = D.plus_uniq nk12 (D.plus_zero nk1) in
      f
  | End (e, bf) -> tface_of_bw_r m12 (D.suc_plus'' k12) (D.suc_plus'' nk12) (tface_end f e) bf
  | Mid bf -> tface_of_bw_r (D.suc_plus'' m12) (D.suc_plus'' k12) (D.suc_plus'' nk12) (Mid f) bf

let rec tface_of_bw_lt :
    type m1 m2 m n k1 k2 k nk nk1.
    (m1, m2, m) D.plus ->
    (k1, k2, k) D.plus ->
    (nk1, k2, nk) D.plus ->
    (n, k1, nk1) D.plus ->
    (m1, nk1) sface ->
    (m2, D.zero, k2, k2) bwtface ->
    (m, n, k, nk) tface =
 fun m12 k12 n12k nk12 f bf ->
  match bf with
  | REnd (e, bf) -> tface_of_bw_r m12 (D.suc_plus'' k12) (D.suc_plus'' n12k) (End (f, nk12, e)) bf
  | RMid bf ->
      tface_of_bw_lt (D.suc_plus'' m12) (D.suc_plus'' k12) (D.suc_plus'' n12k) (Suc nk12) (Mid f) bf

let rec tface_of_bw_ls :
    type m1 m2 m n1 n2 k n nk nk2.
    (m1, m2, m) D.plus ->
    (n1, n2, n) D.plus ->
    (n1, nk2, nk) D.plus ->
    (m1, n1) sface ->
    (m2, n2, k, nk2) bwtface ->
    (m, n, k, nk) tface =
 fun m12 n12 nk12 f bf ->
  match bf with
  | LEnd (e, bf) -> tface_of_bw_ls m12 (D.suc_plus'' n12) (D.suc_plus'' nk12) (End (f, e)) bf
  | LMid bf -> tface_of_bw_ls (D.suc_plus'' m12) (D.suc_plus'' n12) (D.suc_plus'' nk12) (Mid f) bf
  | REnd (e, bf) ->
      let n1 = cod_sface f in
      let Eq = D.plus_uniq n12 (D.plus_zero n1) in
      tface_of_bw_r m12
        (D.suc_plus' (D.zero_plus (cod_bwsface bf)))
        (D.suc_plus'' nk12)
        (End (f, D.plus_zero n1, e))
        bf
  | RMid bf ->
      let n1 = cod_sface f in
      let Eq = D.plus_uniq n12 (D.plus_zero n1) in
      tface_of_bw_lt (D.suc_plus'' m12)
        (D.suc_plus' (D.zero_plus (cod_bwtface bf)))
        (D.suc_plus'' nk12) (Suc Zero) (Mid f) bf

let tface_of_bw : type m n k nk. (m, n, k, nk) bwtface -> (m, n, k, nk) tface =
 fun bf ->
  tface_of_bw_ls
    (D.zero_plus (dom_bwtface bf))
    (D.zero_plus (codl_bwtface bf))
    (D.zero_plus (cod_bwtface bf))
    (id_sface D.zero) bf

(* ********** Tube data structures ********** *)

module Tube (F : Fam) = struct
  module C = Cube (F)
  open C.Infix

  (* An (n,k,n+k)-tube is like a (n+k)-cube but where the top k indices (the "instantiated" ones) are not all maximal.  Hence if k=0 it is empty, while if n=0 it contains everything except the top face.  A (m,k,m+k,n)-gtube is the height-(m+k) part of such a tube, with k dimensions left to be instantiated and m uninstantiated, m+k total dimensions left, and n the current face dimension. *)
  type (_, _, _, _, _) gt =
    | Leaf : 'n D.t -> ('n, D.zero, 'n, 'nk, 'b) gt
    | Branch :
        (('mk, 'n, 'b) C.gt, Endpoints.len) Bwv.t * ('m, 'k, 'mk, 'n D.suc, 'b) gt
        -> ('m, 'k D.suc, 'mk D.suc, 'n D.suc, 'b) gt

  (* This definition gives a cardinality F(k,m) for (m,k,m+k,n,b) gtube with recurrence relations

     F(0,m) = 0
     F(k+1,m) = 3^(m+k) * 2 + F(k,m)

     Therefore, we can compute examples like

     F(1,m) = 3^m * 2 + F(0,m) = 3^m * 2 + 0 = 3^m * 2 = 3^(m+1) - 3^m
     F(2,m) = 3^(m+1) * 2 + F(1,m) = (3^(m+1) + 3^m) * 2 = (3^(m+2) + 3^(m+1)) - (3^(m+1) + 3^m) = 3^(m+2) - 3^m

     and so on, in general

     F(k,m) = 3^(m+k) - 3^m
  *)

  type ('n, 'k, 'nk, 'b) t = ('n, 'k, 'nk, 'nk, 'b) gt

  (* In a tube we always have m + k = m+k. *)

  let rec gplus : type m k mk n b. (m, k, mk, n, b) gt -> (m, k, mk) D.plus = function
    | Leaf _ -> Zero
    | Branch (_, mid) -> Suc (gplus mid)

  let plus : type m k mk b. (m, k, mk, b) t -> (m, k, mk) D.plus = fun t -> gplus t

  (* The constituents of a tube are valid dimensions. *)

  let inst : type m k mk b. (m, k, mk, b) t -> k D.t = fun t -> Nat (plus t)

  let rec guninst : type m k mk n b. (m, k, mk, n, b) gt -> m D.t = function
    | Leaf m -> m
    | Branch (_, mid) -> guninst mid

  let uninst : type m k mk b. (m, k, mk, b) t -> m D.t = fun t -> guninst t
  let out : type m k mk b. (m, k, mk, b) t -> mk D.t = fun t -> D.plus_out (uninst t) (plus t)

  (* The empty tube, with nothing instantiated *)

  let empty : type n b. n D.t -> (n, D.zero, n, b) t = fun n -> Leaf n

  (* Looking up with a tface *)

  let rec gfind :
      type m n k nk p q pq b.
      (n, k, nk, pq, b) gt ->
      (m, q, nk) D.plus ->
      (p, q, pq) D.plus ->
      (m, n, k, nk) tface ->
      (p, b) F.t =
   fun tr mq pq d ->
    match d with
    | End (d, _, e) ->
        (* End (d,e) : (m,n,k+1,nk+1) tface *)
        (* d : (m,nk) sface *)
        (* tr : (n,k+1,nk+1,pq+1,b) gt *)
        let (Branch (ends, _)) = tr in
        (* ends : bwv of (nk,pq,b) C.gt  *)
        let (Le km') = plus_of_sface d in
        (* km' : m + q = nk *)
        (* Suc km' : m + (q+1) = nk+1 *)
        (* mq : m + q+1 = nk+1 *)
        let Eq = D.minus_uniq' (dom_sface d) (Suc km') mq in
        (* q + 1 = q+1 *)
        (* pq : p + q+1 = pq+1 *)
        let (Suc pq') = pq in
        (* pq' : p + q = pq *)
        C.gfind (Bwv.nth e ends) km' pq' d
    | Mid d ->
        let (Branch (_, mid)) = tr in
        let (Suc mq) = N.suc_plus mq in
        gfind mid mq pq d

  let find : type m n k nk b. (n, k, nk, b) t -> (m, n, k, nk) tface -> (m, b) F.t =
   fun tr d ->
    let (Le km) = plus_of_tface d in
    gfind tr km km d

  (* The boundary of a cube is a maximal tube. *)

  let rec gboundary : type m n b. (m, n, b) C.gt -> (D.zero, m, m, n, b) gt = function
    | Leaf _ -> Leaf D.zero
    | Branch (ends, mid) -> Branch (ends, gboundary mid)

  let boundary : type n b. (n, b) C.t -> (D.zero, n, n, b) t = fun tr -> gboundary tr

  (* We can also pick out a less-instantiated part of a tube *)

  let rec gpboundary :
      type m k mk l kl mkl n b.
      (m, k, mk) D.plus -> (k, l, kl) D.plus -> (m, kl, mkl, n, b) gt -> (mk, l, mkl, n, b) gt =
   fun mk kl tr ->
    match (kl, tr) with
    | Zero, _ ->
        let Eq = D.plus_uniq mk (gplus tr) in
        Leaf (D.plus_out (guninst tr) mk)
    | Suc kl, Branch (ends, mid) -> Branch (ends, gpboundary mk kl mid)

  let pboundary :
      type m k mk l kl mkl b.
      (m, k, mk) D.plus -> (k, l, kl) D.plus -> (m, kl, mkl, b) t -> (mk, l, mkl, b) t =
   fun mk kl tr -> gpboundary mk kl tr

  (* Heterogeneous lists and multimaps *)

  (* The structure of hlists for tubes is exactly parallel to that for cubes. *)
  module Heter = struct
    open Hlist

    type (_, _, _, _, _) hgt =
      | [] : ('m, 'k, 'mk, 'nk, nil) hgt
      | ( :: ) :
          ('m, 'k, 'mk, 'nk, 'x) gt * ('m, 'k, 'mk, 'nk, 'xs) hgt
          -> ('m, 'k, 'mk, 'nk, ('x, 'xs) cons) hgt

    (* Unused *)
    (*
    type (_, _, _, _, _, _) hgts =
      | Nil : ('m, 'k, 'mk, 'nk, nil, nil) hgts
      | Cons :
          ('m, 'k, 'mk, 'nk, 'xs, 'ys) hgts
          -> ('m, 'k, 'mk, 'nk, ('x, 'xs) cons, (('m, 'k, 'mk, 'nk, 'x) gt, 'ys) cons) hgts

         let rec hlist_of_hgt :
             type m k mk n xs ys. (m, k, mk, n, xs, ys) hgts -> (m, k, mk, n, xs) hgt -> ys hlist =
          fun hs xs ->
           match (hs, xs) with
           | Nil, [] -> []
           | Cons hs, x :: xs -> x :: hlist_of_hgt hs xs

         let rec hgt_of_hlist :
             type m k mk n xs ys. (m, k, mk, n, xs, ys) hgts -> ys hlist -> (m, k, mk, n, xs) hgt =
          fun hs xs ->
           match (hs, xs) with
           | Nil, [] -> []
           | Cons hs, x :: xs -> x :: hgt_of_hlist hs xs

         let rec tlist_hgts : type m k mk n xs ys. (m, k, mk, n, xs, ys) hgts -> xs tlist -> ys tlist =
          fun hs xs ->
           match (hs, xs) with
           | Nil, Nil -> Nil
           | Cons hs, Cons xs -> Cons (tlist_hgts hs xs)

         type (_, _, _, _, _) has_hgts =
           | Hgts : ('m, 'k, 'mk, 'nk, 'xs, 'xss) hgts -> ('m, 'k, 'mk, 'nk, 'xs) has_hgts

         let rec hgts_of_tlist : type m k mk n xs. xs tlist -> (m, k, mk, n, xs) has_hgts = function
           | Nil -> Hgts Nil
           | Cons xs ->
               let (Hgts xss) = hgts_of_tlist xs in
               Hgts (Cons xss)
    *)

    type (_, _, _) ends =
      | Ends :
          ('mk, 'n, 'bs, 'hs) C.Heter.hgts * ('hs, Endpoints.len) Bwv.Heter.ht
          -> ('mk, 'n, 'bs) ends

    let rec ends : type m k mk n bs. (m, k D.suc, mk D.suc, n D.suc, bs) hgt -> (mk, n, bs) ends =
     fun xss ->
      match xss with
      | [] -> Ends (Nil, [])
      | Branch (es, _) :: xs ->
          let (Ends (hs, ess)) = ends xs in
          Ends (Cons hs, es :: ess)

    let rec mid :
        type m k mk n bs. (m, k D.suc, mk D.suc, n D.suc, bs) hgt -> (m, k, mk, n D.suc, bs) hgt =
      function
      | [] -> []
      | Branch (_, m) :: xs -> m :: mid xs

    let rec leaf : type n nk bs. n D.t -> bs Hlist.tlist -> (n, D.zero, n, nk, bs) hgt =
     fun n bs ->
      match bs with
      | Nil -> []
      | Cons bs -> Leaf n :: leaf n bs

    let rec branch :
        type m k mk n bs hs.
        (mk, n, bs, hs) C.Heter.hgts ->
        (hs, Endpoints.len) Bwv.Heter.ht ->
        (m, k, mk, n D.suc, bs) hgt ->
        (m, k D.suc, mk D.suc, n D.suc, bs) hgt =
     fun hs endss mids ->
      match (hs, endss, mids) with
      | Nil, [], [] -> []
      | Cons hs, ends :: endss, mid :: mids -> Branch (ends, mid) :: branch hs endss mids
  end

  module Infix = C.Infix

  (* Now the generic monadic traversal.  This appears to require *three* helper functions, corresponding to three stages of where we are in the instantiated or uninstantiated dimensions. *)

  module Monadic (M : Monad.Plain) = struct
    open Monad.Ops (M)
    module BwvM = Bwv.Monadic (M)

    type ('n, 'k, 'nk, 'bs, 'cs) pmapperM = {
      map : 'm. ('m, 'n, 'k, 'nk) tface -> ('m, 'bs) C.Heter.hft -> ('m, 'cs) C.Heter.hft M.t;
    }

    let rec gpmapM_ll :
        type k m mk l1 l2 l ml ml1 b bs cs.
        (m, k, mk) D.plus ->
        (m, l, ml) D.plus ->
        (m, l1, ml1) D.plus ->
        (k, l1, l2, l) bwtface ->
        (ml1, l2, ml, (b, bs) Hlist.cons, cs) pmapperM ->
        (m, mk, (b, bs) Hlist.cons) C.Heter.hgt ->
        cs Hlist.tlist ->
        (m, mk, cs) C.Heter.hgt M.t =
     fun mk ml ml1 d g trs cst ->
      match trs with
      | Leaf _ :: _ ->
          let Eq = D.plus_uniq mk (D.zero_plus (dom_bwtface d)) in
          let Eq = D.plus_uniq ml (D.zero_plus (cod_bwtface d)) in
          let Eq = D.plus_uniq ml1 (D.zero_plus (codl_bwtface d)) in
          let* x = g.map (tface_of_bw d) (C.Heter.lab trs) in
          return (C.Heter.leaf x)
      | Branch (_, _) :: _ ->
          let mk' = D.suc_plus mk in
          let (Suc mk'') = mk' in
          let ml' = D.suc_plus ml in
          let ml1' = D.suc_plus ml1 in
          let (Ends (hs, ends)) = C.Heter.ends trs in
          let mid = C.Heter.mid trs in
          let (Hgts newhs) = C.Heter.hgts_of_tlist cst in
          let* newends =
            BwvM.pmapM
              (fun (e :: brs) ->
                let* xs =
                  gpmapM_ll mk'' ml' ml1' (LEnd (e, d)) g (C.Heter.hgt_of_hlist hs brs) cst in
                return (C.Heter.hlist_of_hgt newhs xs))
              (Endpoints.indices :: ends) (C.Heter.tlist_hgts newhs cst) in
          let* newmid = gpmapM_ll mk' ml' ml1' (LMid d) g mid cst in
          return (C.Heter.branch newhs newends newmid)

    let rec gpmapM_l :
        type k m mk l ml b bs cs m1 m2 m2l.
        (m, k, mk) D.plus ->
        (m, l, ml) D.plus ->
        (m1, m2, m) D.plus ->
        (m2, l, m2l) D.plus ->
        (k, D.zero, l, l) bwtface ->
        (m1, m2l, ml, (b, bs) Hlist.cons, cs) pmapperM ->
        (m, mk, (b, bs) Hlist.cons) C.Heter.hgt ->
        cs Hlist.tlist ->
        (m, mk, cs) C.Heter.hgt M.t =
     fun mk ml m12 m2l d g trs cst ->
      match (m12, trs) with
      | Zero, _ ->
          let Eq = D.plus_uniq m2l (D.zero_plus (D.plus_right ml)) in
          gpmapM_ll mk ml Zero d g trs cst
      | Suc m12, Branch (_, _) :: _ ->
          let mk' = D.suc_plus mk in
          let (Suc mk'') = mk' in
          let ml' = D.suc_plus ml in
          let m2l' = D.suc_plus m2l in
          let (Ends (hs, ends)) = C.Heter.ends trs in
          let mid = C.Heter.mid trs in
          let (Hgts newhs) = C.Heter.hgts_of_tlist cst in
          let* newends =
            BwvM.pmapM
              (fun (e :: brs) ->
                let* xs =
                  gpmapM_l mk'' ml' m12 m2l' (bwtface_rend e d) g (C.Heter.hgt_of_hlist hs brs) cst
                in
                return (C.Heter.hlist_of_hgt newhs xs))
              (Endpoints.indices :: ends) (C.Heter.tlist_hgts newhs cst) in
          let* newmid = gpmapM_l mk' ml' m12 m2l' (RMid d) g mid cst in
          return (C.Heter.branch newhs newends newmid)

    let rec gpmapM_r :
        type n k1 k2 l2 kl nk1 nkl nk b bs cs.
        (n, k1, nk1) D.plus ->
        (k1, l2, kl) D.plus ->
        (nk1, k2, nk) D.plus ->
        (nk1, l2, nkl) D.plus ->
        (k2, l2) bwsface ->
        (n, kl, nkl, (b, bs) Hlist.cons, cs) pmapperM ->
        (n, k1, nk1, nk, (b, bs) Hlist.cons) Heter.hgt ->
        cs Hlist.tlist ->
        (n, k1, nk1, nk, cs) Heter.hgt M.t =
     fun nk1 kl nk12 nkl d g trs cst ->
      match (nk1, trs) with
      | Zero, Leaf n :: _ -> return (Heter.leaf n cst)
      | Suc nk1, Branch (_, _) :: _ ->
          let nk12' = D.suc_plus nk12 in
          let (Suc nk12'') = nk12' in
          let (Ends (hs, ends)) = Heter.ends trs in
          let mid = Heter.mid trs in
          let (Hgts newhs) = C.Heter.hgts_of_tlist cst in
          let* newends =
            BwvM.pmapM
              (fun (e :: brs) ->
                let* xs =
                  gpmapM_l nk12'' (D.suc_plus nkl) nk1 (D.suc_plus kl)
                    (REnd (e, d))
                    g (C.Heter.hgt_of_hlist hs brs) cst in
                return (C.Heter.hlist_of_hgt newhs xs))
              (Endpoints.indices :: ends) (C.Heter.tlist_hgts newhs cst) in
          let* newmid = gpmapM_r nk1 (N.suc_plus kl) nk12' (D.suc_plus nkl) (Mid d) g mid cst in
          return (Heter.branch newhs newends newmid)

    let pmapM :
        type n k nk b bs cs.
        (n, k, nk, (b, bs) Hlist.cons, cs) pmapperM ->
        (n, k, nk, nk, (b, bs) Hlist.cons) Heter.hgt ->
        cs Hlist.tlist ->
        (n, k, nk, nk, cs) Heter.hgt M.t =
     fun g trs cst ->
      let (tr :: _) = trs in
      let n = uninst tr in
      let k = inst tr in
      let k0 = D.plus_zero k in
      let n_k = plus tr in
      let nk = D.plus_out n n_k in
      let nk0 = D.plus_zero nk in
      gpmapM_r n_k k0 nk0 nk0 Zero g trs cst

    (* And now the more specialized versions. *)

    type ('n, 'k, 'nk, 'bs, 'c) mmapperM = {
      map : 'm. ('m, 'n, 'k, 'nk) tface -> ('m, 'bs) C.Heter.hft -> ('m, 'c) F.t M.t;
    }

    let mmapM :
        type n k nk b bs c.
        (n, k, nk, (b, bs) Hlist.cons, c) mmapperM ->
        (n, k, nk, nk, (b, bs) Hlist.cons) Heter.hgt ->
        (n, k, nk, c) t M.t =
     fun g xs ->
      let* [ ys ] =
        pmapM
          {
            map =
              (fun fa x ->
                let* y = g.map fa x in
                return (y @: []));
          }
          xs (Cons Nil) in
      return ys

    type ('n, 'k, 'nk, 'bs) miteratorM = {
      it : 'm. ('m, 'n, 'k, 'nk) tface -> ('m, 'bs) C.Heter.hft -> unit M.t;
    }

    let miterM :
        type n k nk b bs.
        (n, k, nk, (b, bs) Hlist.cons) miteratorM ->
        (n, k, nk, nk, (b, bs) Hlist.cons) Heter.hgt ->
        unit M.t =
     fun g xs ->
      let* [] =
        pmapM
          {
            map =
              (fun fa x ->
                let* () = g.it fa x in
                return hnil);
          }
          xs Nil in
      return ()

    (* We also have a monadic builder function *)

    type ('n, 'k, 'nk, 'b) builderM = { build : 'm. ('m, 'n, 'k, 'nk) tface -> ('m, 'b) F.t M.t }

    let rec gbuildM_ll :
        type k m mk l1 l2 l ml ml1 b.
        m D.t ->
        (m, k, mk) D.plus ->
        (m, l, ml) D.plus ->
        (m, l1, ml1) D.plus ->
        (k, l1, l2, l) bwtface ->
        (ml1, l2, ml, b) builderM ->
        (m, mk, b) C.gt M.t =
     fun m mk ml ml1 d g ->
      match m with
      | Nat Zero ->
          let Eq = D.plus_uniq mk (D.zero_plus (dom_bwtface d)) in
          let Eq = D.plus_uniq ml (D.zero_plus (cod_bwtface d)) in
          let Eq = D.plus_uniq ml1 (D.zero_plus (codl_bwtface d)) in
          let* x = g.build (tface_of_bw d) in
          return (C.Leaf x)
      | Nat (Suc m) ->
          let mk' = D.suc_plus mk in
          let (Suc mk'') = mk' in
          let ml' = D.suc_plus ml in
          let ml1' = D.suc_plus ml1 in
          let* ends =
            BwvM.mapM (fun e -> gbuildM_ll (Nat m) mk'' ml' ml1' (LEnd (e, d)) g) Endpoints.indices
          in
          let* mid = gbuildM_ll (Nat m) mk' ml' ml1' (LMid d) g in
          return (C.Branch (ends, mid))

    let rec gbuildM_l :
        type k m mk l ml b m1 m2 m2l.
        m D.t ->
        (m, k, mk) D.plus ->
        (m, l, ml) D.plus ->
        (m1, m2, m) D.plus ->
        (m2, l, m2l) D.plus ->
        (k, D.zero, l, l) bwtface ->
        (m1, m2l, ml, b) builderM ->
        (m, mk, b) C.gt M.t =
     fun m mk ml m12 m2l d g ->
      match m12 with
      | Zero ->
          let Eq = D.plus_uniq m2l (D.zero_plus (D.plus_right ml)) in
          gbuildM_ll m mk ml Zero d g
      | Suc m12 ->
          let (Nat (Suc m)) = m in
          let mk' = D.suc_plus mk in
          let (Suc mk'') = mk' in
          let ml' = D.suc_plus ml in
          let m2l' = D.suc_plus m2l in
          let* ends =
            BwvM.mapM
              (fun e -> gbuildM_l (Nat m) mk'' ml' m12 m2l' (bwtface_rend e d) g)
              Endpoints.indices in
          let* mid = gbuildM_l (Nat m) mk' ml' m12 m2l' (RMid d) g in
          return (C.Branch (ends, mid))

    let rec gbuildM_r :
        type n k1 k2 l2 kl nk1 nkl nk b.
        n D.t ->
        (n, k1, nk1) D.plus ->
        (k1, l2, kl) D.plus ->
        (nk1, k2, nk) D.plus ->
        (nk1, l2, nkl) D.plus ->
        (k2, l2) bwsface ->
        (n, kl, nkl, b) builderM ->
        (n, k1, nk1, nk, b) gt M.t =
     fun n nk1 kl nk12 nkl d g ->
      match nk1 with
      | Zero -> return (Leaf n)
      | Suc nk1 ->
          let nk12' = D.suc_plus nk12 in
          let (Suc nk12'') = nk12' in
          let* ends =
            BwvM.mapM
              (fun e ->
                gbuildM_l (D.plus_out n nk1) nk12'' (D.suc_plus nkl) nk1 (D.suc_plus kl)
                  (REnd (e, d))
                  g)
              Endpoints.indices in
          let* mid = gbuildM_r n nk1 (N.suc_plus kl) nk12' (D.suc_plus nkl) (Mid d) g in
          return (Branch (ends, mid))

    let buildM :
        type n k nk b. n D.t -> (n, k, nk) D.plus -> (n, k, nk, b) builderM -> (n, k, nk, b) t M.t =
     fun n nk g ->
      gbuildM_r n nk
        (D.plus_zero (D.plus_right nk))
        (D.plus_zero (D.plus_out n nk))
        (D.plus_zero (D.plus_out n nk))
        Zero g
  end

  (* Now we deduce the non-monadic versions *)

  module IdM = Monadic (Monad.Identity)

  let pmap :
      type n k nk b bs cs.
      (n, k, nk, (b, bs) Hlist.cons, cs) IdM.pmapperM ->
      (n, k, nk, nk, (b, bs) Hlist.cons) Heter.hgt ->
      cs Hlist.tlist ->
      (n, k, nk, nk, cs) Heter.hgt =
   fun g trs cst -> IdM.pmapM g trs cst

  let mmap :
      type n k nk b bs c.
      (n, k, nk, (b, bs) Hlist.cons, c) IdM.mmapperM ->
      (n, k, nk, nk, (b, bs) Hlist.cons) Heter.hgt ->
      (n, k, nk, c) t =
   fun g xs -> IdM.mmapM g xs

  let miter :
      type n k nk b bs.
      (n, k, nk, (b, bs) Hlist.cons) IdM.miteratorM ->
      (n, k, nk, nk, (b, bs) Hlist.cons) Heter.hgt ->
      unit =
   fun g xs -> IdM.miterM g xs

  let build :
      type n k nk b. n D.t -> (n, k, nk) D.plus -> (n, k, nk, b) IdM.builderM -> (n, k, nk, b) t =
   fun n nk g -> IdM.buildM n nk g

  (* Finally, a one-dimensional tube is just two elements. *)

  let pair : type b. (D.zero, b) F.t -> (D.zero, b) F.t -> (D.zero, D.one, D.one, b) t =
   fun x y -> Branch (Snoc (Snoc (Emp, Leaf x), Leaf y), Leaf D.zero)
end

module TubeOf = struct
  include Tube (FamOf)

  (* We can lift and lower a tube too *)

  let rec glift :
      type m k mk n1 n2 n12 b. (n1, n2, n12) D.plus -> (m, k, mk, n1, b) gt -> (m, k, mk, n12, b) gt
      =
   fun n12 tr ->
    match tr with
    | Leaf m -> Leaf m
    | Branch (ends, mid) ->
        let (Suc n12') = N.suc_plus n12 in
        Branch (Bwv.map (fun t -> CubeOf.lift n12' t) ends, glift n12 mid)

  let rec glower :
      type m k mk n1 n2 n12 l b.
      (mk, l, n1) D.plus -> (n1, n2, n12) D.plus -> (m, k, mk, n12, b) gt -> (m, k, mk, n1, b) gt =
   fun mk n12 tr ->
    match (tr, n12) with
    | Leaf m, _ -> Leaf m
    | _, Zero -> tr
    | Branch (ends, mid), Suc n12' ->
        let mk' = N.suc_plus mk in
        let (Suc mk'') = mk' in
        Branch (Bwv.map (fun t -> CubeOf.lower mk'' (N.suc_plus n12') t) ends, glower mk' n12 mid)

  (* We can fill in the missing pieces of a tube with a cube, yielding a cube. *)

  let rec gplus_gcube : type n m l ml b. (m, l, ml, n, b) gt -> (m, n, b) C.gt -> (ml, n, b) C.gt =
   fun tl tm ->
    match tl with
    | Leaf _ -> tm
    | Branch (ends, mid) -> Branch (ends, gplus_gcube mid tm)

  let plus_cube : type m l ml b. (m, l, ml, b) t -> (m, b) C.t -> (ml, b) C.t =
   fun tl tm ->
    let ml = gplus tl in
    gplus_gcube tl (CubeOf.lift ml tm)

  (* Or we can fill in some of those missing pieces with a tube instead, yielding another tube. *)

  let rec gplus_gtube :
      type n m k mk l kl mkl b.
      (k, l, kl) D.plus -> (mk, l, mkl, n, b) gt -> (m, k, mk, n, b) gt -> (m, kl, mkl, n, b) gt =
   fun kl tl tk ->
    match (kl, tl) with
    | Zero, Leaf _ -> tk
    | Suc kl, Branch (ends, mid) -> Branch (ends, gplus_gtube kl mid tk)

  let plus_tube :
      type m k mk l kl mkl b.
      (k, l, kl) D.plus -> (mk, l, mkl, b) t -> (m, k, mk, b) t -> (m, kl, mkl, b) t =
   fun kl tl tk ->
    let mk_l = gplus tl in
    gplus_gtube kl tl (glift mk_l tk)

  (* We can also pick out a lower-dimensional part around the middle of a tube. *)

  let rec gmiddle :
      type m k mk l kl mkl n b.
      (m, k, mk) D.plus -> (k, l, kl) D.plus -> (m, kl, mkl, n, b) gt -> (m, k, mk, n, b) gt =
   fun mk kl tr ->
    match (kl, tr) with
    | Zero, _ ->
        let Eq = D.plus_uniq mk (gplus tr) in
        tr
    | Suc kl, Branch (_, mid) -> gmiddle mk kl mid

  let middle :
      type m k mk l kl mkl b.
      (m, k, mk) D.plus -> (k, l, kl) D.plus -> (m, kl, mkl, b) t -> (m, k, mk, b) t =
   fun mk kl tr ->
    let mk_l = D.plus_assocl mk kl (plus tr) in
    glower Zero mk_l (gmiddle mk kl tr)
end

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

(* An element of ('a, 'b, 'c) insertion is an insertion of 'c into 'b: a permutation of a = b + c that maintains the relative order of 'b.  *)
type (_, _, _) insertion =
  | Zero : 'a D.t -> ('a, 'a, D.zero) insertion
  | Suc : ('a, 'b, 'c) insertion * 'a D.suc D.index -> ('a D.suc, 'b, 'c D.suc) insertion

let zero_ins : type a. a D.t -> (a, a, D.zero) insertion = fun a -> Zero a

let rec dom_ins : type a b c. (a, b, c) insertion -> a D.t = function
  | Zero a -> a
  | Suc (ins, _) -> N.suc (dom_ins ins)

let rec cod_left_ins : type a b c. (a, b, c) insertion -> b D.t = function
  | Zero a -> a
  | Suc (ins, _) -> cod_left_ins ins

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

let rec perm_of_ins : type a b c. (a, b, c) insertion -> a perm =
  (* fun i -> deg_of_ins i (plus_of_ins i) *)
  function
  | Zero a -> id_perm a
  | Suc (i, e) -> Suc (perm_of_ins i, e)

let deg_of_plus_of_ins : type a b c. (a, b, c) insertion -> b deg_of_plus =
 fun ins -> Of (plus_of_ins ins, perm_of_ins ins)

(* Any degeneracy with a decomposition of its codomain factors as an insertion followed by a whiskered degeneracy. *)

type (_, _, _) insfact = Insfact : ('a, 'b) deg * ('ac, 'a, 'c) insertion -> ('ac, 'b, 'c) insfact

let comp_insfact : type b c ac bc. (ac, b, c) insfact -> (b, c, bc) D.plus -> (ac, bc) deg =
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

(* In particular, any insertion can be composed with a degeneracy to produce a smaller degeneracy and an insertion. *)
type _ insfact_comp = Insfact_comp : ('m, 'n) deg * ('ml, 'm, 'l) insertion -> 'n insfact_comp

let insfact_comp : type n k nk a b. (nk, n, k) insertion -> (a, b) deg -> n insfact_comp =
 fun ins s ->
  let nk = plus_of_ins ins in
  let s' = perm_of_ins ins in
  let (DegExt (_, nk_d, s's)) = comp_deg_extending s' s in
  let (Plus kd) = D.plus (D.plus_right nk_d) in
  let n_kd = D.plus_assocr nk kd nk_d in
  let (Insfact (fa, new_ins)) = insfact s's n_kd in
  Insfact_comp (fa, new_ins)

(* ********** Special generators ********** *)

type one = D.one

let one = D.one
let refl : (one, D.zero) deg = Zero D.one
let zero_sface_one : (D.zero, one) sface = End (Zero, Pop Top)
let one_sface_one : (D.zero, one) sface = End (Zero, Top)

type two = D.two

let sym : (two, two) deg = Suc (Suc (Zero D.zero, Top), Pop Top)

type _ is_suc = Is_suc : 'n D.t * ('n, one, 'm) D.plus -> 'm is_suc

let suc_pos : type n. n D.pos -> n is_suc = fun (Pos n) -> Is_suc (n, Suc Zero)

let deg_of_name : string -> any_deg option = function
  | "refl" -> Some (Any refl)
  | "Id" -> Some (Any refl)
  | "sym" -> Some (Any sym)
  | _ -> None

let name_of_deg : type a b. (a, b) deg -> string option = function
  | Zero (Nat (Suc Zero)) -> Some "refl"
  | Suc (Suc (Zero (Nat Zero), Top), Pop Top) -> Some "sym"
  | _ -> None
