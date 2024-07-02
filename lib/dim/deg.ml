open Util
open Arith

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
      let (Suc mk') = D.plus_suc mk in
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
let rec is_id_deg : type m n. (m, n) deg -> (m, n) Eq.t option = function
  | Zero n -> (
      match N.compare n D.zero with
      | Eq -> Some Eq
      | Neq -> None)
  | Suc (p, Top) -> (
      match is_id_deg p with
      | Some Eq -> Some Eq
      | None -> None)
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
  match N.trichotomy (cod_deg s1) (cod_deg s2) with
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

let is_id_perm : type n. n perm -> unit option =
 fun p ->
  match is_id_deg p with
  | Some _ -> Some ()
  | None -> None

(* The inverse of a permutation *)

let rec coinsert : type m. m perm -> m D.suc D.index -> m D.suc perm =
 fun p -> function
  | Top -> Suc (p, Top)
  | Pop i ->
      let Suc (p, j), _ = (p, i) in
      Suc (coinsert p i, Pop j)

let rec perm_inv : type m. m perm -> m perm = function
  | Zero z -> Zero z
  | Suc (p, i) -> coinsert (perm_inv p) i

(* A degeneracy with codomain a sum of dimensions might decompose as a sum of a degeneracy and a permutation. *)
type (_, _, _) deg_perm_of_plus =
  | Deg_perm_of_plus :
      ('m, 'k, 'mk) D.plus * ('m, 'n) deg * 'k perm
      -> ('mk, 'n, 'k) deg_perm_of_plus
  | None_deg_perm_of_plus : ('mk, 'n, 'k) deg_perm_of_plus

let rec deg_perm_of_plus :
    type mk n k nk. (n, k, nk) D.plus -> (mk, nk) deg -> (mk, n, k) deg_perm_of_plus =
 fun nk s ->
  match nk with
  | Zero -> Deg_perm_of_plus (Zero, s, Zero N.zero)
  | Suc nk -> (
      let (Suc (s, i)) = s in
      match deg_perm_of_plus nk s with
      | None_deg_perm_of_plus -> None_deg_perm_of_plus
      | Deg_perm_of_plus (mk, s, p) -> (
          match N.index_in_plus (Suc mk) i with
          | Left _ -> None_deg_perm_of_plus
          | Right j -> Deg_perm_of_plus (Suc mk, s, Suc (p, j))))

(* ********** Variable degeneracies ********** *)

type _ deg_of = Of : ('m, 'n) deg -> 'n deg_of
type _ deg_of_plus = Of : ('n, 'k, 'nk) D.plus * ('m, 'nk) deg -> 'n deg_of_plus

let comp_deg_of_plus : type m n. (m, n) deg -> m deg_of_plus -> n deg_of_plus =
 fun s2 (Of (mk, s1)) ->
  let (Plus nk) = D.plus (Nat mk) in
  let s2k = deg_plus s2 nk mk in
  Of (nk, comp_deg s2k s1)

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

(* ******************** Printing and parsing ******************** *)

let rec strings_of_deg : type a b. (a, b) deg -> (string, a) Bwv.t = function
  | Zero a -> Bwv.init a (fun _ -> Endpoints.refl_string ())
  | Suc (s, k) -> Bwv.insert k (string_of_int (D.to_int (cod_deg s) + 1)) (strings_of_deg s)

let string_of_deg : type a b. (a, b) deg -> string =
 fun s ->
  String.concat (if D.to_int (cod_deg s) > 9 then "-" else "") (Bwv.to_list (strings_of_deg s))

type _ deg_to = To : ('m, 'n) deg -> 'm deg_to

(* A degeneracy is represented by a list of positive integers and strings.  The integers give a permutation of the codomain, and the strings are 'r' characters indicating where degeneracies are inserted in the domain.  Thus the length of the list (here a Bwv) is equal to the length of the domain.  The integer supplied is the length of the codomain. *)
let rec deg_of_strings : type n. ([ `Int of int | `Str of string ], n) Bwv.t -> int -> n deg_to option =
 fun xs i ->
  let open Monad.Ops (Monad.Maybe) in
  (* If the codomain has length 0, then all the remaining generating dimensions must be degeneracies, and the degeneracy is a Zero. *)
  if i <= 0 then
    if Bwv.fold_right (fun x b -> x = `Str (Endpoints.refl_string ()) && b) xs true then
      Some (To (Zero (Bwv.length xs)))
    else None
  else
    (* Otherwise, there must be at least one remaining generating dimension. *)
    match xs with
    | Emp -> None
    | Snoc _ ->
        (* We find where the last generating dimension of the *codomain* occurs and remove it, remembering its index to supply to Suc. *)
        let* xs, j = Bwv.find_remove (`Int i) xs in
        (* Then what's left we can recurse into with a smaller expected codomain. *)
        let* (To s) = deg_of_strings xs (i - 1) in
        return (To (Suc (s, j)))

(* We could write the next function monadically to include the errors as options, but it's simpler to just raise a local exception. *)
exception Invalid_direction_name of string

(* A list of positive integers and strings is represented by a single string that either concatenates them, if the integers are all <10 and the strings are all 1-character, or concatenates them with '-' between otherwise.  There is no confusion because if a degeneracy consists of a single number, that number can only be 1, so a multi-digit string must be concatenated.  *)
let deg_of_string : string -> any_deg option =
 fun str ->
  (* First we break our string into a list, as in the input to deg_of_strings, and simultaneously compute its maximum. *)
  let strs =
    if String.contains str '-' then String.split_on_char '-' str
    else String.fold_right (fun c s -> String.make 1 c :: s) str [] in
  let parsestr x m =
    match int_of_string_opt x with
    | Some i -> (`Int i, max i m)
    | None -> if x = Endpoints.refl_string () then (`Str x, m) else raise (Invalid_direction_name x)
  in
  try
    let Wrap strs, i =
      List.fold_left
        (fun (Bwv.Wrap l, i) c ->
          let x, i = parsestr c i in
          (Wrap (Snoc (l, x)), i))
        (Wrap Emp, 0) strs in
    (* Finally we pass off to deg_of_strings. *)
    match deg_of_strings strs i with
    | None -> None
    | Some (To s) -> Some (Any s)
  with Invalid_direction_name _ -> None

(* A degeneracy is "locking" if it has degenerate external directions. *)
let rec locking : type a b. (a, b) deg -> bool = function
  | Suc (s, _) -> locking s
  | Zero x -> (
      match N.compare x D.zero with
      | Eq -> false
      | Neq -> true && not (Endpoints.internal ()))
