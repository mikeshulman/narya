open Util
open Deg

(* ********** Permutations ********** *)

type ('m, 'n) perm =
  | Zero : (D.zero, D.zero) perm
  | Suc : ('a, 'b) perm * ('a, 'c) D.insert -> ('c, 'b D.suc) perm

let rec dom_perm : type m n. (m, n) perm -> m D.t = function
  | Zero -> D.zero
  | Suc (p, i) -> D.insert_out (dom_perm p) i

let rec cod_perm : type a b. (a, b) perm -> b D.t = function
  | Zero -> D.zero
  | Suc (p, _) -> D.suc (cod_perm p)

let rec id_perm : type a. a D.t -> (a, a) perm = function
  | Nat Zero -> Zero
  | Nat (Suc a) -> Suc (id_perm (Nat a), Now)

let rec is_id_perm : type a b. (a, b) perm -> (a, b) Eq.compare = function
  | Zero -> Eq
  | Suc (p, i) -> (
      match is_id_perm p with
      | Neq -> Neq
      | Eq -> (
          match i with
          | Now -> Eq
          | Later _ -> Neq))

(* Every permutation is a degeneracy. *)
let rec deg_of_perm : type m n. (m, n) perm -> (m, n) deg = function
  | Zero -> Zero D.zero
  | Suc (p, i) -> Suc (deg_of_perm p, i)

(* Conversely, a degeneracy *might* be a permutation. *)
let rec perm_of_deg : type m n. (m, n) deg -> (m, n) perm option = function
  | Zero (Nat Zero) -> Some Zero
  | Zero _ -> None
  | Suc (p, i) -> (
      match perm_of_deg p with
      | Some p -> Some (Suc (p, i))
      | None -> None)

(* Residuals of permutations are just like those for degeneracies *)

type (_, _, _) perm_residual =
  | Residual : ('m, 'n) perm * ('m, 'msuc) D.insert -> ('msuc, 'n, 'n D.suc) perm_residual

let rec perm_residual : type m n npred.
    (m, n) perm -> (npred, n) D.insert -> (m, npred, n) perm_residual =
 fun s k ->
  match (k, s) with
  | Now, Suc (s, i) -> Residual (s, i)
  | Later k, Suc (s, i) ->
      let (Residual (s, j)) = perm_residual s k in
      let (Swap_inserts (i, j)) = D.swap_inserts i j in
      Residual (Suc (s, j), i)

let rec comp_perm : type a b c. (b, c) perm -> (a, b) perm -> (a, c) perm =
 fun a b ->
  match a with
  | Zero ->
      let Zero = b in
      Zero
  | Suc (s, k) ->
      let (Residual (t, i)) = perm_residual b k in
      Suc (comp_perm s t, i)

let rec perm_plus : type m n k mk nk.
    (m, n) perm -> (n, k, nk) D.plus -> (m, k, mk) D.plus -> (mk, nk) perm =
 fun s nk mk ->
  match (nk, mk) with
  | Zero, Zero -> s
  | Suc nk, Suc mk -> Suc (perm_plus s nk mk, Now)

let rec perm_plus_perm : type m n mn k l kl.
    (k, m) perm -> (m, n, mn) D.plus -> (k, l, kl) D.plus -> (l, n) perm -> (kl, mn) perm =
 fun skm mn kl sln ->
  match sln with
  | Zero ->
      let Zero, Zero = (mn, kl) in
      skm
  | Suc (sln', i) ->
      let (Suc mn') = mn in
      let (Plus kl') = D.plus (dom_perm sln') in
      Suc (perm_plus_perm skm mn' kl' sln', D.plus_insert kl' kl i)

let rec cosuc : type m n nsuc. (m, n) perm -> (n, nsuc) D.insert -> (m D.suc, nsuc) perm =
 fun p -> function
  | Now -> Suc (p, Now)
  | Later i ->
      let Suc (p, j), _ = (p, i) in
      Suc (cosuc p i, Later j)

let rec perm_inv : type m n. (m, n) perm -> (n, m) perm = function
  | Zero -> Zero
  | Suc (p, i) -> cosuc (perm_inv p) i

(* A degeneracy with codomain a sum of dimensions might decompose as a sum of a degeneracy and a permutation. *)
type (_, _, _) deg_perm_of_plus =
  | Deg_perm_of_plus :
      ('m, 'l, 'ml) D.plus * ('m, 'n) deg * ('l, 'k) perm
      -> ('ml, 'n, 'k) deg_perm_of_plus
  | None_deg_perm_of_plus : ('mk, 'n, 'k) deg_perm_of_plus

let rec deg_perm_of_plus : type mk n k nk.
    (n, k, nk) D.plus -> (mk, nk) deg -> (mk, n, k) deg_perm_of_plus =
 fun nk s ->
  match nk with
  | Zero -> Deg_perm_of_plus (Zero, s, id_perm D.zero)
  | Suc nk -> (
      let (Suc (s, i)) = s in
      match deg_perm_of_plus nk s with
      | None_deg_perm_of_plus -> None_deg_perm_of_plus
      | Deg_perm_of_plus (mk, s, p) -> (
          match D.insert_into_plus mk i with
          | Left _ -> None_deg_perm_of_plus
          | Right (j, mk') -> Deg_perm_of_plus (mk', s, Suc (p, j))))

(* A permutation with specified domain only *)
type _ perm_to = Perm_to : ('a, 'b) perm -> 'a perm_to
