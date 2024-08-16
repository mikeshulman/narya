open Util
open Deg
open Perm

(* An element of ('a, 'b, 'c) insertion is an insertion of 'c into 'b: a permutation from a to b+c that maintains the relative order of 'b.  *)
(* TODO: Should an insertion be parametrized by b+c as well? *)
type (_, _, _) insertion =
  | Zero : 'a D.t -> ('a, 'a, D.zero) insertion
  | Suc : ('a, 'b, 'c) insertion * ('a, 'asuc) D.insert -> ('asuc, 'b, 'c D.suc) insertion

let ins_zero : type a. a D.t -> (a, a, D.zero) insertion = fun a -> Zero a

let rec zero_ins : type a. a D.t -> (a, D.zero, a) insertion =
 fun a ->
  match a with
  | Nat Zero -> Zero a
  | Nat (Suc a) ->
      let ins = zero_ins (Nat a) in
      Suc (ins, Now)

let rec id_ins : type a b ab. a D.t -> (a, b, ab) D.plus -> (ab, a, b) insertion =
 fun a b ->
  match b with
  | Zero -> Zero a
  | Suc b ->
      let ins = id_ins a b in
      Suc (ins, Now)

let rec dom_ins : type a b c. (a, b, c) insertion -> a D.t = function
  | Zero a -> a
  | Suc (ins, i) -> N.insert_out (dom_ins ins) i

let rec cod_left_ins : type a b c. (a, b, c) insertion -> b D.t = function
  | Zero a -> a
  | Suc (ins, _) -> cod_left_ins ins

let rec cod_right_ins : type a b c. (a, b, c) insertion -> c D.t = function
  | Zero _ -> D.zero
  | Suc (ins, _) -> D.suc (cod_right_ins ins)

(* An insertion induces a degeneracy, which is in fact a permutation. *)
let rec deg_of_ins_plus : type a b c bc. (a, b, c) insertion -> (b, c, bc) D.plus -> (a, bc) deg =
 fun i bc ->
  match (i, bc) with
  | Zero a, Zero -> id_deg a
  | Suc (i, e), Suc bc -> Suc (deg_of_ins_plus i bc, e)

let deg_of_ins : type a b c. (a, b, c) insertion -> a deg_to =
 fun ins ->
  let (Plus bc) = D.plus (cod_right_ins ins) in
  To (deg_of_ins_plus ins bc)

let rec perm_of_ins_plus : type a b c bc. (a, b, c) insertion -> (b, c, bc) D.plus -> (a, bc) perm =
 fun i bc ->
  match (i, bc) with
  | Zero a, Zero -> id_perm a
  | Suc (i, e), Suc bc -> Suc (perm_of_ins_plus i bc, e)

let perm_of_ins : type a b c. (a, b, c) insertion -> a perm_to =
 fun ins ->
  let (Plus bc) = D.plus (cod_right_ins ins) in
  Perm_to (perm_of_ins_plus ins bc)

let rec is_id_ins : type a b c. (a, b, c) insertion -> (b, c, a) D.plus option = function
  | Zero _ -> Some Zero
  | Suc (ins, Now) -> (
      match is_id_ins ins with
      | Some bc -> Some (Suc bc)
      | None -> None)
  | Suc (_, Later _) -> None

let deg_of_plus_of_ins : type a b c. (a, b, c) insertion -> b deg_of_plus =
 fun ins ->
  let (Plus bc) = D.plus (cod_right_ins ins) in
  Of (bc, deg_of_ins_plus ins bc)

(* Any degeneracy with a decomposition of its codomain factors as an insertion followed by a whiskered degeneracy. *)

type (_, _, _) insfact = Insfact : ('a, 'b) deg * ('ac, 'a, 'c) insertion -> ('ac, 'b, 'c) insfact

let rec insfact : type ac b c bc. (ac, bc) deg -> (b, c, bc) D.plus -> (ac, b, c) insfact =
 fun s bc ->
  match bc with
  | Zero -> Insfact (s, Zero (dom_deg s))
  | Suc bc ->
      let (Suc (s, e)) = s in
      let (Insfact (s, i)) = insfact s bc in
      Insfact (s, Suc (i, e))

(* In particular, any insertion can be composed with a degeneracy to produce a smaller degeneracy and an insertion. *)
type (_, _, _) insfact_comp =
  | Insfact_comp :
      ('m, 'n) deg * ('ml, 'm, 'l) insertion * ('k, 'j, 'l) D.plus * ('a, 'i, 'ml) D.plus
      -> ('n, 'k, 'a) insfact_comp

let insfact_comp : type n k nk a b. (nk, n, k) insertion -> (a, b) deg -> (n, k, a) insfact_comp =
 fun ins s ->
  let (Plus nk) = D.plus (cod_right_ins ins) in
  let s' = deg_of_ins_plus ins nk in
  let (DegExt (ai, nk_d, s's)) = comp_deg_extending s' s in
  let (Plus kd) = D.plus (D.plus_right nk_d) in
  let n_kd = D.plus_assocr nk kd nk_d in
  let (Insfact (fa, new_ins)) = insfact s's n_kd in
  Insfact_comp (fa, new_ins, kd, ai)
