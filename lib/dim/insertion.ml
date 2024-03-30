open Util
open Deg

(* An element of ('a, 'b, 'c) insertion is an insertion of 'c into 'b: a permutation of a = b + c that maintains the relative order of 'b.  *)
type (_, _, _) insertion =
  | Zero : 'a D.t -> ('a, 'a, D.zero) insertion
  | Suc : ('a, 'b, 'c) insertion * 'a D.suc D.index -> ('a D.suc, 'b, 'c D.suc) insertion

let ins_zero : type a. a D.t -> (a, a, D.zero) insertion = fun a -> Zero a

let rec zero_ins : type a. a D.t -> (a, D.zero, a) insertion =
 fun a ->
  match a with
  | Nat Zero -> Zero a
  | Nat (Suc a) ->
      let ins = zero_ins (Nat a) in
      Suc (ins, Top)

type (_, _) id_ins = Id_ins : ('ab, 'a, 'b) insertion -> ('a, 'b) id_ins

let rec id_ins : type a b. a D.t -> b D.t -> (a, b) id_ins =
 fun a b ->
  match b with
  | Nat Zero -> Id_ins (Zero a)
  | Nat (Suc b) ->
      let (Id_ins ins) = id_ins a (Nat b) in
      Id_ins (Suc (ins, Top))

let rec dom_ins : type a b c. (a, b, c) insertion -> a D.t = function
  | Zero a -> a
  | Suc (ins, _) -> N.suc (dom_ins ins)

let rec cod_left_ins : type a b c. (a, b, c) insertion -> b D.t = function
  | Zero a -> a
  | Suc (ins, _) -> cod_left_ins ins

let rec cod_right_ins : type a b c. (a, b, c) insertion -> c D.t = function
  | Zero _ -> D.zero
  | Suc (ins, _) -> D.suc (cod_right_ins ins)

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

let is_id_ins : type a b c. (a, b, c) insertion -> unit option = fun s -> is_id_perm (perm_of_ins s)

let deg_of_plus_of_ins : type a b c. (a, b, c) insertion -> b deg_of_plus =
 fun ins -> Of (plus_of_ins ins, perm_of_ins ins)

(* We can extend an insertion by the identity on the left *)

let rec plus_ins :
    type a b c ab bc abc.
    a D.t ->
    (a, b, ab) D.plus ->
    (a, bc, abc) D.plus ->
    (bc, b, c) insertion ->
    (abc, ab, c) insertion =
 fun a ab abc ins ->
  match ins with
  | Zero _ ->
      let Eq = D.plus_uniq ab abc in
      Zero (D.plus_out a ab)
  | Suc (ins, i) ->
      let (Suc abc') = abc in
      Suc (plus_ins a ab abc' ins, D.plus_index abc i)

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
type (_, _, _) insfact_comp =
  | Insfact_comp :
      ('m, 'n) deg * ('ml, 'm, 'l) insertion * ('k, 'j, 'l) D.plus * ('a, 'i, 'ml) D.plus
      -> ('n, 'k, 'a) insfact_comp

let insfact_comp : type n k nk a b. (nk, n, k) insertion -> (a, b) deg -> (n, k, a) insfact_comp =
 fun ins s ->
  let nk = plus_of_ins ins in
  let s' = perm_of_ins ins in
  let (DegExt (ai, nk_d, s's)) = comp_deg_extending s' s in
  let (Plus kd) = D.plus (D.plus_right nk_d) in
  let n_kd = D.plus_assocr nk kd nk_d in
  let (Insfact (fa, new_ins)) = insfact s's n_kd in
  Insfact_comp (fa, new_ins, kd, ai)
