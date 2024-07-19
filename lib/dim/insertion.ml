open Bwd
open Util
open Sface
open Tface
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

let rec equal_ins :
    type a1 b1 c1 a2 b2 c2. (a1, b1, c1) insertion -> (a2, b2, c2) insertion -> unit option =
 fun i1 i2 ->
  match (i1, i2) with
  | Zero a1, Zero a2 -> (
      match D.compare a1 a2 with
      | Eq -> Some ()
      | Neq -> None)
  | Suc (i1, x1), Suc (i2, x2) ->
      let open Monad.Ops (Monad.Maybe) in
      let* () = N.insert_equiv x1 x2 in
      equal_ins i1 i2
  | _ -> None

let rec plus_ins :
    type a b c d ab ac.
    a D.t -> (a, b, ab) D.plus -> (a, c, ac) D.plus -> (b, c, d) insertion -> (ab, ac, d) insertion
    =
 fun a ab ac ins ->
  match ins with
  | Zero _ ->
      let Eq = D.plus_uniq ab ac in
      Zero (D.plus_out a ab)
  | Suc (ins, i) ->
      let (Plus ab') = D.plus (D.insert_in (D.plus_right ab) i) in
      Suc (plus_ins a ab' ac ins, D.plus_insert ab' ab i)

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

(* A degeneracy of the left codomain of an insertion can be extended to a degeneracy of its domain, completing a commutative square with a larger insertion. *)

type (_, _, _) deg_lift_ins =
  | Deg_lift_ins : ('mk, 'm, 'k) insertion * ('mk, 'nk) deg -> ('m, 'k, 'nk) deg_lift_ins

let rec deg_lift_ins : type n k nk m. (m, n) deg -> (nk, n, k) insertion -> (m, k, nk) deg_lift_ins
    =
 fun s0 ins0 ->
  match ins0 with
  | Zero _ -> Deg_lift_ins (Zero (dom_deg s0), s0)
  | Suc (ins1, i1) ->
      let (Deg_lift_ins (ins2, s1)) = deg_lift_ins s0 ins1 in
      let (Insert_deg (j2, s2)) = insert_deg s1 i1 in
      Deg_lift_ins (Suc (ins2, j2), s2)

(* And similarly for a strict face of the left codomain. *)

type (_, _, _) sface_lift_ins =
  | Sface_lift_ins : ('mk, 'm, 'k) insertion * ('mk, 'nk) sface -> ('m, 'k, 'nk) sface_lift_ins

let rec sface_lift_ins :
    type n k nk m. (m, n) sface -> (nk, n, k) insertion -> (m, k, nk) sface_lift_ins =
 fun fa0 ins0 ->
  match ins0 with
  | Zero _ -> Sface_lift_ins (Zero (dom_sface fa0), fa0)
  | Suc (ins1, i1) ->
      let (Sface_lift_ins (ins2, fa1)) = sface_lift_ins fa0 ins1 in
      let (Insert_sface (j2, fa2)) = insert_sface fa1 i1 in
      Sface_lift_ins (Suc (ins2, j2), fa2)

(* Or a proper face *)

type (_, _, _) pface_lift_ins =
  | Pface_lift_ins : ('mk, 'm, 'k) insertion * ('mk, 'nk) pface -> ('m, 'k, 'nk) pface_lift_ins

let rec pface_lift_ins :
    type n k nk m. (m, n) pface -> (nk, n, k) insertion -> (m, k, nk) pface_lift_ins =
 fun fa0 ins0 ->
  match ins0 with
  | Zero _ -> Pface_lift_ins (Zero (dom_tface fa0), fa0)
  | Suc (ins1, i1) ->
      let (Pface_lift_ins (ins2, fa1)) = pface_lift_ins fa0 ins1 in
      let (Insert_pface (j2, fa2)) = insert_pface fa1 i1 in
      Pface_lift_ins (Suc (ins2, j2), fa2)

(* Construct an insertion from a domain and a list of numbers. *)
type _ ins_of = Ins_of : ('ab, 'a, 'b) insertion -> 'ab ins_of

let rec ins_of_ints : type ab. ab D.t -> int Bwd.t -> ab ins_of option =
 fun ab ns ->
  match ns with
  | Emp -> Some (Ins_of (Zero ab))
  | Snoc (ns, n) -> (
      match (ab, N.index_of_int ab (N.to_int ab - n)) with
      | Nat (Suc ab), Some ix -> (
          let ab = N.Nat ab in
          let ns =
            Bwd.map
              (fun i ->
                if i < n then i else if i > n then i - 1 else raise (Invalid_argument "ins_of_ints"))
              ns in
          match ins_of_ints ab ns with
          | Some (Ins_of ins) -> Some (Ins_of (Suc (ins, N.insert_of_index ix)))
          | None -> None)
      | Nat Zero, Some _ -> .
      | _, None -> None)

(* Conversely, display an insertion as a list of numbers. *)
let rec ints_of_ins : type ab a b. (ab, a, b) insertion -> int Bwd.t = function
  | Zero _ -> Emp
  | Suc (ins, ix) ->
      let x = N.to_int (dom_ins ins) + 1 - N.int_of_index (N.index_of_insert ix) in
      Snoc (Bwd.map (fun i -> if i >= x then i + 1 else i) (ints_of_ins ins), x)

let string_of_ins_ints : int Bwd.t -> string =
 fun ints ->
  let strs = Bwd_extra.to_list_map string_of_int ints in
  if List.is_empty strs then ""
  else if List.fold_right (fun s m -> max (String.length s) m) strs 0 > 1 then
    ".." ^ String.concat "." strs
  else "." ^ String.concat "" strs

let string_of_ins : type ab a b. (ab, a, b) insertion -> string =
 fun ins -> string_of_ins_ints (ints_of_ins ins)

type any_ins = Any_ins : ('a, 'b, 'c) insertion -> any_ins

(* List all the insertions with a given total dimension. *)
let rec all_ins_of : type ab. ab D.t -> ab ins_of Seq.t =
 fun ab ->
  let open Monad.Ops (Monad.Seq) in
  Seq.cons (Ins_of (Zero ab))
    (let* (Into ix) = D.all_inserts ab in
     let* (Ins_of ins) = all_ins_of (D.insert_in ab ix) in
     return (Ins_of (Suc (ins, ix))))
