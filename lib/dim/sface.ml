open Util

(* ********** Strict faces ********** *)

(* A strict face is an order-preserving partial map that is surjective and with an endpoint index assigned to each element not mapping to the codomain. *)

type (_, _) sface =
  | Zero : (D.zero, D.zero) sface
  | End : ('m, 'n) sface * 'l Endpoints.t -> ('m, 'n D.suc) sface
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

let rec is_id_sface : type m n. (m, n) sface -> (m, n) Eq.t option = function
  | Zero -> Some Eq
  | End _ -> None
  | Mid f -> (
      match is_id_sface f with
      | Some Eq -> Some Eq
      | None -> None)

let rec comp_sface : type m n k. (n, k) sface -> (m, n) sface -> (m, k) sface =
 fun a b ->
  match (a, b) with
  | Zero, Zero -> Zero
  | End (a', e), _ -> End (comp_sface a' b, e)
  | Mid a', End (b', e) -> End (comp_sface a' b', e)
  | Mid a', Mid b' -> Mid (comp_sface a' b')

(* Zero has only the trivial strict face *)
let sface_zero : type n. (n, D.zero) sface -> (n, D.zero) Eq.t = function
  | Zero -> Eq

type _ sface_of = SFace_of : ('m, 'n) sface -> 'n sface_of

(* Insert an element in the codomain and domain of a strict face, with the same numerical De Bruijn index. *)

type (_, _) insert_sface =
  | Insert_sface : ('m, 'msuc) D.insert * ('msuc, 'nsuc) sface -> ('m, 'nsuc) insert_sface

let rec insert_sface : type m n nsuc. (m, n) sface -> (n, nsuc) D.insert -> (m, nsuc) insert_sface =
 fun f i ->
  match i with
  | Now -> Insert_sface (Now, Mid f)
  | Later i -> (
      match f with
      | End (f, e) ->
          let (Insert_sface (i, f)) = insert_sface f i in
          Insert_sface (i, End (f, e))
      | Mid f ->
          let (Insert_sface (i, f)) = insert_sface f i in
          Insert_sface (Later i, Mid f))

(* Concatenate two strict faces left-to-right. *)
let rec sface_plus_sface : type m n mn k p kp.
    (k, m) sface -> (m, n, mn) D.plus -> (k, p, kp) D.plus -> (p, n) sface -> (kp, mn) sface =
 fun fkm mn kp fpn ->
  match (fpn, mn, kp) with
  | Zero, Zero, Zero -> fkm
  | End (fpn, e), Suc mn, kp -> End (sface_plus_sface fkm mn kp fpn, e)
  | Mid fpn, Suc mn, Suc kp -> Mid (sface_plus_sface fkm mn kp fpn)

(* In particular, we can extend by identities on the right or left. *)

let sface_plus : type m n mn k kn.
    (k, m) sface -> (m, n, mn) D.plus -> (k, n, kn) D.plus -> (kn, mn) sface =
 fun f mn kn -> sface_plus_sface f mn kn (id_sface (Nat mn))

let plus_sface : type m n nm k nk.
    n D.t -> (n, m, nm) D.plus -> (n, k, nk) D.plus -> (k, m) sface -> (nk, nm) sface =
 fun n nm nk f -> sface_plus_sface (id_sface n) nm nk f

(* Conversely, any strict face of a sum decomposes as a sum. *)

type (_, _, _) sface_of_plus =
  | SFace_of_plus :
      ('m, 'l, 'ml) D.plus * ('m, 'n) sface * ('l, 'k) sface
      -> ('ml, 'n, 'k) sface_of_plus

let rec sface_of_plus : type ml n k nk.
    (n, k, nk) D.plus -> (ml, nk) sface -> (ml, n, k) sface_of_plus =
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

let rec string_of_sface : type n k. (n, k) sface -> string =
 fun fa ->
  match fa with
  | Zero -> ""
  | End (fa, e) -> Endpoints.to_string (Some e) ^ string_of_sface fa
  | Mid fa -> Endpoints.to_string None ^ string_of_sface fa

let sface_of_string : string -> any_sface option =
 fun str ->
  let (Wrap l) = Endpoints.wrapped () in
  String.fold_right
    (fun x fa ->
      match (fa, Endpoints.of_char l x) with
      | None, _ | _, Error _ -> None
      | Some (Any_sface fa), Ok (Some e) -> Some (Any_sface (End (fa, e)))
      | Some (Any_sface fa), Ok None -> Some (Any_sface (Mid fa)))
    str (Some (Any_sface Zero))
