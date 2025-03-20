open Util
open Deg
open Perm

(* A shuffle is a permutation of a sum that preserves the relative order of *both* inputs.  Specifically, an ('a, 'b, 'c) shuffle shuffles the two inputs 'a and 'b together to produce 'c. *)

type (_, _, _) shuffle =
  | Zero : (D.zero, D.zero, D.zero) shuffle
  | Left : ('a, 'b, 'ab) shuffle -> ('a D.suc, 'b, 'ab D.suc) shuffle
  | Right : ('a, 'b, 'ab) shuffle -> ('a, 'b D.suc, 'ab D.suc) shuffle

let rec plus_of_shuffle : type a b c. (a, b, c) shuffle -> (a, b, c) D.plus = function
  | Zero -> Zero
  | Left s -> D.suc_plus_eq_suc (plus_of_shuffle s)
  | Right s -> Suc (plus_of_shuffle s)

let rec deg_of_shuffle : type a b c ab. (a, b, c) shuffle -> (a, b, ab) D.plus -> (c, ab) deg =
 fun s ab ->
  match s with
  | Zero ->
      let Zero = ab in
      Zero D.zero
  | Left s ->
      let (Suc ab) = D.plus_suc ab in
      Suc (deg_of_shuffle s ab, Now)
  | Right s ->
      let (Suc ab) = ab in
      Suc (deg_of_shuffle s ab, Now)

let rec perm_of_shuffle : type a b c ab. (a, b, c) shuffle -> (a, b, ab) D.plus -> (c, ab) perm =
 fun s ab ->
  match s with
  | Zero ->
      let Zero = ab in
      Zero
  | Left s ->
      let (Suc ab) = D.plus_suc ab in
      Suc (perm_of_shuffle s ab, Now)
  | Right s ->
      let (Suc ab) = ab in
      Suc (perm_of_shuffle s ab, Now)

let rec left_shuffle : type a b c. (a, b, c) shuffle -> a D.t = function
  | Zero -> D.zero
  | Left s -> D.suc (left_shuffle s)
  | Right s -> left_shuffle s

let rec right_shuffle : type a b c. (a, b, c) shuffle -> b D.t = function
  | Zero -> D.zero
  | Left s -> right_shuffle s
  | Right s -> D.suc (right_shuffle s)

let rec out_shuffle : type a b c. (a, b, c) shuffle -> c D.t = function
  | Zero -> D.zero
  | Left s -> D.suc (out_shuffle s)
  | Right s -> D.suc (out_shuffle s)

let rec shuffle_zero : type a. a D.t -> (a, D.zero, a) shuffle = function
  | Nat Zero -> Zero
  | Nat (Suc a) -> Left (shuffle_zero (Nat a))

let rec zero_shuffle : type a. a D.t -> (D.zero, a, a) shuffle = function
  | Nat Zero -> Zero
  | Nat (Suc a) -> Right (zero_shuffle (Nat a))

let rec eq_of_zero_shuffle : type a b. (D.zero, a, b) shuffle -> (a, b) Eq.t = function
  | Zero -> Eq
  | Right s ->
      let Eq = eq_of_zero_shuffle s in
      Eq

let rec eq_of_shuffle_zero : type a b. (a, D.zero, b) shuffle -> (a, b) Eq.t = function
  | Zero -> Eq
  | Left s ->
      let Eq = eq_of_shuffle_zero s in
      Eq

type (_, _, _, _) comp_shuffle_right =
  | Comp_shuffle_right :
      ('a, 'b, 'ab) shuffle * ('ab, 'c, 'abc) shuffle
      -> ('a, 'b, 'c, 'abc) comp_shuffle_right

let rec comp_shuffle_right : type a b c bc abc.
    (b, c, bc) shuffle -> (a, bc, abc) shuffle -> (a, b, c, abc) comp_shuffle_right =
 fun bc abc ->
  match (bc, abc) with
  | Zero, _ ->
      let Eq = eq_of_shuffle_zero abc in
      Comp_shuffle_right (shuffle_zero (left_shuffle abc), shuffle_zero (left_shuffle abc))
  | _, Left abc ->
      let (Comp_shuffle_right (ab, abc')) = comp_shuffle_right bc abc in
      Comp_shuffle_right (Left ab, Left abc')
  | Left bc, Right abc ->
      let (Comp_shuffle_right (ab, abc')) = comp_shuffle_right bc abc in
      Comp_shuffle_right (Right ab, Left abc')
  | Right bc, Right abc ->
      let (Comp_shuffle_right (ab, abc')) = comp_shuffle_right bc abc in
      Comp_shuffle_right (ab, Right abc')

type (_, _) shuffle_right = Of_right : ('a, 'b, 'c) shuffle -> ('b, 'c) shuffle_right

let rec all_shuffles_right : type b c. b D.t -> c D.t -> (b, c) shuffle_right Seq.t =
 fun b c ->
  match b with
  | Nat Zero -> Seq.cons (Of_right (shuffle_zero c)) Seq.empty
  | Nat (Suc b') -> (
      match c with
      | Nat Zero -> Seq.empty
      | Nat (Suc c') ->
          Seq.append
            (Seq.map (fun (Of_right s) -> Of_right (Left s)) (all_shuffles_right b (Nat c')))
            (Seq.map
               (fun (Of_right s) -> Of_right (Right s))
               (all_shuffles_right (Nat b') (Nat c'))))
