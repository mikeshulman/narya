(* "Forwards" natural numbers.  Backwards natural numbers are the natural lengths of backwards lists, while forwards natural numbers are the natural lengths of forwards lists.  This module should not be opened, but used qualified. *)

type zero = private Dummy_zero
type 'n suc = private Dummy_suc

(* We can add a backwards nat to a forwards nat and get a backwards one.  This is the length-level analogue of appending a forward list on the end of a backwards one.  *)

type (_, _, _) bplus =
  | Zero : ('a, zero, 'a) bplus
  | Suc : ('a N.suc, 'b, 'ab) bplus -> ('a, 'b suc, 'ab) bplus

type _ t = Zero : zero t | Suc : 'a t -> 'a suc t

let zero : zero t = Zero

let suc : type n. n t -> n suc t = function
  | n -> Suc n

let rec bplus_right : type a b ab. (a, b, ab) bplus -> b t = function
  | Zero -> Zero
  | Suc ab -> Suc (bplus_right ab)

let rec bplus_out : type a b ab. a N.t -> (a, b, ab) bplus -> ab N.t =
 fun a ab ->
  match ab with
  | Zero -> a
  | Suc ab -> bplus_out (N.suc a) ab

let rec bplus_uniq : type a b ab ab'. (a, b, ab) bplus -> (a, b, ab') bplus -> (ab, ab') Eq.t =
 fun ab ab' ->
  match (ab, ab') with
  | Zero, Zero -> Eq
  | Suc ab, Suc ab' ->
      let Eq = bplus_uniq ab ab' in
      Eq

type (_, _) has_bplus = Bplus : ('a, 'b, 'ab) bplus -> ('a, 'b) has_bplus

let rec bplus : type a b. b t -> (a, b) has_bplus = function
  | Zero -> Bplus Zero
  | Suc b ->
      let (Bplus ab) = bplus b in
      Bplus (Suc ab)

(* We can also get a forwards one as the result.  This is the length-level analogue of prepending a backwards list on the front of a forwards one.  *)
type (_, _, _) fplus =
  | Zero : (N.zero, 'a, 'a) fplus
  | Suc : ('a, 'b suc, 'ab) fplus -> ('a N.suc, 'b, 'ab) fplus

let rec fplus_left : type a b ab. (a, b, ab) fplus -> a N.t = function
  | Zero -> N.zero
  | Suc ab -> N.suc (fplus_left ab)

let rec fplus_uniq : type a b ab ab'. (a, b, ab) fplus -> (a, b, ab') fplus -> (ab, ab') Eq.t =
 fun ab ab' ->
  match (ab, ab') with
  | Zero, Zero -> Eq
  | Suc ab, Suc ab' ->
      let Eq = fplus_uniq ab ab' in
      Eq

let rec suc_fplus : type a b ab. (a, b, ab) fplus -> (a N.suc, b, ab suc) fplus = function
  | Zero -> Suc Zero
  | Suc ab -> Suc (suc_fplus ab)

type (_, _) has_fplus = Fplus : ('a, 'b, 'ab) fplus -> ('a, 'b) has_fplus

let rec fplus : type a b. a N.t -> (a, b) has_fplus = function
  | Nat Zero -> Fplus Zero
  | Nat (Suc a) ->
      let (Fplus ab) = fplus (Nat a) in
      Fplus (Suc ab)

(* These two kinds of addition associate with addition of backwards nats.  Here a, b, ab, and abc are backwards, while c and bc are forwards. *)
let rec assocr :
    type a b ab c bc abc.
    (a, b, ab) N.plus -> (b, c, bc) fplus -> (ab, c, abc) bplus -> (a, bc, abc) bplus =
 fun ab bc abc ->
  match (ab, bc) with
  | Zero, Zero -> abc
  | Suc ab, Suc bc -> assocr ab bc (Suc abc)

(* Convert a backwards nat to a forwards one. *)
type _ of_bwn = Of_bwn : 'a t * (N.zero, 'a, 'b) bplus -> 'b of_bwn

let of_bwn : type c. c N.t -> c of_bwn =
 fun c ->
  let rec go : type a b c. a N.t -> b t -> (a, b, c) bplus -> c of_bwn =
   fun a b abc ->
    match a with
    | Nat Zero -> Of_bwn (b, abc)
    | Nat (Suc a) -> go (Nat a) (Suc b) (Suc abc) in
  go c Zero Zero

(* Compare two forwards nats *)
let rec compare : type a b. a t -> b t -> (a, b) Eq.compare =
 fun a b ->
  match (a, b) with
  | Zero, Zero -> Eq
  | Suc a, Suc b -> (
      match compare a b with
      | Eq -> Eq
      | Neq -> Neq)
  | _ -> Neq

(* Convert a forwards nat to an integer *)
let rec to_int : type a. a t -> int = function
  | Zero -> 0
  | Suc a -> to_int a + 1
