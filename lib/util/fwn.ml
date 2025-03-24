(* "Forwards" natural numbers.  Backwards natural numbers are the natural lengths of backwards lists, while forwards natural numbers are the natural lengths of forwards lists.  This module should not be opened, but used qualified. *)

type zero = private Dummy_zero
type 'n suc = private Dummy_suc
type one = zero suc
type two = one suc
type three = two suc
type four = three suc
type five = four suc
type six = five suc

(* We can add a backwards nat to a forwards nat and get a backwards one.  This is the length-level analogue of appending a forward list on the end of a backwards one.  *)

type (_, _, _) bplus =
  | Zero : ('a, zero, 'a) bplus
  | Suc : ('a N.suc, 'b, 'ab) bplus -> ('a, 'b suc, 'ab) bplus

type _ t = Zero : zero t | Suc : 'a t -> 'a suc t

let zero : zero t = Zero

let suc : type n. n t -> n suc t = function
  | n -> Suc n

let one : one t = suc zero

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

let rec suc_bplus_eq_suc : type a b ab. (a, b, ab) bplus -> (a N.suc, b, ab N.suc) bplus = function
  | Zero -> Zero
  | Suc ab -> Suc (suc_bplus_eq_suc ab)

let bplus_suc_eq_suc : type a b ab. (a, b, ab) bplus -> (a, b suc, ab N.suc) bplus =
 fun ab -> Suc (suc_bplus_eq_suc ab)

let rec insert_bplus : type a asuc b ab asucb.
    (a, asuc) N.insert -> (a, b, ab) bplus -> (asuc, b, asucb) bplus -> (ab, asucb) N.insert =
 fun i ab asucb ->
  match (ab, asucb) with
  | Zero, Zero -> i
  | Suc ab, Suc asucb -> insert_bplus (Later i) ab asucb

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
let rec bfplus_assocr : type a b ab c bc abc.
    (a, b, ab) N.plus -> (b, c, bc) fplus -> (ab, c, abc) bplus -> (a, bc, abc) bplus =
 fun ab bc abc ->
  match (ab, bc) with
  | Zero, Zero -> abc
  | Suc ab, Suc bc -> bfplus_assocr ab bc (Suc abc)

(* We can also add together two forwards nats. *)
type (_, _, _) plus =
  | Zero : (zero, 'a, 'a) plus
  | Suc : ('a, 'b, 'ab) plus -> ('a suc, 'b, 'ab suc) plus

type (_, _) has_plus = Plus : ('a, 'b, 'ab) plus -> ('a, 'b) has_plus

let rec plus : type a b. a t -> (a, b) has_plus = function
  | Zero -> Plus Zero
  | Suc a ->
      let (Plus ab) = plus a in
      Plus (Suc ab)

let rec plus_left : type a b ab. (a, b, ab) plus -> a t = function
  | Zero -> Zero
  | Suc ab -> Suc (plus_left ab)

let rec plus_uniq : type m n mn mn'. (m, n, mn) plus -> (m, n, mn') plus -> (mn, mn') Eq.t =
 fun mn mn' ->
  match (mn, mn') with
  | Zero, Zero -> Eq
  | Suc mn, Suc mn' ->
      let Eq = plus_uniq mn mn' in
      Eq

let rec suc_plus : type a b ab. (a, b suc, ab) plus -> (a suc, b, ab) plus = function
  | Zero -> Suc Zero
  | Suc ab -> Suc (suc_plus ab)

let rec plus_assocl : type m n mn p np mnp.
    (m, n, mn) plus -> (n, p, np) plus -> (m, np, mnp) plus -> (mn, p, mnp) plus =
 fun mn np m_np ->
  match mn with
  | Zero ->
      let Zero = m_np in
      np
  | Suc mn ->
      let (Suc m_np) = m_np in
      Suc (plus_assocl mn np m_np)

let rec plus_assocr : type m n mn p np mnp.
    (m, n, mn) plus -> (n, p, np) plus -> (mn, p, mnp) plus -> (m, np, mnp) plus =
 fun mn np mn_p ->
  match mn with
  | Zero ->
      let Eq = plus_uniq np mn_p in
      Zero
  | Suc mn ->
      let (Suc mn_p) = mn_p in
      let m_np = plus_assocr mn np mn_p in
      Suc m_np

type (_, _, _, _) plus_assocrr =
  | Plus_assocrr : ('b, 'c, 'bc) plus * ('a, 'bc, 'abc) plus -> ('a, 'b, 'c, 'abc) plus_assocrr

let rec plus_assocrr : type a b c ab abc.
    (a, b, ab) plus -> (ab, c, abc) plus -> (a, b, c, abc) plus_assocrr =
 fun ab ab_c ->
  match ab with
  | Zero -> Plus_assocrr (ab_c, Zero)
  | Suc ab ->
      let (Suc ab_c) = ab_c in
      let (Plus_assocrr (bc, a_bc)) = plus_assocrr ab ab_c in
      Plus_assocrr (bc, Suc a_bc)

(* This associates with bplus and fplus too.  Here a is backwards, while b, c, ab, bc, and abc are forwards. *)
let rec fbplus_assocl : type a b ab c bc abc.
    (a, b, ab) fplus -> (b, c, bc) plus -> (a, bc, abc) fplus -> (ab, c, abc) plus =
 fun ab bc abc ->
  match (ab, abc) with
  | Zero, Zero -> bc
  | Suc ab, Suc abc -> fbplus_assocl ab (Suc bc) abc

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

(* And vice versa *)
type _ to_bwn = To_bwn : 'a N.t * ('a, zero, 'b) fplus -> 'b to_bwn

let to_bwn : type c. c t -> c to_bwn =
 fun c ->
  let rec go : type a b c. a N.t -> b t -> (a, b, c) fplus -> c to_bwn =
   fun a b abc ->
    match b with
    | Zero -> To_bwn (a, abc)
    | Suc b -> go (N.suc a) b (Suc abc) in
  go N.zero c Zero

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

type wrapped = Wrap : 'a t -> wrapped

let rec of_int : int -> wrapped =
 fun n ->
  if n < 0 then raise (Invalid_argument "Fwn.of_int")
  else if n = 0 then Wrap Zero
  else
    let (Wrap n) = of_int (n - 1) in
    Wrap (Suc n)
