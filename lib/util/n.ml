(* Type-level natural numbers.  This module should not be opened, but used qualified.  Natural numbers are types satisfying the predicate 'a N.t. *)

(* ********** Definitions ********** *)

type zero = private Dummy_zero
type 'n suc = private Dummy_suc
type one = zero suc
type two = one suc
type three = two suc
type four = three suc
type five = four suc
type six = five suc

(* ********** Addition ********** *)

(* Addition as a relation.  It's tempting to think that since we're indexing by types, we could actually just use coproduct types rather than defining addition on canonical finite types as a relation.  However, coproducts aren't strictly associative, so we would have to transport across isomorphisms somehow.  Since OCaml is not univalent, it's easier to stick with canonical finite types and make addition a relation. *)
type (_, _, _) plus =
  | Zero : ('m, zero, 'm) plus
  | Suc : ('m, 'n, 'p) plus -> ('m, 'n suc, 'p suc) plus

(* Successors shift between the inputs of addition.  These are named after the shape of their outputs. *)
let rec plus_suc : type m n p. (m suc, n, p) plus -> (m, n suc, p) plus = function
  | Zero -> Suc Zero
  | Suc x -> Suc (plus_suc x)

let rec suc_plus_eq_suc : type m n p. (m, n, p) plus -> (m suc, n, p suc) plus = function
  | Zero -> Zero
  | Suc x -> Suc (suc_plus_eq_suc x)

let suc_plus : type m n p. (m, n suc, p) plus -> (m suc, n, p) plus =
 fun x ->
  let (Suc y) = suc_plus_eq_suc x in
  y

(* A type is a natural number if there is something it can be added to on the right. *)
type _ t = Nat : ('any, 'n, 'anyn) plus -> 'n t

(* Zero is a natural number *)
let zero : zero t = Nat Zero

(* Natural numbers are closed under successors *)
let suc : type n. n t -> n suc t = function
  | Nat n -> Nat (Suc n)

(* Some other small natural numbers *)
let one : one t = suc zero
let two : two t = suc one
let three : three t = suc two
let four : four t = suc three
let five : five t = suc four
let six : six t = suc five

(* A natural number can be added on the right to anything.  We "return a type" by wrapping it in a GADT.  *)
type (_, _) has_plus = Plus : ('m, 'n, 'mn) plus -> ('m, 'n) has_plus

let rec plus : type m n. n t -> (m, n) has_plus = function
  | Nat Zero -> Plus Zero
  | Nat (Suc n) ->
      let (Plus mn) = plus (Nat n) in
      Plus (Suc mn)

(* Addition preserves natural numbers *)
let rec plus_out : type m n mn. m t -> (m, n, mn) plus -> mn t =
 fun pm mn ->
  match mn with
  | Zero -> pm
  | Suc mn ->
      let (Nat p_mn) = plus_out pm mn in
      Nat (Suc p_mn)

(* Anything that can be added is a natural number *)
let plus_right : type m n mn. (m, n, mn) plus -> n t = fun mn -> Nat mn

let rec plus_left : type m n mn. (m, n, mn) plus -> mn t -> m t =
 fun p mn ->
  match (p, mn) with
  | Zero, _ -> mn
  | Suc p, Nat (Suc mn) -> plus_left p (Nat mn)

(* Sums are unique *)
let rec plus_uniq : type m n mn mn'. (m, n, mn) plus -> (m, n, mn') plus -> (mn, mn') Eq.t =
 fun mn mn' ->
  match (mn, mn') with
  | Zero, Zero -> Eq
  | Suc mn, Suc mn' ->
      let Eq = plus_uniq mn mn' in
      Eq

(* Addition is associative. *)

let rec plus_assocl : type m n mn p np mnp.
    (m, n, mn) plus -> (n, p, np) plus -> (m, np, mnp) plus -> (mn, p, mnp) plus =
 fun mn np m_np ->
  match np with
  | Zero ->
      let Eq = plus_uniq mn m_np in
      Zero
  | Suc np ->
      let (Suc m_np) = m_np in
      let mn_p = plus_assocl mn np m_np in
      Suc mn_p

let rec plus_assocr : type m n mn p np mnp.
    (m, n, mn) plus -> (n, p, np) plus -> (mn, p, mnp) plus -> (m, np, mnp) plus =
 fun mn np mn_p ->
  match np with
  | Zero ->
      let Zero = mn_p in
      mn
  | Suc np ->
      let (Suc mn_p) = mn_p in
      Suc (plus_assocr mn np mn_p)

(* Addition is left and right unital. *)
let rec zero_plus : type n. n t -> (zero, n, n) plus = function
  | Nat Zero -> Zero
  | Nat (Suc n) -> Suc (zero_plus (Nat n))

let plus_zero : type n. n t -> (n, zero, n) plus = fun _ -> Zero

(* Addition is commutative *)
let rec plus_comm : type m n mn. m t -> (m, n, mn) plus -> (n, m, mn) plus =
 fun m mn ->
  match mn with
  | Zero -> zero_plus m
  | Suc mn -> suc_plus_eq_suc (plus_comm m mn)

(* ********** Well-scoped De Bruijn indices ********** *)

(* It's tempting to take these actually *be* the types "zero" and "suc", i.e. to define

   type zero = |
   type 'n suc = Top | Pop of 'n

   However, with that approach a De Bruijn index in scope 'n is just an element of 'n, which doesn't guarantee that 'n is actually a type-level natural number; it could be any inhabited type at all.  Thus, we need extra hypotheses of "n N.t" in several places.  By contrast, if we define De Bruijn indices as a GADT, we are guaranteed that if we have an element of "n index" then n must be a natural number. *)

type _ index = Top : 'n suc index | Pop : 'n index -> 'n suc index

(* Lift an index to a context extended on the left, thereby maintaining the same numerical De Bruijn index value. *)
let rec plus_index : type m n mn. (m, n, mn) plus -> n index -> mn index =
 fun mn i ->
  match i with
  | Top ->
      let (Suc _) = mn in
      Top
  | Pop i ->
      let (Suc mn) = mn in
      Pop (plus_index mn i)

(* Lift an index to a context extended on the right, thereby extending the numerical De Bruijn index value by the same amount. *)
let rec index_plus : type m n mn. m index -> (m, n, mn) plus -> mn index =
 fun i mn ->
  match mn with
  | Zero -> i
  | Suc mn -> Pop (index_plus i mn)

(* Lift an index to a context extended on the right by one element, keeping the same numerical De Bruijn index.  *)
let rec suc_index : type m. m index -> m suc index = function
  | Top -> Top
  | Pop i -> Pop (suc_index i)

(* Lift an index to a context extended on the right, keeping the same numerical De Bruijn index.  Although computationally this is a no-op, unfortunately the best intrinsically well-typed implementation I've found is O(n^2). *)
let rec lift_index : type m n mn. (m, n, mn) plus -> m index -> mn index =
 fun mn i ->
  match i with
  | Top ->
      let (Suc _) = plus_suc mn in
      Top
  | Pop i ->
      let (Suc mn) = plus_suc mn in
      Pop (lift_index mn i)

(* Alternative implementation of lift_index, also O(n^2): *)
let rec _lift_index : type m n mn. (m, n, mn) plus -> m index -> mn index =
 fun mn i ->
  match mn with
  | Zero -> i
  | Suc mn -> suc_index (_lift_index mn i)

(* The mth index from the right of m+n+1. *)
let rec switch_index : type m n mn. m t -> (m, n suc, mn) plus -> mn index =
 fun (Nat m) mn ->
  match m with
  | Zero -> (
      match mn with
      | Suc _ -> Top)
  | Suc m -> (
      match plus_suc mn with
      | Suc mn -> Pop (switch_index (Nat m) mn))

(* If an 'n index is thought of as something to remove from a list of 'n things to get a smaller list, and if we remove one such thing and then another, we could have removed those things in the other order, and this function computes the indices that would be required to do that. *)
let rec swap_indices : type n. n suc index -> n index -> n suc index * n index =
 fun k l ->
  match k with
  | Top -> (
      match l with
      | Top -> (Pop l, Top)
      | Pop _ -> (Pop l, Top))
  | Pop k' -> (
      match l with
      | Top -> (Top, k')
      | Pop l' ->
          let l'', k'' = swap_indices k' l' in
          (Pop l'', Pop k''))

(* This function considers two indices equivalent if they are numerically the same De Bruijn index, even if they are in different contexts. *)
let rec index_equiv : type m n. m index -> n index -> unit option =
 fun k l ->
  match (k, l) with
  | Top, Top -> Some ()
  | Pop k, Pop l -> index_equiv k l
  | _, _ -> None

(* An index in a sum is either an index in the RHS, or an index in the LHS lifted. *)
let rec index_in_plus : type m n mn. (m, n, mn) plus -> mn index -> (m index, n index) Either.t =
 fun mn i ->
  match mn with
  | Zero -> Left i
  | Suc mn -> (
      match i with
      | Top -> Right Top
      | Pop i -> (
          match index_in_plus mn i with
          | Left j -> Left j
          | Right k -> Right (Pop k)))

(* ********** Insertions ********** *)

type (_, _) insert =
  | Now : ('a, 'a suc) insert
  | Later : ('a, 'b) insert -> ('a suc, 'b suc) insert

let rec insert_out : type a b. a t -> (a, b) insert -> b t =
 fun a i ->
  match i with
  | Now -> suc a
  | Later i ->
      let (Nat (Suc a)) = a in
      suc (insert_out (Nat a) i)

let rec insert_in : type a b. b t -> (a, b) insert -> a t =
 fun b i ->
  match i with
  | Now ->
      let (Nat (Suc a)) = b in
      Nat a
  | Later i ->
      let (Nat (Suc b)) = b in
      suc (insert_in (Nat b) i)

let rec plus_insert : type a b c ab ac.
    (a, b, ab) plus -> (a, c, ac) plus -> (b, c) insert -> (ab, ac) insert =
 fun ab ac i ->
  match i with
  | Now ->
      let (Suc ac) = ac in
      let Eq = plus_uniq ab ac in
      Now
  | Later i ->
      let Suc ab, Suc ac = (ab, ac) in
      Later (plus_insert ab ac i)

(* Extend an insertion by the identity *)
type (_, _, _) insert_plus =
  | Insert_plus : ('a, 'c, 'ac) plus * ('ac, 'bc) insert -> ('a, 'c, 'bc) insert_plus

let rec insert_plus : type a b c bc. (a, b) insert -> (b, c, bc) plus -> (a, c, bc) insert_plus =
 fun ins bc ->
  match bc with
  | Zero -> Insert_plus (Zero, ins)
  | Suc _ ->
      let (Insert_plus (ac, i)) = insert_plus (Later ins) (suc_plus bc) in
      Insert_plus (plus_suc ac, i)

let rec int_of_insert : type a b. (a, b) insert -> int = function
  | Now -> 0
  | Later i -> int_of_insert i + 1

let rec insert_of_index : type b. b suc index -> (b, b suc) insert = function
  | Top -> Now
  | Pop i -> (
      match i with
      | Top -> Later (insert_of_index i)
      | Pop _ -> Later (insert_of_index i))

let rec index_of_insert : type b bsuc. (b, bsuc) insert -> bsuc index = function
  | Now -> Top
  | Later i -> (
      match i with
      | Now -> Pop (index_of_insert i)
      | Later _ -> Pop (index_of_insert i))

(* Like swap_indices, but now tracking the types. *)
type (_, _) swap_inserts =
  | Swap_inserts : ('b, 'c) insert * ('a, 'b) insert -> ('a, 'c) swap_inserts

let rec swap_inserts : type a b c. (b, c) insert -> (a, b) insert -> (a, c) swap_inserts =
 fun k l ->
  match k with
  | Now -> (
      match l with
      | Now -> Swap_inserts (Later l, Now)
      | Later _ -> Swap_inserts (Later l, Now))
  | Later k' -> (
      match l with
      | Now -> Swap_inserts (Now, k')
      | Later l' ->
          let (Swap_inserts (l'', k'')) = swap_inserts k' l' in
          Swap_inserts (Later l'', Later k''))

(* Lift an insert to a context extended on the right by one element, keeping the same numerical De Bruijn index.  *)
let rec suc_insert : type a b. (a, b) insert -> (a suc, b suc) insert = function
  | Now -> Now
  | Later i -> Later (suc_insert i)

type _ insert_to = Insert_to : ('a, 'b) insert -> 'a insert_to

(* Lift one insert to a larger domain obtained by inserting something else.  Specifically, the result has the same numerical De Bruijn index as the "lift" argument.  Computationally this is a no-op. *)
let rec lift_insert : type a b c. lift:(a, b) insert -> over:(a, c) insert -> c insert_to =
 fun ~lift ~over ->
  match over with
  | Now -> Insert_to (suc_insert lift)
  | Later over -> (
      match lift with
      | Now -> Insert_to Now
      | Later lift ->
          let (Insert_to res) = lift_insert ~lift ~over in
          Insert_to (Later res))

(* Similarly, commute two insertions past each other, maintaining the same numerical De Bruijn index for both.  Another computational no-op. *)
type (_, _) commute_insert =
  | Commute_insert : ('b, 'd) insert * ('c, 'd) insert -> ('b, 'c) commute_insert

let rec commute_insert : type a b c.
    lift:(a, b) insert -> over:(a, c) insert -> (b, c) commute_insert =
 fun ~lift ~over ->
  match over with
  | Now -> Commute_insert (Now, suc_insert lift)
  | Later over -> (
      match lift with
      | Now -> Commute_insert (Later (suc_insert over), Now)
      | Later lift ->
          let (Commute_insert (s, t)) = commute_insert ~lift ~over in
          Commute_insert (Later s, Later t))

(* Check whether two insertions with the same output are equal.  If so, identify their inputs.  If not, commute them. *)
type (_, _) compare_inserts =
  | Eq_inserts : ('m, 'm) compare_inserts
  | Neq_inserts : ('r, 'm) insert * ('r, 'n) insert -> ('m, 'n) compare_inserts

let rec compare_inserts : type m n p. (m, p) insert -> (n, p) insert -> (m, n) compare_inserts =
 fun m n ->
  match (m, n) with
  | Now, Now -> Eq_inserts
  | Now, Later m -> Neq_inserts (m, Now)
  | Later n, Now -> Neq_inserts (Now, n)
  | Later m, Later n -> (
      match compare_inserts m n with
      | Eq_inserts -> Eq_inserts
      | Neq_inserts (m', n') -> Neq_inserts (Later m', Later n'))

(* Like index_equiv, but for inserts. *)
let rec insert_equiv : type m msuc n nsuc. (m, msuc) insert -> (n, nsuc) insert -> unit option =
 fun k l ->
  match (k, l) with
  | Now, Now -> Some ()
  | Later k, Later l -> insert_equiv k l
  | _, _ -> None

type (_, _, _) insert_in_plus =
  | Left : ('pred_m, 'm) insert * ('pred_m, 'n, 'pred_mn) plus -> ('m, 'n, 'pred_mn) insert_in_plus
  | Right : ('pred_n, 'n) insert * ('m, 'pred_n, 'pred_mn) plus -> ('m, 'n, 'pred_mn) insert_in_plus

let rec insert_in_plus : type m n pred_mn mn.
    (m, n, mn) plus -> (pred_mn, mn) insert -> (m, n, pred_mn) insert_in_plus =
 fun mn i ->
  match mn with
  | Zero -> Left (i, Zero)
  | Suc mn -> (
      match i with
      | Now -> Right (Now, mn)
      | Later i -> (
          match insert_in_plus mn i with
          | Left (j, pred_mn) -> Left (j, Suc pred_mn)
          | Right (k, pred_mn) -> Right (Later k, Suc pred_mn)))

type (_, _, _) insert_into_plus =
  | Left : ('m, 'msuc) insert * ('msuc, 'n, 'mn_suc) plus -> ('m, 'n, 'mn_suc) insert_into_plus
  | Right : ('n, 'nsuc) insert * ('m, 'nsuc, 'mn_suc) plus -> ('m, 'n, 'mn_suc) insert_into_plus

let rec insert_into_plus : type m n mn mn_suc.
    (m, n, mn) plus -> (mn, mn_suc) insert -> (m, n, mn_suc) insert_into_plus =
 fun mn i ->
  match i with
  | Now -> Right (Now, Suc mn)
  | Later i -> (
      match mn with
      | Zero -> Left (Later i, Zero)
      | Suc mn -> (
          match insert_into_plus mn i with
          | Left (j, mn_suc) -> Left (j, Suc mn_suc)
          | Right (k, mn_suc) -> Right (Later k, Suc mn_suc)))

type _ insert_into = Into : ('m, 'msuc) insert -> 'msuc insert_into

(* Iterate through all the insertions into a given nat. *)
let rec all_inserts : type n. n t -> n insert_into Seq.t = function
  | Nat Zero -> Seq.empty
  | Nat (Suc n) ->
      Seq.cons (Into Now) (Seq.map (fun (Into k) -> Into (Later k)) (all_inserts (Nat n)))

(* ********** Comparison ********** *)

(* We can compare two natural numbers, in such a way that equality identifies their types, and inequality is witnessed by addition. *)

type (_, _) trichotomy =
  | Eq : ('n, 'n) trichotomy
  | Lt : ('m, 'n suc, 'mn) plus -> ('m, 'mn) trichotomy
  | Gt : ('m, 'n suc, 'mn) plus -> ('mn, 'm) trichotomy

let rec trichotomy : type m n. m t -> n t -> (m, n) trichotomy =
 fun m n ->
  match (m, n) with
  | Nat Zero, Nat Zero -> Eq
  | Nat Zero, Nat (Suc n) -> Lt (zero_plus (Nat (Suc n)))
  | Nat (Suc m), Nat Zero -> Gt (zero_plus (Nat (Suc m)))
  | Nat (Suc m), Nat (Suc n) -> (
      match trichotomy (Nat m) (Nat n) with
      | Eq -> Eq
      | Lt p -> Lt (suc_plus_eq_suc p)
      | Gt p -> Gt (suc_plus_eq_suc p))

(* In particular, we can compare for equality and inequality. *)

let compare : type m n. m t -> n t -> (m, n) Eq.compare =
 fun m n ->
  match trichotomy m n with
  | Eq -> Eq
  | _ -> Neq

(* Similarly, we can compare two additions.  We are lazy and don't record the evidence for Lt and Gt. *)

type (_, _, _, _) plus_compare =
  | Eq : ('n, 'n, 'mn, 'mn) plus_compare
  | Lt : ('n1, 'n2, 'mn1, 'mn2) plus_compare
  | Gt : ('n1, 'n2, 'mn1, 'mn2) plus_compare

let rec plus_compare : type m n1 n2 mn1 mn2.
    (m, n1, mn1) plus -> (m, n2, mn2) plus -> (n1, n2, mn1, mn2) plus_compare =
 fun n1 n2 ->
  match (n1, n2) with
  | Zero, Zero -> Eq
  | Suc _, Zero -> Gt
  | Zero, Suc _ -> Lt
  | Suc n1, Suc n2 -> (
      match plus_compare n1 n2 with
      | Eq -> Eq
      | Lt -> Lt
      | Gt -> Gt)

let rec minus : type m n mn. mn t -> (m, n, mn) plus -> m t =
 fun mn n ->
  match (mn, n) with
  | mn, Zero -> mn
  | Nat (Suc mn), Suc n -> minus (Nat mn) n

let rec minus_uniq : type m1 m2 n mn. (m1, n, mn) plus -> (m2, n, mn) plus -> (m1, m2) Eq.t =
 fun n1 n2 ->
  match (n1, n2) with
  | Zero, Zero -> Eq
  | Suc n1, Suc n2 -> minus_uniq n1 n2

let minus_uniq' : type m n1 n2 mn. m t -> (m, n1, mn) plus -> (m, n2, mn) plus -> (n1, n2) Eq.t =
 fun m n1 n2 -> minus_uniq (plus_comm m n1) (plus_comm m n2)

(* ********** Converting to and from integers ********** *)

let rec int_of_plus : type m n mn. (m, n, mn) plus -> int = function
  | Zero -> 0
  | Suc n -> 1 + int_of_plus n

let to_int : type n. n t -> int = fun (Nat n) -> int_of_plus n

type _ plus_something = Plus_something : ('a, 'b, 'ab) plus -> 'a plus_something

let rec plus_of_int : type a. int -> a plus_something =
 fun b ->
  if b < 0 then raise (Invalid_argument "plus_of_int")
  else if b = 0 then Plus_something Zero
  else
    let (Plus_something ab) = plus_of_int (b - 1) in
    Plus_something (Suc ab)

let rec int_of_index : type n. n index -> int = function
  | Top -> 0
  | Pop k -> 1 + int_of_index k

let rec index_of_int : type n. n t -> int -> n index option =
 fun n x ->
  match n with
  | Nat Zero -> None
  | Nat (Suc n) ->
      if x < 0 then None
      else if x = 0 then Some Top
      else Option.map (fun y -> Pop y) (index_of_int (Nat n) (x - 1))

(* ********** Multiplication ********** *)

type (_, _, _) times =
  | Zero : 'n t -> ('n, zero, zero) times
  | Suc : ('n, 'm, 'nm) times * ('nm, 'n, 'nmn) plus -> ('n, 'm suc, 'nmn) times

let times_left : type a b ab. (a, b, ab) times -> a t = function
  | Zero a -> a
  | Suc (_, a) -> plus_right a

let rec times_right : type a b ab. (a, b, ab) times -> b t = function
  | Zero _ -> Nat Zero
  | Suc (ab, _) -> suc (times_right ab)

let rec times_out : type a b ab. (a, b, ab) times -> ab t =
 fun ab ->
  match ab with
  | Zero _ -> zero
  | Suc (ab, abc) -> plus_out (times_out ab) abc

type (_, _) has_times = Has_times : ('a, 'b, 'ab) times -> ('a, 'b) has_times

let rec times : type a b. a t -> b t -> (a, b) has_times =
 fun a -> function
  | Nat Zero -> Has_times (Zero a)
  | Nat (Suc b) ->
      let (Has_times ab) = times a (Nat b) in
      let (Plus aba) = plus a in
      Has_times (Suc (ab, aba))

let times_zero : type a. a t -> (a, zero, zero) times = fun a -> Zero a

let rec zero_times : type a. a t -> (zero, a, zero) times = function
  | Nat Zero -> Zero zero
  | Nat (Suc a) -> Suc (zero_times (Nat a), zero_plus zero)

let times_one : type a. a t -> (a, one, a) times = fun a -> Suc (Zero a, zero_plus a)

let rec one_times : type a. a t -> (one, a, a) times = function
  | Nat Zero -> Zero one
  | Nat (Suc a) -> Suc (one_times (Nat a), Suc Zero)

let rec times_uniq : type a b ab ab'. (a, b, ab) times -> (a, b, ab') times -> (ab, ab') Eq.t =
 fun ab ab' ->
  match (ab, ab') with
  | Zero _, Zero _ -> Eq
  | Suc (ab, aba), Suc (ab', ab'a) ->
      let Eq = times_uniq ab ab' in
      plus_uniq aba ab'a

let rec distrib_left : type a b c a_times_b a_times_c b_plus_c a_times__b_plus_c.
    (a, b, a_times_b) times ->
    (a, c, a_times_c) times ->
    (b, c, b_plus_c) plus ->
    (a, b_plus_c, a_times__b_plus_c) times ->
    (a_times_b, a_times_c, a_times__b_plus_c) plus =
 fun a_times_b a_times_c b_plus_c a_times__b_plus_c ->
  match b_plus_c with
  | Zero ->
      (* c=0, b+c=b *)
      let (Zero _) = a_times_c in
      (* a*c=0 *)
      let Eq = times_uniq a_times_b a_times__b_plus_c in
      (* a*b = a*(b+c) *)
      Zero
  | Suc b_plus_c' ->
      (* c=c'+1, b+c = (b+c')+1 *)
      let (Suc (a_times_c', a_times_c'__plus_a)) = a_times_c in
      (* a*c = a*c' + a *)
      let (Suc (a_times__b_plus_c', a_times__b_plus_c'___plus_a)) = a_times__b_plus_c in
      (* a*(b+c) = a*(b+c') + a *)
      plus_assocr
        (distrib_left a_times_b a_times_c' b_plus_c' a_times__b_plus_c')
        a_times_c'__plus_a a_times__b_plus_c'___plus_a

let distrib_left' : type a b c a_times_b a_times_c b_plus_c a_times__b_plus_c.
    (a, b, a_times_b) times ->
    (a, c, a_times_c) times ->
    (b, c, b_plus_c) plus ->
    (a_times_b, a_times_c, a_times__b_plus_c) plus ->
    (a, b_plus_c, a_times__b_plus_c) times =
 fun a_times_b a_times_c b_plus_c a_times_b__plus__a_times_c ->
  (* Lazy approach *)
  let (Has_times x) = times (times_left a_times_b) (plus_out (times_right a_times_b) b_plus_c) in
  let y = distrib_left a_times_b a_times_c b_plus_c x in
  let Eq = plus_uniq a_times_b__plus__a_times_c y in
  x

let rec times_assocl : type a b c ab bc abc.
    a t -> (a, b, ab) times -> (b, c, bc) times -> (a, bc, abc) times -> (ab, c, abc) times =
 fun a a_times_b b_times_c a_times__b_times_c ->
  match b_times_c with
  | Zero _ ->
      let (Zero _) = a_times__b_times_c in
      Zero (times_out a_times_b)
  | Suc (b_times_c', b_times_c'__plus_b) ->
      (* b*c = b*c' + b *)
      let (Has_times a_times__b_times_c') = times a (times_out b_times_c') in
      let a_times_b__times_c' = times_assocl a a_times_b b_times_c' a_times__b_times_c' in
      (* a*(b*c) = (a*b)*c *)
      let a_times_b__times_c'___plus__a_times_b =
        distrib_left a_times__b_times_c' a_times_b b_times_c'__plus_b a_times__b_times_c in
      Suc (a_times_b__times_c', a_times_b__times_c'___plus__a_times_b)

let rec times_assocr : type a b c ab bc abc.
    a t -> (a, b, ab) times -> (b, c, bc) times -> (ab, c, abc) times -> (a, bc, abc) times =
 fun a a_times_b b_times_c a_times_b__times_c ->
  (* We could take a lazy approach to this too, but we don't. *)
  match b_times_c with
  | Zero _ ->
      let (Zero _) = a_times_b__times_c in
      Zero a
  | Suc (b_times_c', b_times_c'__plus_b) ->
      (* b*c = b*c' + b *)
      let (Suc (a_times_b__times_c', a_times_b__times_c'___plus_a_times_b)) = a_times_b__times_c in
      (* (a*b)*c = (a*b)*c' + a*b *)
      let a_times__b_times_c' = times_assocr a a_times_b b_times_c' a_times_b__times_c' in
      (* (a*b)*c' = a*(b*c') *)
      distrib_left' a_times__b_times_c' a_times_b b_times_c'__plus_b
        a_times_b__times_c'___plus_a_times_b

(* We have shown that N is not just a commutative monoid but a rig! *)

(* ********** Exponentiation ********** *)

type (_, _, _) pow =
  | Zero : ('n, zero, one) pow
  | Suc : ('n, 'm, 'nm) pow * ('nm, 'n, 'nmn) times -> ('n, 'm suc, 'nmn) pow

type (_, _) has_pow = Has_pow : ('a, 'b, 'c) pow -> ('a, 'b) has_pow

let rec pow_right : type a b c. (a, b, c) pow -> b t = function
  | Zero -> Nat Zero
  | Suc (p, _) -> suc (pow_right p)

let pow_out : type a b ab. (a, b, ab) pow -> ab t =
 fun ab ->
  match ab with
  | Zero -> one
  | Suc (_, aba) -> times_out aba

let rec pow : type a b. a t -> b t -> (a, b) has_pow =
 fun a b ->
  match b with
  | Nat Zero -> Has_pow Zero
  | Nat (Suc b) ->
      let (Has_pow ab) = pow a (Nat b) in
      let (Has_times aba) = times (pow_out ab) a in
      Has_pow (Suc (ab, aba))

let rec pow_uniq : type a b ab ab'. (a, b, ab) pow -> (a, b, ab') pow -> (ab, ab') Eq.t =
 fun ab ab' ->
  match (ab, ab') with
  | Zero, Zero -> Eq
  | Suc (ab, aba), Suc (ab', ab'a) ->
      let Eq = pow_uniq ab ab' in
      times_uniq aba ab'a

let rec pow_plus : type a b c a_to_b a_to_c b_plus_c a_to__b_plus_c.
    a t ->
    (a, b, a_to_b) pow ->
    (a, c, a_to_c) pow ->
    (b, c, b_plus_c) plus ->
    (a, b_plus_c, a_to__b_plus_c) pow ->
    (a_to_b, a_to_c, a_to__b_plus_c) times =
 fun a a_to_b a_to_c b_plus_c a_to__b_plus_c ->
  match b_plus_c with
  | Zero ->
      (* c = 0, b+c = b *)
      let Zero = a_to_c in
      (* a^c = 1 *)
      let Eq = pow_uniq a_to_b a_to__b_plus_c in
      (* a^(b+c) = a^b *)
      times_one (pow_out a_to_b)
  | Suc b_plus_c' ->
      (* c = c'+1, b+c = (b+c')+1 *)
      let (Suc (a_to_c', a_to_c'__times_a)) = a_to_c in
      (* a^c = a^c' * a *)
      let (Suc (a_to__b_plus_c', a_to__b_plus_c'___times_a)) = a_to__b_plus_c in
      (* a^(b+c) = a^(b+c') * a *)
      let a_to_b__times__a_to_c' = pow_plus a a_to_b a_to_c' b_plus_c' a_to__b_plus_c' in
      (* a^(b+c') = a^b * a^c' *)
      times_assocr (pow_out a_to_b) a_to_b__times__a_to_c' a_to_c'__times_a
        a_to__b_plus_c'___times_a

(* ********** Positive numbers ********** *)

type _ pos = Pos : 'n t -> 'n suc pos

let zero_nonpos : type c. zero pos -> c = function
  | _ -> .

let plus_pos : type a b ab. a t -> b pos -> (a, b, ab) plus -> ab pos =
 fun a b ab ->
  let (Pos _) = b in
  let (Suc ab) = ab in
  Pos (plus_out a ab)

let rec insert_pos : type a b. a t -> (a, b) insert -> b pos =
 fun a i ->
  match i with
  | Now -> Pos a
  | Later i ->
      let (Nat (Suc a)) = a in
      let (Pos (Nat b)) = insert_pos (Nat a) i in
      Pos (Nat (Suc b))

let pos_plus : type a b ab. a pos -> (a, b, ab) plus -> ab pos =
 fun (Pos a) ab ->
  let (Suc ab) = plus_suc ab in
  Pos (plus_out a ab)

let pos : type a. a pos -> a t = fun (Pos a) -> suc a

let times_pos : type a b ab. a pos -> b pos -> (a, b, ab) times -> ab pos =
 fun a b ab ->
  let (Pos _) = b in
  let (Suc (ab, aba)) = ab in
  plus_pos (times_out ab) a aba

let rec pow_pos : type a b ab. a pos -> (a, b, ab) pow -> ab pos =
 fun a -> function
  | Zero -> Pos zero
  | Suc (nm, nmn) -> times_pos (pow_pos a nm) a nmn

type _ compare_zero = Zero : zero compare_zero | Pos : 'n pos -> 'n compare_zero

let compare_zero : type a. a t -> a compare_zero = function
  | Nat Zero -> Zero
  | Nat (Suc a) -> Pos (Pos (Nat a))

(* ******************** Permutations ******************** *)

(* A permutation is either the identity, or obtained from a smaller permutation by inserting the last element of the domain at some index of the codomain. *)
type (_, _) perm =
  | Id : ('a, 'a) perm
  | Insert : ('a, 'b) perm * 'b suc index -> ('a suc, 'b suc) perm

let rec perm_dom : type a b. b t -> (a, b) perm -> a t =
 fun b p ->
  match p with
  | Id -> b
  | Insert (p, _) ->
      let (Nat (Suc b)) = b in
      suc (perm_dom (Nat b) p)

(* Since our type-level naturals are skeletal, the domain and codomain of a permutation actually have to be equal.  But we never use this, because keeping them as distinct type variables provides better bug-catching type-checking, e.g. it prevents us from forgetting to invert a permutation when necessary. *)
let rec _perm_eq : type a b. (a, b) perm -> (a, b) Eq.t = function
  | Id -> Eq
  | Insert (p, _) ->
      let Eq = _perm_eq p in
      Eq

(* There is some redundancy in the above presentation of permutations: Insert (Id, Top) is the same permutation as Id of the successor.  We could probably set up the data structures to exclude that possibility statically, but for now we are content to provide a "smart constructor" version of Insert that refuses to create Insert (Id, Top), returning Id instead.  (The latter is preferred for efficiency reasons, because when computing with a permutation we can sometimes short-circuit the rest of the computation if we know the rest of the permutation is an identity.)  *)
let insert : type a b. (a, b) perm -> b suc index -> (a suc, b suc) perm =
 fun p i ->
  match (p, i) with
  | Id, Top -> Id
  | _ -> Insert (p, i)

(* Insert a sequence of 'c' elements into a permutation at the same position, in order. *)
let rec insert_many : type a b c ac bc.
    (a, b) perm -> b suc index -> (a, c, ac) plus -> (b, c, bc) plus -> (ac, bc) perm =
 fun p i ac bc ->
  match (ac, bc) with
  | Zero, Zero -> p
  | Suc ac, Suc bc -> insert (insert_many p i ac bc) (lift_index (suc_plus_eq_suc bc) i)

(* A permutation can be applied to an index in its domain to produce an index in its codomain. *)
let rec perm_apply : type a b. (a, b) perm -> a index -> b index =
 fun p i ->
  match (p, i) with
  | Id, _ -> i
  | Insert (_, j), Top -> j
  | Insert (p, j), Pop i -> fst (swap_indices j (perm_apply p i))

(* A permutation can be extended by the identity on the right. *)
let rec perm_plus : type a b c ac bc.
    (a, b) perm -> (a, c, ac) plus -> (b, c, bc) plus -> (ac, bc) perm =
 fun p ac bc ->
  match (ac, bc) with
  | Zero, Zero -> p
  | Suc ac, Suc bc -> insert (perm_plus p ac bc) Top

(* The identity permutation.  (With our current implementation this is just a constructor.) *)
let id_perm : type a. a t -> (a, a) perm = fun _ -> Id

(* To invert permutations, we first define the dual of "insert" that inserts the last element of the codomain into the domain. *)

let rec coinsert : type a b. (a, b) perm -> a suc index -> (a suc, b suc) perm =
 fun p i ->
  match i with
  | Top -> insert p Top
  | Pop i -> (
      match p with
      | Insert (p, j) -> insert (coinsert p i) (Pop j)
      | Id -> (
          match i with
          | Top -> insert (coinsert Id i) (Pop Top)
          | Pop _ -> insert (coinsert Id i) (Pop Top)))

let rec perm_inv : type a b. (a, b) perm -> (b, a) perm = function
  | Id -> Id
  | Insert (p, i) -> coinsert (perm_inv p) i

(* Similarly to degeneracies, the "residual" of permutation at an element of its domain is the image of that element together with the permutation obtained by removing that element from the domain and its image from the codomain. *)
type (_, _) perm_residual =
  | Residual : ('a, 'b) perm * 'b suc index -> ('a suc, 'b suc) perm_residual

let rec perm_residual : type a b. (a, b) perm -> a index -> (a, b) perm_residual =
 fun s k ->
  match (s, k) with
  | Insert (s, i), Top -> Residual (s, i)
  | Id, Top -> Residual (Id, Top)
  | Insert (s, i), Pop k ->
      let (Residual (s, j)) = perm_residual s k in
      let i, j = swap_indices i j in
      Residual (insert s j, i)
  | Id, Pop k ->
      let (Residual (s, j)) = perm_residual Id k in
      let i, j = swap_indices Top j in
      Residual (insert s j, i)

(* Using residuals, we can define composition of permutations. *)
let rec comp_perm : type a b c. (a, b) perm -> (b, c) perm -> (a, c) perm =
 fun a b ->
  match a with
  | Id -> b
  | Insert (s, k) ->
      let (Residual (t, i)) = perm_residual b k in
      insert (comp_perm s t) i
