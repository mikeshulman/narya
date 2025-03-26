open Signatures

(* Type-level dyadic rationals, represeted as surreal sign-sequences, plus +ω and -ω. *)

type zero = Dummy_zero
type 'a plus = Dummy_plus
type 'a minus = Dummy_minus
type plus_omega = Dummy_plus_omega
type minus_omega = Dummy_minus_omega
type _ fin = Zero : zero fin | Plus : 'a fin -> 'a plus fin | Minus : 'a fin -> 'a minus fin
type _ t = Fin : 'a fin -> 'a t | Plus_omega : plus_omega t | Minus_omega : minus_omega t
type one = zero plus
type two = one plus
type three = two plus
type four = three plus
type five = four plus
type six = five plus
type seven = six plus
type eight = seven plus
type minus_one = zero minus
type minus_two = minus_one minus

let zero : zero t = Fin Zero
let one : one t = Fin (Plus Zero)
let two : two t = Fin (Plus (Plus Zero))
let three : three t = Fin (Plus (Plus (Plus Zero)))
let four : four t = Fin (Plus (Plus (Plus (Plus Zero))))
let five : five t = Fin (Plus (Plus (Plus (Plus (Plus Zero)))))
let six : six t = Fin (Plus (Plus (Plus (Plus (Plus (Plus Zero))))))
let seven : seven t = Fin (Plus (Plus (Plus (Plus (Plus (Plus (Plus Zero)))))))
let eight : eight t = Fin (Plus (Plus (Plus (Plus (Plus (Plus (Plus (Plus Zero))))))))
let minus_one : minus_one t = Fin (Minus Zero)
let minus_two : minus_two t = Fin (Minus (Minus Zero))
let minus_omega = Minus_omega
let plus_omega = Plus_omega

(* Type-level indices for strict inequality < and non-strict inequality ≤. *)
type strict = Dummy_strict
type nonstrict = Dummy_nonstrict
type _ strictness = Strict : strict strictness | Nonstrict : nonstrict strictness

(* An element of "(a,strict,b) lt" is a witness that a<b, and similarly for nonstrict and a≤b. *)
type (_, _, _) lt =
  | Plusomega_plusomega : (plus_omega, nonstrict, plus_omega) lt
  | Minusomega_minusomega : (minus_omega, nonstrict, minus_omega) lt
  | Fin_plusomega : 'a fin -> ('a, 's, plus_omega) lt
  | Minusomega_plusomega : (minus_omega, 's, plus_omega) lt
  | Minusomega_fin : 'b fin -> (minus_omega, 's, 'b) lt
  | Zero_plus : 'b fin -> (zero, 's, 'b plus) lt
  | Minus_plus : 'a fin * 'b fin -> ('a minus, 's, 'b plus) lt
  | Minus_zero : 'a fin -> ('a minus, 's, zero) lt
  | Plus_plus : 'a fin * 'b fin * ('a, 's, 'b) lt -> ('a plus, 's, 'b plus) lt
  | Minus_minus : 'a fin * 'b fin * ('a, 's, 'b) lt -> ('a minus, 's, 'b minus) lt
  | Zero_zero : (zero, nonstrict, zero) lt

(* ≤, but not <, is reflexive. *)
let rec le_refl : type a. a t -> (a, nonstrict, a) lt = function
  | Plus_omega -> Plusomega_plusomega
  | Minus_omega -> Minusomega_minusomega
  | Fin Zero -> Zero_zero
  | Fin (Plus a) -> Plus_plus (a, a, le_refl (Fin a))
  | Fin (Minus a) -> Minus_minus (a, a, le_refl (Fin a))

let plusomega_nlt : type a b. (plus_omega, strict, a) lt -> b = function
  | Fin_plusomega _ -> .

let le_plusomega : type a. a t -> (a, nonstrict, plus_omega) lt = function
  | Minus_omega -> Minusomega_plusomega
  | Fin x -> Fin_plusomega x
  | Plus_omega -> Plusomega_plusomega

let minusomega_le : type a. a t -> (minus_omega, nonstrict, a) lt = function
  | Minus_omega -> Minusomega_minusomega
  | Fin x -> Minusomega_fin x
  | Plus_omega -> Minusomega_plusomega

let minusomega_lt_plusomega : (minus_omega, strict, plus_omega) lt = Minusomega_plusomega
let zero_lt_plusomega : type s. (zero, s, plus_omega) lt = Fin_plusomega Zero
let minusomega_lt_zero : type s. (minus_omega, s, zero) lt = Minusomega_fin Zero

type (_, _, _) strict_trans =
  | Strict_any : (strict, 'a, 'b) strict_trans
  | Any_strict : ('a, strict, 'b) strict_trans
  | Nonstrict_nonstrict : (nonstrict, nonstrict, nonstrict) strict_trans

type (_, _) has_strict_trans =
  | Strict_trans : ('s1, 's2, 's3) strict_trans -> ('s1, 's2) has_strict_trans

let strict_trans : type s1 s2. s1 strictness -> s2 strictness -> (s1, s2) has_strict_trans =
 fun s1 s2 ->
  match (s1, s2) with
  | Strict, _ -> Strict_trans Strict_any
  | _, Strict -> Strict_trans Any_strict
  | Nonstrict, Nonstrict -> Strict_trans Nonstrict_nonstrict

let rec lt_to_le : type a b s. (a, strict, b) lt -> (a, s, b) lt =
 fun lt ->
  match lt with
  | Fin_plusomega x -> Fin_plusomega x
  | Minusomega_plusomega -> Minusomega_plusomega
  | Minusomega_fin x -> Minusomega_fin x
  | Zero_plus x -> Zero_plus x
  | Minus_plus (x, y) -> Minus_plus (x, y)
  | Minus_zero x -> Minus_zero x
  | Plus_plus (x, y, xy) -> Plus_plus (x, y, lt_to_le xy)
  | Minus_minus (x, y, xy) -> Minus_minus (x, y, lt_to_le xy)

(*
let le_left : type a b s. (a, s, b) lt -> a t = function
  | Plusomega_plusomega -> Plus_omega
  | Minusomega_minusomega -> Minus_omega
  | Zero_plus _ -> Fin Zero
  | Zero_zero -> Fin Zero
  | Fin_plusomega a -> Fin a
  | Minusomega_plusomega -> Minus_omega
  | Minusomega_fin _ -> Minus_omega
  | Minus_plus (a, _) -> Fin (Minus a)
  | Minus_zero a -> Fin (Minus a)
  | Plus_plus (a, _, _) -> Fin (Plus a)
  | Minus_minus (a, _, _) -> Fin (Minus a)

let le_right : type a b s. (a, s, b) lt -> b t = function
  | Plusomega_plusomega -> Plus_omega
  | Minusomega_minusomega -> Minus_omega
  | Zero_plus b -> Fin (Plus b)
  | Zero_zero -> Fin Zero
  | Fin_plusomega _ -> Plus_omega
  | Minusomega_plusomega -> Plus_omega
  | Minusomega_fin b -> Fin b
  | Minus_plus (_, b) -> Fin (Plus b)
  | Minus_zero _ -> Fin Zero
  | Plus_plus (_, b, _) -> Fin (Plus b)
  | Minus_minus (_, b, _) -> Fin (Minus b)
*)

let rec lt_trans : type a b c s1 s2 s3.
    (s1, s2, s3) strict_trans -> (a, s1, b) lt -> (b, s2, c) lt -> (a, s3, c) lt =
 fun tr ab bc ->
  match (ab, bc, tr) with
  | Plusomega_plusomega, Plusomega_plusomega, Nonstrict_nonstrict -> Plusomega_plusomega
  | Minusomega_plusomega, Plusomega_plusomega, _ -> Minusomega_plusomega
  | Fin_plusomega a, Plusomega_plusomega, _ -> Fin_plusomega a
  | Minusomega_minusomega, Minusomega_minusomega, Nonstrict_nonstrict -> Minusomega_minusomega
  | Minusomega_minusomega, Minusomega_plusomega, _ -> Minusomega_plusomega
  | Minusomega_minusomega, Minusomega_fin b, _ -> Minusomega_fin b
  | Zero_plus _, Fin_plusomega (Plus _), _ -> Fin_plusomega Zero
  | Minus_plus (a, _), Fin_plusomega _, _ -> Fin_plusomega (Minus a)
  | Minus_zero a, Fin_plusomega _, _ -> Fin_plusomega (Minus a)
  | Plus_plus (a, _, _), Fin_plusomega _, _ -> Fin_plusomega (Plus a)
  | Zero_zero, Fin_plusomega _, _ -> Fin_plusomega Zero
  | Minus_minus (a, _, _), Fin_plusomega _, _ -> Fin_plusomega (Minus a)
  | Minusomega_fin _, Fin_plusomega _, _ -> Minusomega_plusomega
  | Minusomega_fin _, Zero_plus b, _ -> Minusomega_fin (Plus b)
  | Minusomega_fin _, Minus_plus (_, b), _ -> Minusomega_fin (Plus b)
  | Minusomega_fin _, Minus_zero _, _ -> Minusomega_fin Zero
  | Minusomega_fin _, Plus_plus (_, b, _), _ -> Minusomega_fin (Plus b)
  | Minusomega_fin _, Minus_minus (_, b, _), _ -> Minusomega_fin (Minus b)
  | Minusomega_fin _, Zero_zero, _ -> Minusomega_fin Zero
  | Minus_plus (a, _), Plus_plus (_, b, _), _ -> Minus_plus (a, b)
  | Minus_zero a, Zero_plus b, _ -> Minus_plus (a, b)
  | Minus_zero a, Zero_zero, _ -> Minus_zero a
  | Plus_plus (a, _, ab), Plus_plus (_, c, ac), _ -> Plus_plus (a, c, lt_trans tr ab ac)
  | Zero_zero, Zero_plus b, _ -> Zero_plus b
  | Zero_zero, Zero_zero, Nonstrict_nonstrict -> Zero_zero
  | Minus_minus (a, _, _), Minus_plus (_, b), _ -> Minus_plus (a, b)
  | Minus_minus (a, _, _), Minus_zero _, _ -> Minus_zero a
  | Minus_minus (a, _, ab), Minus_minus (_, c, bc), _ -> Minus_minus (a, c, lt_trans tr ab bc)
  | Zero_plus _, Plus_plus (_, b, _), _ -> Zero_plus b
  | Plusomega_plusomega, Fin_plusomega _, _ -> .
  | Minusomega_minusomega, Fin_plusomega _, _ -> .
  | Minusomega_fin _, Plusomega_plusomega, _ -> .
  | Minusomega_plusomega, Fin_plusomega _, _ -> .
  | Minusomega_fin _, Minusomega_minusomega, _ -> .
  | Minusomega_fin _, Minusomega_plusomega, _ -> .
  | Minusomega_fin _, Minusomega_fin _, _ -> .
  | Fin_plusomega _, Fin_plusomega _, _ -> .

let rec equal_fin : type a b. a fin -> b fin -> (a, b) Eq.compare =
 fun x y ->
  match (x, y) with
  | Zero, Zero -> Eq
  | Plus x, Plus y -> (
      match equal_fin x y with
      | Eq -> Eq
      | Neq -> Neq)
  | Minus x, Minus y -> (
      match equal_fin x y with
      | Eq -> Eq
      | Neq -> Neq)
  | _ -> Neq

let equal : type a b. a t -> b t -> (a, b) Eq.compare =
 fun x y ->
  match (x, y) with
  | Fin x, Fin y -> equal_fin x y
  | Plus_omega, Plus_omega -> Eq
  | Minus_omega, Minus_omega -> Eq
  | _ -> Neq

let equalb : type a b. a t -> b t -> bool =
 fun x y ->
  match equal x y with
  | Eq -> true
  | Neq -> false

(* Inequality is transitive.  There are many versions of this, depending on strictness of the inputs and outputs, but the only one we have need for so far is this. *)
let rec lt_trans1 : type a b c s1 s2. (a, s1, b) lt -> (b, s2, c) lt -> (a, s1, c) lt =
 fun ab bc ->
  match (ab, bc) with
  | Plusomega_plusomega, Plusomega_plusomega -> Plusomega_plusomega
  | Minusomega_plusomega, Plusomega_plusomega -> Minusomega_plusomega
  | Fin_plusomega a, Plusomega_plusomega -> Fin_plusomega a
  | Minusomega_minusomega, Minusomega_minusomega -> Minusomega_minusomega
  | Minusomega_minusomega, Minusomega_plusomega -> Minusomega_plusomega
  | Minusomega_minusomega, Minusomega_fin b -> Minusomega_fin b
  | Zero_plus _, Fin_plusomega (Plus _) -> Fin_plusomega Zero
  | Minus_plus (a, _), Fin_plusomega _ -> Fin_plusomega (Minus a)
  | Minus_zero a, Fin_plusomega _ -> Fin_plusomega (Minus a)
  | Plus_plus (a, _, _), Fin_plusomega _ -> Fin_plusomega (Plus a)
  | Zero_zero, Fin_plusomega _ -> Fin_plusomega Zero
  | Minus_minus (a, _, _), Fin_plusomega _ -> Fin_plusomega (Minus a)
  | Minusomega_fin _, Fin_plusomega _ -> Minusomega_plusomega
  | Minusomega_fin _, Zero_plus b -> Minusomega_fin (Plus b)
  | Minusomega_fin _, Minus_plus (_, b) -> Minusomega_fin (Plus b)
  | Minusomega_fin _, Minus_zero _ -> Minusomega_fin Zero
  | Minusomega_fin _, Plus_plus (_, b, _) -> Minusomega_fin (Plus b)
  | Minusomega_fin _, Minus_minus (_, b, _) -> Minusomega_fin (Minus b)
  | Minusomega_fin _, Zero_zero -> Minusomega_fin Zero
  | Minus_plus (a, _), Plus_plus (_, b, _) -> Minus_plus (a, b)
  | Minus_zero a, Zero_plus b -> Minus_plus (a, b)
  | Minus_zero a, Zero_zero -> Minus_zero a
  | Plus_plus (a, _, ab), Plus_plus (_, c, ac) ->
      let lt = lt_trans1 ab ac in
      Plus_plus (a, c, lt)
  | Zero_zero, Zero_plus b -> Zero_plus b
  | Zero_zero, Zero_zero -> Zero_zero
  | Minus_minus (a, _, _), Minus_plus (_, b) -> Minus_plus (a, b)
  | Minus_minus (a, _, _), Minus_zero _ -> Minus_zero a
  | Minus_minus (a, _, ab), Minus_minus (_, c, bc) ->
      let lt = lt_trans1 ab bc in
      Minus_minus (a, c, lt)
  | Zero_plus _, Plus_plus (_, b, _) -> Zero_plus b
  | Plusomega_plusomega, Fin_plusomega _ -> .
  | Minusomega_minusomega, Fin_plusomega _ -> .
  | Minusomega_fin _, Plusomega_plusomega -> .
  | Minusomega_plusomega, Fin_plusomega _ -> .
  | Minusomega_fin _, Minusomega_minusomega -> .
  | Minusomega_fin _, Minusomega_plusomega -> .
  | Minusomega_fin _, Minusomega_fin _ -> .
  | Fin_plusomega _, Fin_plusomega _ -> .

(* Decidable test for inequality. *)

let rec compare : type a s b. s strictness -> a t -> b t -> (a, s, b) lt option =
 fun s x y ->
  let open Monad.Ops (Monad.Maybe) in
  match (x, y) with
  | Fin Zero, Fin Zero -> (
      match s with
      | Strict -> None
      | Nonstrict -> Some Zero_zero)
  | Fin (Plus _), Fin Zero -> None
  | Fin (Minus x), Fin Zero -> Some (Minus_zero x)
  | Fin Zero, Fin (Plus y) -> Some (Zero_plus y)
  | Fin (Plus x), Fin (Plus y) ->
      let* r = compare s (Fin x) (Fin y) in
      return (Plus_plus (x, y, r))
  | Fin (Minus x), Fin (Plus y) -> Some (Minus_plus (x, y))
  | Fin Zero, Fin (Minus _) -> None
  | Fin (Plus _), Fin (Minus _) -> None
  | Fin (Minus x), Fin (Minus y) ->
      let* r = compare s (Fin x) (Fin y) in
      return (Minus_minus (x, y, r))
  | Plus_omega, Fin _ -> None
  | Minus_omega, Fin y -> Some (Minusomega_fin y)
  | Fin x, Plus_omega -> Some (Fin_plusomega x)
  | Fin _, Minus_omega -> None
  | Plus_omega, Plus_omega -> (
      match s with
      | Strict -> None
      | Nonstrict -> Some Plusomega_plusomega)
  | Minus_omega, Plus_omega -> Some Minusomega_plusomega
  | Plus_omega, Minus_omega -> None
  | Minus_omega, Minus_omega -> (
      match s with
      | Strict -> None
      | Nonstrict -> Some Minusomega_minusomega)

(* Convert to rationals in ZArith.Q. *)

let q_two = Q.add Q.one Q.one

let to_rat : type a. a t -> Q.t =
 fun x ->
  let rec fin_to_rat : type a. Q.t -> Q.t -> a fin -> Q.t =
   fun accum step x ->
    match x with
    | Zero -> accum
    | Plus x ->
        let step = if step = Q.one then step else Q.div (Q.abs step) q_two in
        fin_to_rat (Q.add accum step) step x
    | Minus x ->
        let step = if step = Q.minus_one then step else Q.neg (Q.div (Q.abs step) q_two) in
        fin_to_rat (Q.add accum step) step x in
  match x with
  | Plus_omega -> Q.inf
  | Minus_omega -> Q.minus_inf
  | Fin Zero -> Q.zero
  | Fin (Plus x) -> fin_to_rat Q.one Q.one x
  | Fin (Minus x) -> fin_to_rat Q.minus_one Q.minus_one x

(* Conversion from ZArith.Q can fail, if the input is not a dyadic rational.  (Note that a similar algorithm for floats would never fail, since all floating-point numbers *are* technically dyadic.) *)

type wrapped_fin = Wrapfin : 'a fin -> wrapped_fin
type wrapped = Wrap : 'a t -> wrapped

let of_rat (x : Q.t) : wrapped option =
  let rec of_rat x l r =
    let m = Q.div (Q.add l r) q_two in
    if x = m then Wrapfin Zero
    else if Q.(x < m) then
      let (Wrapfin y) = of_rat x l m in
      Wrapfin (Minus y)
    else
      let (Wrapfin y) = of_rat x m r in
      Wrapfin (Plus y) in
  let rec of_pos x l =
    let l' = Q.add l Q.one in
    if x = l' then Wrapfin (Plus Zero)
    else if Q.(x > l') then
      let (Wrapfin y) = of_pos x l' in
      Wrapfin (Plus y)
    else
      let (Wrapfin y) = of_rat x l l' in
      Wrapfin (Plus (Minus y)) in
  let rec of_neg x r =
    let r' = Q.sub r Q.one in
    if x = r' then Wrapfin (Minus Zero)
    else if Q.(x < r') then
      let (Wrapfin y) = of_neg x r' in
      Wrapfin (Minus y)
    else
      let (Wrapfin y) = of_rat x r' r in
      Wrapfin (Minus (Plus y)) in
  if x = Q.zero then Some (Wrap (Fin Zero))
  else if x = Q.inf then Some (Wrap Plus_omega)
  else if x = Q.minus_inf then Some (Wrap Minus_omega)
  else if Z.log2 x.den = Z.log2up x.den then
    if x > Q.zero then
      let (Wrapfin y) = of_pos x Q.zero in
      Some (Wrap (Fin y))
    else
      let (Wrapfin y) = of_neg x Q.zero in
      Some (Wrap (Fin y))
  else None

let to_string : type a. a t -> string = function
  | Plus_omega -> "+ω"
  | Minus_omega -> "-ω"
  | Fin _ as x ->
      let x = to_rat x in
      if Z.equal (Q.den x) Z.one then Z.to_string (Q.num x) else string_of_float (Q.to_float x)

(* Our sign-sequences above are morally *forwards* lists of signs, even though OCaml's type-former notation forces us to write them postfix.  That is, the type "zero minus plus plus" actually represents the sign-sequence "++-", meaning 1.5.  But it is also sometimes useful to have "backwards" lists of signs, so that for instance "then_zero then_minus then_plus then_plus" represents "-++".  *)

type 'a then_plus = Dummy_then_plus
type 'a then_minus = Dummy_then_minus
type then_zero = Dummy_then_zero

(* We can prepend a backwards sign sequence onto a forwards one. *)

type (_, _, _) prepend =
  | Zero : (then_zero, 'a, 'a) prepend
  | Plus : ('a, 'b plus, 'c) prepend -> ('a then_plus, 'b, 'c) prepend
  | Minus : ('a, 'b minus, 'c) prepend -> ('a then_minus, 'b, 'c) prepend

let rec prepend_uniq : type a b c c'. (a, b, c) prepend -> (a, b, c') prepend -> (c, c') Eq.t =
 fun ab ab' ->
  match (ab, ab') with
  | Zero, Zero -> Eq
  | Plus ab, Plus ab' -> prepend_uniq ab ab'
  | Minus ab, Minus ab' -> prepend_uniq ab ab'

let rec prepend_fin : type a b c. b fin -> (a, b, c) prepend -> c fin =
 fun b ab ->
  match ab with
  | Zero -> b
  | Plus ab -> prepend_fin (Plus b) ab
  | Minus ab -> prepend_fin (Minus b) ab

(* For a backwards 'a and forwards 'b, "('a, 'b) then_lt" says that whenever we prepend 'a onto a forwards sign-sequence 'c, the result is less than 'b.  This is a strong sort of inequality a<b. *)

type ('a, 'b) then_lt = { then_lt : 'c 'ac 's. 'c fin -> ('a, 'c, 'ac) prepend -> ('ac, 's, 'b) lt }
type ('a, 'b) then_gt = { then_gt : 'c 'ac 's. 'c fin -> ('a, 'c, 'ac) prepend -> ('b, 's, 'ac) lt }

(* It is strong enough that extending 'a by anything preserves it. *)

let then_plus_lt : type a b. (a, b) then_lt -> (a then_plus, b) then_lt =
 fun g -> { then_lt = (fun c (Plus ac) -> g.then_lt (Plus c) ac) }

let then_minus_lt : type a b. (a, b) then_lt -> (a then_minus, b) then_lt =
 fun g -> { then_lt = (fun c (Minus ac) -> g.then_lt (Minus c) ac) }

let then_plus_gt : type a b. (a, b) then_gt -> (a then_plus, b) then_gt =
 fun g -> { then_gt = (fun c (Plus ac) -> g.then_gt (Plus c) ac) }

let then_minus_gt : type a b. (a, b) then_gt -> (a then_minus, b) then_gt =
 fun g -> { then_gt = (fun c (Minus ac) -> g.then_gt (Minus c) ac) }

(* Inequalities b<c and b≤c are preserved by prepending any a onto both b and c. *)

let rec prepend_lt : type a b c ab ac s.
    b fin -> c fin -> (b, s, c) lt -> (a, b, ab) prepend -> (a, c, ac) prepend -> (ab, s, ac) lt =
 fun b c lt ab ac ->
  match (ab, ac) with
  | Zero, Zero -> lt
  | Plus ab, Plus ac -> prepend_lt (Plus b) (Plus c) (Plus_plus (b, c, lt)) ab ac
  | Minus ab, Minus ac -> prepend_lt (Minus b) (Minus c) (Minus_minus (b, c, lt)) ab ac

(* a prepended onto zero, or anything starting with a plus, is strongly greater than a followed by a minus. *)

let then_minus_lt' : type a b. (a, zero, b) prepend -> (a then_minus, b) then_lt =
 fun a_zero ->
  { then_lt = (fun c (Minus a_mc) -> prepend_lt (Minus c) Zero (Minus_zero c) a_mc a_zero) }

let then_minus_plus_lt' : type a b c. b fin -> (a, b plus, c) prepend -> (a then_minus, c) then_lt =
 fun b ab ->
  { then_lt = (fun d (Minus a_md) -> prepend_lt (Minus d) (Plus b) (Minus_plus (d, b)) a_md ab) }

let then_plus_gt' : type a b. (a, zero, b) prepend -> (a then_plus, b) then_gt =
 fun a_zero ->
  { then_gt = (fun c (Plus a_mc) -> prepend_lt Zero (Plus c) (Zero_plus c) a_zero a_mc) }

let then_plus_minus_gt' : type a b c. b fin -> (a, b minus, c) prepend -> (a then_plus, c) then_gt =
 fun b ab ->
  { then_gt = (fun d (Plus a_md) -> prepend_lt (Minus b) (Plus d) (Minus_plus (b, d)) ab a_md) }

(* We define a notion of intrinsically well-typed immutable map, associating to some numbers 'a an element of 'a F.t. *)

module Map = struct
  module Make (F : Fam2) = struct
    module Key = struct
      type nonrec 'a t = 'a t
    end

    (* First we define a map for finite numbers, then add the two omegas.  An element of "a fin_t" is a piece of a map indexed by a backwards sign-sequence a, in which the forward sign-sequence b acts as an index for something parametrized by the prepending of a onto b. *)

    type (_, _) node =
      | None : ('x, 'a) node
      | Some : (('a, zero, 'b) prepend * ('x, 'b) F.t) -> ('x, 'a) node

    type (_, _) fin_t =
      | Emp : ('x, 'a) fin_t
      | Node :
          ('x, 'a) node * ('x, 'a then_minus) fin_t * ('x, 'a then_plus) fin_t
          -> ('x, 'a) fin_t

    type 'x t = {
      fin : ('x, then_zero) fin_t;
      minus_omega : ('x, minus_omega) F.t option;
      plus_omega : ('x, plus_omega) F.t option;
    }

    (* The empty map *)
    let empty = { fin = Emp; minus_omega = None; plus_omega = None }

    (* 'find_opt' looks up a number in the map and returns its associated value, if any. *)

    let rec fin_find : type x a b c. b fin -> (x, a) fin_t -> (a, b, c) prepend -> (x, c) F.t option
        =
     fun x map ab ->
      match map with
      | Emp -> None
      | Node (y, mmap, pmap) -> (
          match x with
          | Zero -> (
              match y with
              | None -> None
              | Some (aa, y) ->
                  let Eq = prepend_uniq ab aa in
                  Some y)
          | Minus x -> fin_find x mmap (Minus ab)
          | Plus x -> fin_find x pmap (Plus ab))

    let find_opt : type x a. a Key.t -> x t -> (x, a) F.t option =
     fun x map ->
      match x with
      | Fin x -> fin_find x map.fin Zero
      | Minus_omega -> map.minus_omega
      | Plus_omega -> map.plus_omega

    (* 'add' adds an entry to the map, replacing any existing entry for that number. *)

    let rec fin_add : type x a b c.
        (x, a) fin_t -> b fin -> (a, b, c) prepend -> (x, c) F.t -> (x, a) fin_t =
     fun map x ab y ->
      match (x, map) with
      | Zero, Emp -> Node (Some (ab, y), Emp, Emp)
      | Zero, Node (_, mmap, pmap) -> Node (Some (ab, y), mmap, pmap)
      | Minus x, Emp -> Node (None, fin_add Emp x (Minus ab) y, Emp)
      | Minus x, Node (z, mmap, pmap) -> Node (z, fin_add mmap x (Minus ab) y, pmap)
      | Plus x, Emp -> Node (None, Emp, fin_add Emp x (Plus ab) y)
      | Plus x, Node (z, mmap, pmap) -> Node (z, mmap, fin_add pmap x (Plus ab) y)

    let add : type x a. a Key.t -> (x, a) F.t -> x t -> x t =
     fun x y map ->
      match x with
      | Fin x -> { map with fin = fin_add map.fin x Zero y }
      | Minus_omega -> { map with minus_omega = Some y }
      | Plus_omega -> { map with plus_omega = Some y }

    (* 'remove' removes an entry from the map. *)

    let rec fin_remove : type x a b. b fin -> (x, a) fin_t -> (x, a) fin_t =
     fun x map ->
      match map with
      | Emp -> Emp
      | Node (z, mmap, pmap) -> (
          match x with
          | Zero -> Node (None, mmap, pmap)
          | Minus x -> Node (z, fin_remove x mmap, pmap)
          | Plus x -> Node (z, mmap, fin_remove x pmap))

    let remove : type x a. a Key.t -> x t -> x t =
     fun x map ->
      match x with
      | Fin x -> { map with fin = fin_remove x map.fin }
      | Minus_omega -> { map with minus_omega = None }
      | Plus_omega -> { map with plus_omega = None }

    (* 'update' updates an entry in the map. *)

    let rec fin_update : type x a b c.
        (x, a) fin_t ->
        b fin ->
        (a, b, c) prepend ->
        ((x, c) F.t option -> (x, c) F.t option) ->
        (x, a) fin_t =
     fun map x ab f ->
      match (x, map) with
      | Zero, Emp -> (
          match f None with
          | Some z -> Node (Some (ab, z), Emp, Emp)
          | None -> Node (None, Emp, Emp))
      | Zero, Node (None, mmap, pmap) -> (
          match f None with
          | Some z -> Node (Some (ab, z), mmap, pmap)
          | None -> Node (None, mmap, pmap))
      | Zero, Node (Some (ab', y), mmap, pmap) -> (
          let Eq = prepend_uniq ab ab' in
          match f (Some y) with
          | Some z -> Node (Some (ab, z), mmap, pmap)
          | None -> Node (None, mmap, pmap))
      | Minus x, Emp -> Node (None, fin_update Emp x (Minus ab) f, Emp)
      | Minus x, Node (z, mmap, pmap) -> Node (z, fin_update mmap x (Minus ab) f, pmap)
      | Plus x, Emp -> Node (None, Emp, fin_update Emp x (Plus ab) f)
      | Plus x, Node (z, mmap, pmap) -> Node (z, mmap, fin_update pmap x (Plus ab) f)

    let update : type x a. a Key.t -> ((x, a) F.t option -> (x, a) F.t option) -> x t -> x t =
     fun x f map ->
      match x with
      | Fin x -> { map with fin = fin_update map.fin x Zero f }
      | Minus_omega -> { map with minus_omega = f map.minus_omega }
      | Plus_omega -> { map with plus_omega = f map.plus_omega }

    (* 'map' applies a function to all entries in the map. *)

    type 'a mapper = { map : 'g. 'g Key.t -> ('a, 'g) F.t -> ('a, 'g) F.t }

    let rec fin_map : type x a. x mapper -> (x, a) fin_t -> (x, a) fin_t =
     fun f m ->
      match m with
      | Emp -> Emp
      | Node (None, mmap, pmap) ->
          let mmap = fin_map f mmap in
          let pmap = fin_map f pmap in
          Node (None, mmap, pmap)
      | Node (Some (ab, z), mmap, pmap) ->
          let mmap = fin_map f mmap in
          let fz = f.map (Fin (prepend_fin Zero ab)) z in
          let pmap = fin_map f pmap in
          Node (Some (ab, fz), mmap, pmap)

    let map : type x. x mapper -> x t -> x t =
     fun f { fin; minus_omega; plus_omega } ->
      let minus_omega = Option.map (f.map Minus_omega) minus_omega in
      let fin = fin_map f fin in
      let plus_omega = Option.map (f.map Plus_omega) plus_omega in
      { fin; minus_omega; plus_omega }

    type 'a iterator = { it : 'g. 'g Key.t -> ('a, 'g) F.t -> unit }

    let rec fin_iter : type x a. x iterator -> (x, a) fin_t -> unit =
     fun f m ->
      match m with
      | Emp -> ()
      | Node (None, mmap, pmap) ->
          fin_iter f mmap;
          fin_iter f pmap
      | Node (Some (ab, z), mmap, pmap) ->
          fin_iter f mmap;
          f.it (Fin (prepend_fin Zero ab)) z;
          fin_iter f pmap

    let iter : type x. x iterator -> x t -> unit =
     fun f { fin; minus_omega; plus_omega } ->
      Option.iter (f.it Minus_omega) minus_omega;
      fin_iter f fin;
      Option.iter (f.it Plus_omega) plus_omega

    (* 'map_compare' applies one of three polymorphic function to all elements of the map, based on whether their index is less than, greater than, or equal to some specified number, passing a witness of inequality if relevant.  This requires a record type to hold the polymorphic mapper arguments, as well as several helper functions.  *)

    type ('x, 'b) map_compare = {
      map_lt : 'a 's. ('a, strict, 'b) lt -> ('x, 'a) F.t -> ('x, 'a) F.t;
      map_gt : 'a 's. ('b, strict, 'a) lt -> ('x, 'a) F.t -> ('x, 'a) F.t;
      map_eq : ('x, 'b) F.t -> ('x, 'b) F.t;
    }

    (* "fin_map_lt" applies map_lt to all elements of a fin_t, assuming that that is valid given its parameter, and dually for "fin_map_gt". *)

    let rec fin_map_lt : type a c x.
        (x, c) map_compare -> (a, c) then_lt -> (x, a) fin_t -> (x, a) fin_t =
     fun f x map ->
      match map with
      | Emp -> Emp
      | Node (z, mmap, pmap) ->
          Node
            ( (match z with
              | None -> None
              | Some (ab, y) -> Some (ab, f.map_lt (x.then_lt Zero ab) y)),
              fin_map_lt f (then_minus_lt x) mmap,
              fin_map_lt f (then_plus_lt x) pmap )

    let rec fin_map_gt : type x a c.
        (x, c) map_compare -> (a, c) then_gt -> (x, a) fin_t -> (x, a) fin_t =
     fun f x map ->
      match map with
      | Emp -> Emp
      | Node (z, mmap, pmap) ->
          Node
            ( (match z with
              | None -> None
              | Some (ab, y) -> Some (ab, f.map_gt (x.then_gt Zero ab) y)),
              fin_map_gt f (then_minus_gt x) mmap,
              fin_map_gt f (then_plus_gt x) pmap )

    (* Similarly, "fin_map_plusomega" applies a function to all elements of a fin_t, because +ω is greater than them, and dually. *)

    let rec fin_map_plusomega : type x a.
        (x, plus_omega) map_compare -> (x, a) fin_t -> (x, a) fin_t =
     fun f map ->
      match map with
      | Emp -> Emp
      | Node (z, mmap, pmap) ->
          Node
            ( (match z with
              | None -> None
              | Some (ab, y) -> Some (ab, f.map_lt (Fin_plusomega (prepend_fin Zero ab)) y)),
              fin_map_plusomega f mmap,
              fin_map_plusomega f pmap )

    let rec fin_map_minusomega : type x a.
        (x, minus_omega) map_compare -> (x, a) fin_t -> (x, a) fin_t =
     fun f map ->
      match map with
      | Emp -> Emp
      | Node (z, mmap, pmap) ->
          Node
            ( (match z with
              | None -> None
              | Some (ab, y) -> Some (ab, f.map_gt (Minusomega_fin (prepend_fin Zero ab)) y)),
              fin_map_minusomega f mmap,
              fin_map_minusomega f pmap )

    let rec fin_map_compare : type x a b c.
        (x, c) map_compare -> b fin -> (a, b, c) prepend -> (x, a) fin_t -> (x, a) fin_t =
     fun f x ab map ->
      match map with
      | Emp -> Emp
      | Node (z, mmap, pmap) -> (
          match x with
          | Zero ->
              let z =
                match z with
                | None -> None
                | Some (a_zero, z) ->
                    let Eq = prepend_uniq ab a_zero in
                    Some (ab, f.map_eq z) in
              Node (z, fin_map_lt f (then_minus_lt' ab) mmap, fin_map_gt f (then_plus_gt' ab) pmap)
          | Plus x ->
              let z =
                match z with
                | None -> None
                | Some (a_zero, z) ->
                    Some (a_zero, f.map_lt (prepend_lt Zero (Plus x) (Zero_plus x) a_zero ab) z)
              in
              Node
                (z, fin_map_lt f (then_minus_plus_lt' x ab) mmap, fin_map_compare f x (Plus ab) pmap)
          | Minus x ->
              let z =
                match z with
                | None -> None
                | Some (a_zero, z) ->
                    Some (a_zero, f.map_gt (prepend_lt (Minus x) Zero (Minus_zero x) ab a_zero) z)
              in
              Node
                ( z,
                  fin_map_compare f x (Minus ab) mmap,
                  fin_map_gt f (then_plus_minus_gt' x ab) pmap ))

    let map_compare : type b x. (x, b) map_compare -> b Key.t -> x t -> x t =
     fun f x map ->
      match x with
      | Minus_omega ->
          {
            minus_omega = Option.map f.map_eq map.minus_omega;
            fin = fin_map_minusomega f map.fin;
            plus_omega = Option.map (f.map_gt Minusomega_plusomega) map.plus_omega;
          }
      | Fin x ->
          {
            minus_omega = Option.map (f.map_lt (Minusomega_fin x)) map.minus_omega;
            fin = fin_map_compare f x Zero map.fin;
            plus_omega = Option.map (f.map_gt (Fin_plusomega x)) map.plus_omega;
          }
      | Plus_omega ->
          {
            minus_omega = Option.map (f.map_lt Minusomega_plusomega) map.minus_omega;
            fin = fin_map_plusomega f map.fin;
            plus_omega = Option.map f.map_eq map.plus_omega;
          }

    (* 'fin_least' finds the element in a fin_t with the least index, or None if the map is empty. *)

    type ('x, 'a) value =
      | Value : ('a, 'b, 'c) prepend * 'b fin * ('x, 'c) F.t -> ('x, 'a) value
      | None : ('x, 'a) value

    let rec fin_least : type x a. (x, a) fin_t -> (x, a) value =
     fun map ->
      match map with
      | Emp -> None
      | Node (x, mmap, pmap) -> (
          match fin_least mmap with
          | Value (Minus ab, b, y) -> Value (ab, Minus b, y)
          | None -> (
              match x with
              | Some (ab, y) -> Value (ab, Zero, y)
              | None -> (
                  match fin_least pmap with
                  | Value (Plus ab, b, y) -> Value (ab, Plus b, y)
                  | None -> None)))

    (* And dually for 'fin_greatest'. *)

    let rec fin_greatest : type x a. (x, a) fin_t -> (x, a) value =
     fun map ->
      match map with
      | Emp -> None
      | Node (x, mmap, pmap) -> (
          match fin_greatest pmap with
          | Value (Plus ab, b, y) -> Value (ab, Plus b, y)
          | None -> (
              match x with
              | Some (ab, y) -> Value (ab, Zero, y)
              | None -> (
                  match fin_greatest mmap with
                  | Value (Minus ab, b, y) -> Value (ab, Minus b, y)
                  | None -> None)))

    (* 'add_cut' adds a new entry to the map, with specified index, and whose value is computed from the next-highest and next-lowest entries, whatever they are, by a specified polymorphic function.  It requires upper and lower default values to be given in case there is no next-highest or next-lowest entry, i.e. the new entry will be the greatest and/or least one in the map.  If the specified index already has an entry, it is NOT replaced, instead the map is returned unchanged (but not untouched, so it is not physically equal to the input). *)

    type ('x, 'a) upper =
      | Upper : ('a, strict, 'c) lt * ('x, 'c) F.t -> ('x, 'a) upper
      | No_upper : ('x, 'a) upper

    type ('x, 'a) lower =
      | Lower : ('b, strict, 'a) lt * ('x, 'b) F.t -> ('x, 'a) lower
      | No_lower : ('x, 'a) lower

    let rec add_cut_fin : type a b c x.
        (a, b, c) prepend ->
        b fin ->
        ((x, c) lower -> (x, c) upper -> (x, c) F.t) ->
        (x, c) lower ->
        (x, c) upper ->
        (x, a) fin_t ->
        (x, a) fin_t =
     fun ab x f lower upper map ->
      match (x, map) with
      | Plus x, Emp -> Node (None, Emp, add_cut_fin (Plus ab) x f lower upper Emp)
      | Minus x, Emp -> Node (None, add_cut_fin (Minus ab) x f lower upper Emp, Emp)
      | Zero, Emp -> Node (Some (ab, f lower upper), Emp, Emp)
      | Zero, Node (Some _, _, _) -> map
      | Zero, Node (None, mmap, pmap) ->
          let lower =
            match fin_greatest mmap with
            | Value (Minus ad, d, z) -> Lower (prepend_lt (Minus d) Zero (Minus_zero d) ad ab, z)
            | None -> lower in
          let upper =
            match fin_least pmap with
            | Value (Plus ad, d, z) -> Upper (prepend_lt Zero (Plus d) (Zero_plus d) ab ad, z)
            | None -> upper in
          Node (Some (ab, f lower upper), mmap, pmap)
      | Minus x, Node ((Some (lt, y) as z), mmap, pmap) ->
          Node
            ( z,
              add_cut_fin (Minus ab) x f lower
                (Upper (prepend_lt (Minus x) Zero (Minus_zero x) ab lt, y))
                mmap,
              pmap )
      | Minus x, Node (None, mmap, pmap) -> (
          match fin_least pmap with
          | Value (Plus ad, d, y) ->
              Node
                ( None,
                  add_cut_fin (Minus ab) x f lower
                    (Upper (prepend_lt (Minus x) (Plus d) (Minus_plus (x, d)) ab ad, y))
                    mmap,
                  pmap )
          | None -> Node (None, add_cut_fin (Minus ab) x f lower upper mmap, pmap))
      | Plus x, Node ((Some (lt, y) as z), mmap, pmap) ->
          Node
            ( z,
              mmap,
              add_cut_fin (Plus ab) x f
                (Lower (prepend_lt Zero (Plus x) (Zero_plus x) lt ab, y))
                upper pmap )
      | Plus x, Node (None, mmap, pmap) -> (
          match fin_greatest mmap with
          | Value (Minus ad, d, y) ->
              Node
                ( None,
                  mmap,
                  add_cut_fin (Plus ab) x f
                    (Lower (prepend_lt (Minus d) (Plus x) (Minus_plus (d, x)) ad ab, y))
                    upper pmap )
          | None -> Node (None, mmap, add_cut_fin (Plus ab) x f lower upper pmap))

    let add_cut : type x b. b Key.t -> ((x, b) lower -> (x, b) upper -> (x, b) F.t) -> x t -> x t =
     fun x f map ->
      match x with
      | Fin x ->
          let lower =
            match map.minus_omega with
            | None -> No_lower
            | Some y -> Lower (Minusomega_fin x, y) in
          let upper =
            match map.plus_omega with
            | None -> No_upper
            | Some y -> Upper (Fin_plusomega x, y) in
          { map with fin = add_cut_fin Zero x f lower upper map.fin }
      | Minus_omega -> (
          match map.minus_omega with
          | Some _ -> map
          | None ->
              {
                map with
                minus_omega =
                  Some
                    (match fin_least map.fin with
                    | Value (Zero, b, y) -> f No_lower (Upper (Minusomega_fin b, y))
                    | None -> (
                        match map.plus_omega with
                        | Some y -> f No_lower (Upper (Minusomega_plusomega, y))
                        | None -> f No_lower No_upper));
              })
      | Plus_omega -> (
          match map.plus_omega with
          | Some _ -> map
          | None ->
              {
                map with
                plus_omega =
                  Some
                    (match fin_greatest map.fin with
                    | Value (Zero, b, y) -> f (Lower (Fin_plusomega b, y)) No_upper
                    | None -> (
                        match map.minus_omega with
                        | Some y -> f (Lower (Minusomega_plusomega, y)) No_upper
                        | None -> f No_lower No_upper));
              })
  end
end

(* An "upper interval" is of the form (p,+ω] or [p,+ω] for some tightness p.  Ordinarily we would call these "open" and "closed" intervals, but due to the potential confusion with "closed" and "open" notations we call them instead "strict" and "nonstrict". *)

type ('a, 's) iinterval = { strictness : 's strictness; endpoint : 'a t }
type interval = Interval : ('s, 'a) iinterval -> interval

module Interval = struct
  let empty : (plus_omega, strict) iinterval = { strictness = Strict; endpoint = plus_omega }

  let entire : (minus_omega, nonstrict) iinterval =
    { strictness = Nonstrict; endpoint = minus_omega }

  let plus_omega_only : (plus_omega, nonstrict) iinterval =
    { strictness = Nonstrict; endpoint = plus_omega }

  let to_string = function
    | Interval { strictness = Nonstrict; endpoint } ->
        Printf.sprintf "[%s,inf]" (to_string endpoint)
    | Interval { strictness = Strict; endpoint } -> Printf.sprintf "(%s,inf]" (to_string endpoint)

  let contains : type a s b. (a, s) iinterval -> b t -> (a, s, b) lt option =
   fun { strictness; endpoint } x -> compare strictness endpoint x

  let union : interval -> interval -> interval =
   fun (Interval t1 as i1) (Interval t2 as i2) ->
    match compare Strict t1.endpoint t2.endpoint with
    | Some _ -> i1
    | None -> (
        match compare Strict t2.endpoint t1.endpoint with
        | Some _ -> i2
        | None -> (
            match (t1.strictness, t2.strictness) with
            | Strict, Strict -> Interval { t1 with strictness = Strict }
            | _ -> Interval { t1 with strictness = Nonstrict }))

  type (_, _, _, _) subset =
    | Subset_strict : ('t2, strict, 't1) lt -> ('t1, 's1, 't2, 's2) subset
    | Subset_eq : ('t, 's, 't, 's) subset
    | Subset_nonstrict_strict : ('t, strict, 't, nonstrict) subset

  let subset_contains : type t1 s1 t2 s2 a.
      (t1, s1, t2, s2) subset -> (t1, s1, a) lt -> (t2, s2, a) lt =
   fun sub lt1 ->
    match sub with
    | Subset_strict lt2 -> lt_trans Strict_any lt2 lt1
    | Subset_eq -> lt1
    | Subset_nonstrict_strict -> lt_to_le lt1
end
