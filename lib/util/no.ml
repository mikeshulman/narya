open Monoid

type zero = Dummy_zero
type 'a plus = Dummy_plus
type 'a minus = Dummy_minus
type plus_omega = Dummy_plus_omega
type minus_omega = Dummy_minus_omega
type _ fin = Zero : zero fin | Plus : 'a fin -> 'a plus fin | Minus : 'a fin -> 'a minus fin
type _ t = Fin : 'a fin -> 'a t | Plus_omega : plus_omega t | Minus_omega : minus_omega t

let zero = Fin Zero
let one = Fin (Plus Zero)
let minus_one = Fin (Minus Zero)
let two = Fin (Plus (Plus Zero))
let minus_two = Fin (Minus (Minus Zero))
let minus_omega = Minus_omega
let plus_omega = Plus_omega

type strict = Dummy_strict
type nonstrict = Dummy_nonstrict
type _ strictness = Strict : strict strictness | Nonstrict : nonstrict strictness

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

let rec le_refl : type a. a t -> (a, nonstrict, a) lt = function
  | Plus_omega -> Plusomega_plusomega
  | Minus_omega -> Minusomega_minusomega
  | Fin Zero -> Zero_zero
  | Fin (Plus a) -> Plus_plus (a, a, le_refl (Fin a))
  | Fin (Minus a) -> Minus_minus (a, a, le_refl (Fin a))

type (_, _, _) strict_trans =
  | Strict_any : (strict, 'a, 'a) strict_trans
  | Any_strict : ('a, strict, 'a) strict_trans
  | Nonstrict_nonstrict : (nonstrict, nonstrict, nonstrict) strict_trans

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

let rec lt_trans :
    type a b c s1 s2 s3.
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

let rec equal_fin : type a b. a fin -> b fin -> (a, b) compare =
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

let equal : type a b. a t -> b t -> (a, b) compare =
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
  | Fin _ as x -> Q.to_string (to_rat x)

type 'a then_plus = Dummy_then_plus
type 'a then_minus = Dummy_then_minus
type then_zero = Dummy_then_zero

type (_, _, _) prepend =
  | Zero : (then_zero, 'a, 'a) prepend
  | Plus : ('a, 'b plus, 'c) prepend -> ('a then_plus, 'b, 'c) prepend
  | Minus : ('a, 'b minus, 'c) prepend -> ('a then_minus, 'b, 'c) prepend

let rec prepend_uniq : type a b c c'. (a, b, c) prepend -> (a, b, c') prepend -> (c, c') eq =
 fun ab ab' ->
  match (ab, ab') with
  | Zero, Zero -> Eq
  | Plus ab, Plus ab' -> prepend_uniq ab ab'
  | Minus ab, Minus ab' -> prepend_uniq ab ab'

module type Fam = sig
  type 'a t
end

module MapMake (F : Fam) = struct
  type _ fin_t =
    | Emp : 'a fin_t
    | Node :
        (('a, zero, 'b) prepend * 'b F.t) option * 'a then_minus fin_t * 'a then_plus fin_t
        -> 'a fin_t

  let rec fin_find : type a b c. a fin_t -> b fin -> (a, b, c) prepend -> c F.t option =
   fun map x ab ->
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
        | Minus x -> fin_find mmap x (Minus ab)
        | Plus x -> fin_find pmap x (Plus ab))

  let rec fin_add : type a b c. a fin_t -> b fin -> (a, b, c) prepend -> c F.t -> a fin_t =
   fun map x ab y ->
    match (x, map) with
    | Zero, Emp -> Node (Some (ab, y), Emp, Emp)
    | Zero, Node (_, mmap, pmap) -> Node (Some (ab, y), mmap, pmap)
    | Minus x, Emp -> Node (None, fin_add Emp x (Minus ab) y, Emp)
    | Minus x, Node (z, mmap, pmap) ->
        let mmap = fin_add mmap x (Minus ab) y in
        Node (z, mmap, pmap)
    | Plus x, Emp -> Node (None, Emp, fin_add Emp x (Plus ab) y)
    | Plus x, Node (z, mmap, pmap) ->
        let pmap = fin_add pmap x (Plus ab) y in
        Node (z, mmap, pmap)

  let rec fin_remove : type a b. a fin_t -> b fin -> a fin_t =
   fun map x ->
    match map with
    | Emp -> Emp
    | Node (z, mmap, pmap) -> (
        match x with
        | Zero -> Node (None, mmap, pmap)
        | Minus x ->
            let mmap = fin_remove mmap x in
            Node (z, mmap, pmap)
        | Plus x ->
            let pmap = fin_remove pmap x in
            Node (z, mmap, pmap))

  type 'a no = 'a t

  type t = {
    fin : then_zero fin_t;
    minus_omega : minus_omega F.t option;
    plus_omega : plus_omega F.t option;
  }

  let empty = { fin = Emp; minus_omega = None; plus_omega = None }

  let find : type a. t -> a no -> a F.t option =
   fun map x ->
    match x with
    | Fin x -> fin_find map.fin x Zero
    | Minus_omega -> map.minus_omega
    | Plus_omega -> map.plus_omega

  let add : type a. a no -> a F.t -> t -> t =
   fun x y map ->
    match x with
    | Fin x -> { map with fin = fin_add map.fin x Zero y }
    | Minus_omega -> { map with minus_omega = Some y }
    | Plus_omega -> { map with plus_omega = Some y }

  let remove : type a. t -> a no -> t =
   fun map x ->
    match x with
    | Fin x -> { map with fin = fin_remove map.fin x }
    | Minus_omega -> { map with minus_omega = None }
    | Plus_omega -> { map with plus_omega = None }
end
