open Bwd
open Tlist
open Hlist

(* Forwards vectors, indexed by type-level forwards natural numbers.  This module should not be opened, but used qualified. *)

type (_, _) t = [] : ('a, Fwn.zero) t | ( :: ) : 'a * ('a, 'n) t -> ('a, 'n Fwn.suc) t

let nil : type a. (a, Fwn.zero) t = []
let cons : type a n. a -> (a, n) t -> (a, n Fwn.suc) t = fun x xs -> x :: xs

let car : type a n. (a, n Fwn.suc) t -> a = function
  | x :: _ -> x

let cdr : type a n. (a, n Fwn.suc) t -> (a, n) t = function
  | _ :: xs -> xs

let rec length : type a n. (a, n) t -> n Fwn.t = function
  | [] -> Zero
  | _ :: xs -> Suc (length xs)

type _ wrapped = Wrap : ('a, 'n) t -> 'a wrapped

let rec of_list_map : type a b. (a -> b) -> a list -> b wrapped =
 fun f -> function
  | [] -> Wrap []
  | x :: xs ->
      let (Wrap xs) = of_list_map f xs in
      Wrap (f x :: xs)

let of_list : type a. a list -> a wrapped = fun xs -> of_list_map (fun x -> x) xs

let rec to_list_map : type a b n. (a -> b) -> (a, n) t -> b list =
 fun f -> function
  | [] -> []
  | x :: xs -> f x :: to_list_map f xs

let rec to_list : type a n. (a, n) t -> a list = function
  | [] -> []
  | x :: xs -> x :: to_list xs

let rec fold_left : type a n acc. (acc -> a -> acc) -> acc -> (a, n) t -> acc =
 fun f acc xs ->
  match xs with
  | [] -> acc
  | x :: xs -> fold_left f (f acc x) xs

let rec take_bwd : type a n. n Fwn.t -> a Bwd.t -> a Bwd.t * (a, n) t =
 fun n xs ->
  match n with
  | Zero -> (xs, [])
  | Suc n -> (
      match take_bwd n xs with
      | Snoc (xs, x), ys -> (xs, x :: ys)
      | Emp, _ -> raise Not_found)

let rec append : type a m n mn. (m, n, mn) Fwn.plus -> (a, m) t -> (a, n) t -> (a, mn) t =
 fun mn xs ys ->
  match (mn, xs) with
  | Zero, [] -> ys
  | Suc mn, x :: xs -> x :: append mn xs ys

let rec init : type a s n. (s -> a * s) -> n Fwn.t -> s -> (a, n) t =
 fun f n s ->
  match n with
  | Zero -> []
  | Suc n ->
      let x, s = f s in
      x :: init f n s

(* Generic traversal *)

module Heter = struct
  (* An hlist of vectors, all of the same length. *)
  type (_, _) ht =
    | [] : (nil, 'n) ht
    | ( :: ) : ('x, 'n) t * ('xs, 'n) ht -> (('x, 'xs) cons, 'n) ht

  (* The hlist of empty vectors. *)
  let rec nil : type xs. xs Tlist.t -> (xs, Fwn.zero) ht = function
    | Nil -> []
    | Cons xs -> [] :: nil xs

  (* Add an element to the front of each of an hlist of vectors. *)
  let rec cons : type xs n. xs hlist -> (xs, n) ht -> (xs, n Fwn.suc) ht =
   fun xs ys ->
    match (xs, ys) with
    | [], [] -> []
    | x :: xs, y :: ys -> (x :: y) :: cons xs ys

  let car' = car
  let cdr' = cdr

  (* Extract the car and cdr of each of an hlist of vectors, returning another hlist.*)
  let rec car : type xs n. (xs, n Fwn.suc) ht -> xs hlist = function
    | [] -> []
    | x :: xs -> car' x :: car xs

  let rec cdr : type xs n. (xs, n Fwn.suc) ht -> (xs, n) ht = function
    | [] -> []
    | x :: xs -> cdr' x :: cdr xs
end

(* Now we can define the general heterogeneous traversal. *)

module Applicatic (M : Applicative.Plain) = struct
  open Applicative.Ops (M)

  let rec pmapM : type x xs ys n.
      ((x, xs) cons hlist -> ys hlist M.t) ->
      ((x, xs) cons, n) Heter.ht ->
      ys Tlist.t ->
      (ys, n) Heter.ht M.t =
   fun f xss ys ->
    match xss with
    | [] :: _ -> return (Heter.nil ys)
    | (x :: xs) :: xss ->
        let+ fx = f (x :: Heter.car xss) and+ fxs = pmapM f (xs :: Heter.cdr xss) ys in
        Heter.cons fx fxs

  (* With specializations to simple arity possibly-monadic maps and iterators.  *)

  let miterM : type x xs n.
      ((x, xs) cons hlist -> unit M.t) -> ((x, xs) cons, n) Heter.ht -> unit M.t =
   fun f xss ->
    let+ [] =
      pmapM
        (fun x ->
          let+ () = f x in
          Hlist.nil)
        xss Nil in
    ()

  let mmapM : type x xs y n.
      ((x, xs) cons hlist -> y M.t) -> ((x, xs) cons, n) Heter.ht -> (y, n) t M.t =
   fun f xss ->
    let+ [ ys ] =
      pmapM
        (fun x ->
          let+ y = f x in
          Hlist.cons y Hlist.nil)
        xss (Cons Nil) in
    ys

  let mapM : type x y n. (x -> y M.t) -> (x, n) t -> (y, n) t M.t =
   fun f xs -> mmapM (fun [ x ] -> f x) [ xs ]

  let mapM2 : type x y z n. (x -> y -> z M.t) -> (x, n) t -> (y, n) t -> (z, n) t M.t =
   fun f xs ys -> mmapM (fun [ x; y ] -> f x y) [ xs; ys ]

  let iterM : type x n. (x -> unit M.t) -> (x, n) t -> unit M.t =
   fun f xs -> miterM (fun [ x ] -> f x) [ xs ]

  let iterM2 : type x y n. (x -> y -> unit M.t) -> (x, n) t -> (y, n) t -> unit M.t =
   fun f xs ys -> miterM (fun [ x; y ] -> f x y) [ xs; ys ]
end

module Monadic (M : Monad.Plain) = struct
  module A = Applicative.OfMonad (M)
  include Applicatic (A)
end

let pmap : type x xs ys n.
    ((x, xs) cons hlist -> ys hlist) -> ((x, xs) cons, n) Heter.ht -> ys Tlist.t -> (ys, n) Heter.ht
    =
 fun f xss ys ->
  let open Monadic (Monad.Identity) in
  pmapM f xss ys

let mmap : type x xs y n. ((x, xs) cons hlist -> y) -> ((x, xs) cons, n) Heter.ht -> (y, n) t =
 fun f xs ->
  let open Monadic (Monad.Identity) in
  mmapM f xs

let miter : type x xs n. ((x, xs) cons hlist -> unit) -> ((x, xs) cons, n) Heter.ht -> unit =
 fun f xss ->
  let open Monadic (Monad.Identity) in
  miterM f xss

let map : type x y n. (x -> y) -> (x, n) t -> (y, n) t = fun f xs -> mmap (fun [ x ] -> f x) [ xs ]
