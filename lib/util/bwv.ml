(* Backwards vectors, indexed by type-level (backwards) natural numbers.  This module should not be opened, but used qualified. *)

open Bwd
open Tlist
open Hlist

(* An ('a, 'n) Bwv.t is a vector of length 'n of elements of type 'a. *)
type (_, _) t = Emp : ('a, N.zero) t | Snoc : ('a, 'n) t * 'a -> ('a, 'n N.suc) t

let emp : type a. (a, N.zero) t = Emp
let snoc : type a n. (a, n) t -> a -> (a, n N.suc) t = fun xs x -> Snoc (xs, x)

(* A Bwv of nonempty length always has a "tail" (now, the last element) and "head" (the rest of the Bwv), with no possibility of exceptions. *)
let tail : type a n. (a, n N.suc) t -> a = function
  | Snoc (_, x) -> x

let head : type a n. (a, n N.suc) t -> (a, n) t = function
  | Snoc (xs, _) -> xs

(* The length of a vector is always a natural number. *)
let rec zero_plus_length : type a n. (a, n) t -> (N.zero, n, n) N.plus = function
  | Emp -> Zero
  | Snoc (xs, _) -> Suc (zero_plus_length xs)

let length : type a n. (a, n) t -> n N.t = fun v -> Nat (zero_plus_length v)

let is_empty : type a n. (a, n) t -> bool = function
  | Emp -> true
  | Snoc (_, _) -> false

(* Sometimes we want to add the length of a backwards vector to another type-level nat.  This function does both of those in one traversal. *)
let rec plus_length : type a m n. (a, n) t -> (m, n) N.has_plus = function
  | Emp -> Plus Zero
  | Snoc (xs, _) ->
      let (Plus mn) = plus_length xs in
      Plus (Suc mn)

(* De Bruijn indices are the natural index into a backwards vector. *)
let rec nth : type a n. n N.index -> (a, n) t -> a =
 fun k xs ->
  match xs with
  | Snoc (xs, x) -> (
      match k with
      | Top -> x
      | Pop k -> nth k xs)
  | Emp -> (
      match k with
      | _ -> .)

(* Take the *first* m elements (those on the left) of a vector of length m+n. *)
let rec take : type a m n mn. (m, n, mn) N.plus -> (a, mn) t -> (a, m) t =
 fun mn xs ->
  match mn with
  | Zero -> xs
  | Suc mn ->
      let (Snoc (xs, _)) = xs in
      take mn xs

(* Take a specified number of elements from the front (left) of a list to make a vector of that length, if there are that many, returning the vector and the rest of the list.  *)
let of_list : type a mn. mn N.t -> a list -> ((a, mn) t * a list) option =
 fun n ys ->
  let rec of_list : type m n. (m, n, mn) N.plus -> (a, m) t -> a list -> ((a, mn) t * a list) option
      =
   fun n xs ys ->
    match (n, ys) with
    | Zero, _ -> Some (xs, ys)
    | Suc _, y :: ys -> of_list (N.suc_plus n) (Snoc (xs, y)) ys
    | _ -> None in
  of_list (N.zero_plus n) Emp ys

(* Find the rightmost occurrence of an element in a vector, if any, and return its De Bruijn index. *)
let rec find_opt : type a n. (a -> bool) -> (a, n) t -> (a * n N.index) option =
 fun test -> function
  | Emp -> None
  | Snoc (xs, x) ->
      if test x then Some (x, Top) else Option.map (fun (y, z) -> (y, N.Pop z)) (find_opt test xs)

(* Find the rightmost occurrence of an element and return its De Bruijn index, along with the vector with that element removed. *)
let rec find_remove : type a n. a -> (a, n N.suc) t -> ((a, n) t * n N.suc N.index) option =
 fun y (Snoc (xs, x)) ->
  if x = y then Some (xs, Top)
  else
    match xs with
    | Emp -> None
    | Snoc _ -> (
        match find_remove y xs with
        | None -> None
        | Some (ys, i) -> Some (Snoc (ys, x), Pop i))

(* Insert an element at a specified index. *)
let rec insert : type a n. n N.suc N.index -> a -> (a, n) t -> (a, n N.suc) t =
 fun i x xs ->
  match i with
  | Top -> Snoc (xs, x)
  | Pop i -> (
      match xs with
      | Emp -> (
          match i with
          | _ -> .)
      | Snoc (xs, y) -> Snoc (insert i x xs, y))

(* Apply a permutation *)
let rec permute : type a m n. (a, m) t -> (m, n) N.perm -> (a, n) t =
 fun xs p ->
  match (xs, p) with
  | _, Id -> xs
  | Snoc (xs, x), Insert (p, i) ->
      let ys = permute xs p in
      insert i x ys

(* Fill a new vector with the return values of a function. *)
let rec init : type a n. n N.t -> (n N.index -> a) -> (a, n) t =
 fun n f ->
  match n with
  | Nat Zero -> Emp
  | Nat (Suc n) -> Snoc (init (Nat n) (fun k -> f (Pop k)), f Top)

(* Mapping and iterating over vectors.  We use the general framework of mmap for traversals, so we start with heterogeneous lists. *)

module Heter = struct
  (* An hlist of bwvs, all of the same length. *)
  type (_, _) ht =
    | [] : (nil, 'n) ht
    | ( :: ) : ('x, 'n) t * ('xs, 'n) ht -> (('x, 'xs) cons, 'n) ht

  (* The hlist of empty bwvs. *)
  let rec emp : type xs. xs Tlist.t -> (xs, N.zero) ht = function
    | Nil -> []
    | Cons xs -> Emp :: emp xs

  (* Add an element to the end of each of an hlist of bwvs. *)
  let rec snoc : type xs n. (xs, n) ht -> xs hlist -> (xs, n N.suc) ht =
   fun xs ys ->
    match (xs, ys) with
    | [], [] -> []
    | x :: xs, y :: ys -> Snoc (x, y) :: snoc xs ys

  let head' = head
  let tail' = tail

  (* Extract the head and tail of each of an hlist of bwvs, returting another hlist.*)
  let rec tail : type xs n. (xs, n N.suc) ht -> xs hlist = function
    | [] -> []
    | x :: xs -> tail' x :: tail xs

  let rec head : type xs n. (xs, n N.suc) ht -> (xs, n) ht = function
    | [] -> []
    | x :: xs -> head' x :: head xs
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
    | Emp :: _ -> return (Heter.emp ys)
    | Snoc (xs, x) :: xss ->
        let+ fxs = pmapM f (xs :: Heter.head xss) ys and+ fx = f (x :: Heter.tail xss) in
        Heter.snoc fxs fx

  (* With specializations to simple arity possibly-monadic maps and iterators.  *)

  let miterM : type x xs n.
      ((x, xs) cons hlist -> unit M.t) -> ((x, xs) cons, n) Heter.ht -> unit M.t =
   fun f xss ->
    let+ [] =
      pmapM
        (fun x ->
          let+ () = f x in
          [])
        xss Nil in
    ()

  let mmapM : type x xs y n.
      ((x, xs) cons hlist -> y M.t) -> ((x, xs) cons, n) Heter.ht -> (y, n) t M.t =
   fun f xss ->
    let+ [ ys ] =
      pmapM
        (fun x ->
          let+ y = f x in
          [ y ])
        xss (Cons Nil) in
    ys

  let mapM : type x y n. (x -> y M.t) -> (x, n) t -> (y, n) t M.t =
   fun f xs -> mmapM (fun [ x ] -> f x) [ xs ]

  let mapM2 : type x y z n. (x -> y -> z M.t) -> (x, n) t -> (y, n) t -> (z, n) t M.t =
   fun f xs ys -> mmapM (fun [ x; y ] -> f x y) [ xs; ys ]

  let mapM1_2 : type x y z n. (x -> (y * z) M.t) -> (x, n) t -> ((y, n) t * (z, n) t) M.t =
   fun f xs ->
    let open Applicative.Ops (M) in
    let+ [ ys; zs ] =
      pmapM
        (fun [ x ] ->
          let+ y, z = f x in
          [ y; z ])
        [ xs ] (Cons (Cons Nil)) in
    (ys, zs)

  let mapM1_3 : type x y z w n.
      (x -> (y * z * w) M.t) -> (x, n) t -> ((y, n) t * (z, n) t * (w, n) t) M.t =
   fun f xs ->
    let open Applicative.Ops (M) in
    let+ [ ys; zs; ws ] =
      pmapM
        (fun [ x ] ->
          let+ y, z, w = f x in
          [ y; z; w ])
        [ xs ] (Cons (Cons (Cons Nil))) in
    (ys, zs, ws)

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

let map : type a b n. (a -> b) -> (a, n) t -> (b, n) t = fun f xs -> mmap (fun [ x ] -> f x) [ xs ]

let map2 : type a b c n. (a -> b -> c) -> (a, n) t -> (b, n) t -> (c, n) t =
 fun f xs ys -> mmap (fun [ x; y ] -> f x y) [ xs; ys ]

(* Note that with these definitions, the iteration direction is from *left to right*, in contrast to the choice made for backwards lists in Bwd. *)
let iter : type a n. (a -> unit) -> (a, n) t -> unit = fun f xs -> miter (fun [ x ] -> f x) [ xs ]

let iter2 : type a b n. (a -> b -> unit) -> (a, n) t -> (b, n) t -> unit =
 fun f xs ys -> miter (fun [ x; y ] -> f x y) [ xs; ys ]

(* Generating *)

(* List all the De Bruijn indices for a given nat. *)
let rec all_indices : type n. n N.t -> (n N.index, n) t = function
  | Nat Zero -> Emp
  | Nat (Suc n) ->
      let xs = all_indices (Nat n) in
      Snoc (map (fun i -> N.Pop i) xs, Top)

(* Searching *)

(* Find an element in one Bwv satisfying a predicate, if one exists, and return a function of the element and length of the remaining vector at the same (backwards) index of another, possibly longer, Bwv. *)
let rec find2l : type m n mn a b c.
    (m, n, mn) N.plus -> (a -> bool) -> (int -> b -> c) -> (a, n) t -> (b, mn) t -> c option =
 fun mn p f xs ys ->
  match (mn, xs, ys) with
  | Zero, _, _ -> None
  | Suc mn, Snoc (xs, x), Snoc (ys, y) ->
      if p x then Some (f (N.to_int (length ys)) y) else find2l mn p f xs ys

(* Appending *)

(* The natural operation is to append a forwards vector to a backwards one. *)
let rec append : type a m n mn. (m, n, mn) Fwn.bplus -> (a, m) t -> (a, n) Vec.t -> (a, mn) t =
 fun mn xs ys ->
  match (mn, ys) with
  | Zero, [] -> xs
  | Suc mn, y :: ys -> append mn (Snoc (xs, y)) ys

(* Or prepend a backwards vector to a forwards one. *)
let rec prepend : type a m n mn. (m, n, mn) Fwn.fplus -> (a, m) t -> (a, n) Vec.t -> (a, mn) Vec.t =
 fun mn xs ys ->
  match (mn, xs) with
  | Zero, Emp -> ys
  | Suc mn, Snoc (xs, x) -> prepend mn xs (x :: ys)

(* But we can also append one Bwv to another *)
let rec bappend : type a m n mn. (m, n, mn) N.plus -> (a, m) t -> (a, n) t -> (a, mn) t =
 fun mn xs ys ->
  match (mn, ys) with
  | Zero, Emp -> xs
  | Suc mn, Snoc (ys, y) -> Snoc (bappend mn xs ys, y)

(* We can split a Bwv of length m+n into one of length m and one of length n. *)
let rec unappend : type a m n mn. (m, n, mn) N.plus -> (a, mn) t -> (a, m) t * (a, n) t =
 fun mn xys ->
  match mn with
  | Zero -> (xys, Emp)
  | Suc mn -> (
      match xys with
      | Snoc (xys, y) ->
          let xs, ys = unappend mn xys in
          (xs, Snoc (ys, y)))

(* Folds *)

(* As noted in mlist, these could be defined in terms of the monadic iterator iterM using the state and continuation monads. *)

let rec fold_left : type n a b. (a -> b -> a) -> a -> (b, n) t -> a =
 fun f start xs ->
  match xs with
  | Emp -> start
  | Snoc (xs, x) -> f (fold_left f start xs) x

let rec fold_right : type n a b. (a -> b -> b) -> (a, n) t -> b -> b =
 fun f xs start ->
  match xs with
  | Emp -> start
  | Snoc (xs, x) -> fold_right f xs (f x start)

let rec fold_left2 : type n a b c. (a -> b -> c -> a) -> a -> (b, n) t -> (c, n) t -> a =
 fun f start xs ys ->
  match (xs, ys) with
  | Emp, Emp -> start
  | Snoc (xs, x), Snoc (ys, y) -> f (fold_left2 f start xs ys) x y

(* A version of fold_left where the accumulator type 'a is itself replaced by a vector, which starts at length m and results of length m+n.  This requires that the function being applied at each step is polymorphic over the length of the vector, and hence it must be wrapped in a record.  *)

type ('a, 'b) fold_left_mapper = { fold : 'n. ('a, 'n) t -> 'b -> 'a }

let rec fold_left_map_append : type m n mn a b.
    (m, n, mn) N.plus -> (a, b) fold_left_mapper -> (a, m) t -> (b, n) t -> (a, mn) t =
 fun mn f start xs ->
  match (mn, xs) with
  | Zero, Emp -> start
  | Suc mn, Snoc (xs, x) ->
      let zs = fold_left_map_append mn f start xs in
      Snoc (zs, f.fold zs x)

type ('a, 'b, 'c) fold_left2_mapper = { fold : 'n. ('a, 'n) t -> 'b -> 'c -> 'a }

let rec fold_left2_map_append : type m n mn a b c.
    (m, n, mn) N.plus ->
    (a, b, c) fold_left2_mapper ->
    (a, m) t ->
    (b, n) t ->
    (c, n) t ->
    (a, mn) t =
 fun mn f start xs ys ->
  match (mn, xs, ys) with
  | Zero, Emp, Emp -> start
  | Suc mn, Snoc (xs, x), Snoc (ys, y) ->
      let zs = fold_left2_map_append mn f start xs ys in
      Snoc (zs, f.fold zs x y)

let rec fold_left_bind_append : type k m n mn k_mn a c.
    (m, n, mn) N.times ->
    (k, mn, k_mn) N.plus ->
    (a, c) fold_left_mapper ->
    (a, k) t ->
    ((c, m) t, n) t ->
    (a, k_mn) t =
 fun mn k_mn f acc xs ->
  match (mn, xs) with
  | Zero _, Emp ->
      let Eq = N.plus_uniq k_mn Zero in
      acc
  | Suc (mn', mn'_m), Snoc (xs, x) ->
      let (Plus k_mn') = N.plus (N.times_out mn') in
      let k_mn'__m = N.plus_assocl k_mn' mn'_m k_mn in
      fold_left_map_append k_mn'__m f (fold_left_bind_append mn' k_mn' f acc xs) x

type ('a, 'b, 'c, 'm) fold_left2_bind_appender = {
  append : 'n 'nm. ('n, 'm, 'nm) N.plus -> ('a, 'n) t -> 'b -> 'c -> ('a, 'nm) t;
}

let rec fold_left2_bind_append : type k m n mn k_mn a b c.
    (m, n, mn) N.times ->
    (k, mn, k_mn) N.plus ->
    (a, k) t ->
    (b, n) t ->
    (c, n) t ->
    (a, b, c, m) fold_left2_bind_appender ->
    (a, k_mn) t =
 fun mn k_mn acc xs ys g ->
  match (mn, xs, ys) with
  | Zero _, Emp, Emp ->
      let Eq = N.plus_uniq k_mn Zero in
      acc
  | Suc (mn', mn'_m), Snoc (xs, x), Snoc (ys, y) ->
      let (Plus k_mn') = N.plus (N.times_out mn') in
      let k_mn'__m = N.plus_assocl k_mn' mn'_m k_mn in
      g.append k_mn'__m (fold_left2_bind_append mn' k_mn' acc xs ys g) x y

type ('a, 'b, 'c, 'd, 'm) fold_left2_bind_append_mapper = {
  append : 'n 'nm. ('n, 'm, 'nm) N.plus -> ('a, 'n) t -> 'b -> 'c -> ('a, 'nm) t * 'd;
}

let rec fold_left2_bind_append_map : type k m n mn k_mn a b c d.
    (m, n, mn) N.times ->
    (k, mn, k_mn) N.plus ->
    (a, k) t ->
    (b, n) t ->
    (c, n) t ->
    (a, b, c, d, m) fold_left2_bind_append_mapper ->
    (a, k_mn) t * (d, n) t =
 fun mn k_mn acc xs ys g ->
  match (mn, xs, ys) with
  | Zero _, Emp, Emp ->
      let Eq = N.plus_uniq k_mn Zero in
      (acc, Emp)
  | Suc (mn', mn'_m), Snoc (xs, x), Snoc (ys, y) ->
      let (Plus k_mn') = N.plus (N.times_out mn') in
      let k_mn'__m = N.plus_assocl k_mn' mn'_m k_mn in
      let res1, res2 = fold_left2_bind_append_map mn' k_mn' acc xs ys g in
      let res1', z = g.append k_mn'__m res1 x y in
      (res1', Snoc (res2, z))

(* Conversely, a vector of length m*n can be split into a length-n vector of length-m vectors. *)
let rec unbind : type b m n mn. (m, n, mn) N.times -> (b, mn) t -> ((b, m) t, n) t =
 fun mn xss ->
  match mn with
  | Zero _ -> Emp
  | Suc (mn, mnm) ->
      let xss, xs = unappend mnm xss in
      Snoc (unbind mn xss, xs)

(* Ensure that a Bwd has exactly a specified number of elements and return them in a Bwv of that length, returning None if the Bwd has too many or too few elements. *)
let rec of_bwd : type a n. a Bwd.t -> n N.t -> (a, n) t option =
 fun xs n ->
  let open Monad.Ops (Monad.Maybe) in
  match (xs, n) with
  | Emp, Nat Zero -> Some Emp
  | Snoc (xs, x), Nat (Suc n) ->
      let* xs' = of_bwd xs (Nat n) in
      Some (Snoc (xs', x))
  | _ -> None

(* As befits backwards vectors and lists, this takes n elements from the *right* of a Bwd to form a Bwv, returning the remaining elements along with the Bwv. *)
let rec take_bwd : type a n. n N.t -> a Bwd.t -> a Bwd.t * (a, n) t =
 fun n xs ->
  match (n, xs) with
  | Nat Zero, _ -> (xs, Emp)
  | Nat (Suc n), Snoc (xs, x) ->
      let rest, taken = take_bwd (Nat n) xs in
      (rest, Snoc (taken, x))
  | _ -> raise Not_found

(* Converting to a Bwd *)
let rec to_bwd_map : type a b n. (a -> b) -> (a, n) t -> b Bwd.t =
 fun f xs ->
  match xs with
  | Emp -> Emp
  | Snoc (xs, x) -> Snoc (to_bwd_map f xs, f x)

let to_bwd : type a n. (a, n) t -> a Bwd.t = fun xs -> to_bwd_map (fun x -> x) xs

let rec prepend_map : type a b n. (a -> b) -> (a, n) t -> b list -> b list =
 fun f xs ys ->
  match xs with
  | Emp -> ys
  | Snoc (xs, x) -> prepend_map f xs (f x :: ys)

let to_list_map : type a b n. (a -> b) -> (a, n) t -> b list = fun f xs -> prepend_map f xs []
let to_list : type a n. (a, n) t -> a list = fun xs -> to_list_map (fun x -> x) xs

type _ wrapped = Wrap : ('a, 'n) t -> 'a wrapped

let rec append_list_map : type a b n. (a -> b) -> (b, n) t -> a list -> b wrapped =
 fun f xs ys ->
  match ys with
  | [] -> Wrap xs
  | y :: ys -> append_list_map f (Snoc (xs, f y)) ys

let of_list_map : type a b. (a -> b) -> a list -> b wrapped = fun f ys -> append_list_map f Emp ys

let append_list : type a n. (a, n) t -> a list -> a wrapped =
 fun xs ys -> append_list_map (fun x -> x) xs ys

type (_, _) append_plus =
  | Append_plus : ('n, 'm, 'nm) Fwn.bplus * ('a, 'm) Vec.t * ('a, 'nm) t -> ('a, 'n) append_plus

let rec append_plus : type a n. (a, n) t -> a list -> (a, n) append_plus =
 fun ctx vars ->
  match vars with
  | [] -> Append_plus (Zero, [], ctx)
  | x :: xs ->
      let (Append_plus (nm, ys, ctx)) = append_plus (Snoc (ctx, x)) xs in
      Append_plus (Suc nm, x :: ys, ctx)
