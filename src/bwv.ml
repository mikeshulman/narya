(* Snoc vectors, indexed by type-level natural numbers.  This module should not be opened, but used qualified. *)

(* An ('a, 'n) Bwv.t is a vector of length 'n of elements of type 'a. *)
type (_, _) t = Emp : ('a, N.zero) t | Snoc : ('a, 'n) t * 'a -> ('a, 'n N.suc) t

let emp : type a. (a, N.zero) t = Emp
let snoc : type a n. (a, n) t -> a -> (a, n N.suc) t = fun xs x -> Snoc (xs, x)

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
    | Suc _, y :: ys -> of_list (N.suc_plus'' n) (Snoc (xs, y)) ys
    | _ -> None in
  of_list (N.zero_plus n) Emp ys

(* Find the rightmost occurrence of an element in a vector, if any, and return its De Bruijn index. *)
let rec index : type a n. a -> (a, n) t -> n N.index option =
 fun y -> function
  | Emp -> None
  | Snoc (xs, x) -> if x = y then Some Top else Option.map (fun z -> N.Pop z) (index y xs)

(* Mapping and iterating over vectors *)

let rec map : type a b n. (a -> b) -> (a, n) t -> (b, n) t =
 fun f -> function
  | Emp -> Emp
  | Snoc (xs, x) -> Snoc (map f xs, f x)

let rec map_plus : type a b m n mn. (m, n, mn) N.plus -> (a -> b) -> (a, mn) t -> (b, m) t =
 fun mn f xs ->
  match mn with
  | Zero -> map f xs
  | Suc mn -> (
      match xs with
      | Snoc (xs, _) -> map_plus mn f xs)

let rec map2 : type a b c n. (a -> b -> c) -> (a, n) t -> (b, n) t -> (c, n) t =
 fun f xs ys ->
  match (xs, ys) with
  | Emp, Emp -> Emp
  | Snoc (xs, x), Snoc (ys, y) -> Snoc (map2 f xs ys, f x y)

let rec map3 : type a b c d n. (a -> b -> c -> d) -> (a, n) t -> (b, n) t -> (c, n) t -> (d, n) t =
 fun f xs ys zs ->
  match (xs, ys, zs) with
  | Emp, Emp, Emp -> Emp
  | Snoc (xs, x), Snoc (ys, y), Snoc (zs, z) -> Snoc (map3 f xs ys zs, f x y z)

let rec map2_plus :
    type a b c m n mn. (m, n, mn) N.plus -> (a -> b -> c) -> (a, mn) t -> (b, m) t -> (c, m) t =
 fun mn f xs ys ->
  match mn with
  | Zero -> map2 f xs ys
  | Suc mn -> (
      match xs with
      | Snoc (xs, _) -> map2_plus mn f xs ys)

let rec iter : type a n. (a -> unit) -> (a, n) t -> unit =
 fun f -> function
  | Emp -> ()
  | Snoc (xs, x) ->
      iter f xs;
      f x

let rec iter2 : type a b n. (a -> b -> unit) -> (a, n) t -> (b, n) t -> unit =
 fun f xs ys ->
  match (xs, ys) with
  | Emp, Emp -> ()
  | Snoc (xs, x), Snoc (ys, y) ->
      iter2 f xs ys;
      f x y

let rec iter2_plus :
    type a b m n mn. (m, n, mn) N.plus -> (a -> b -> unit) -> (a, mn) t -> (b, m) t -> unit =
 fun mn f xs ys ->
  match mn with
  | Zero -> iter2 f xs ys
  | Suc mn -> (
      match xs with
      | Snoc (xs, _) -> iter2_plus mn f xs ys)

(* Find an element in one Bwv satisfying a predicate, if one exists, and return a function of the element and length of the remaining vector at the same (backwards) index of another, possibly longer, Bwv. *)
let rec find2l :
    type m n mn a b c.
    (m, n, mn) N.plus -> (a -> bool) -> (int -> b -> c) -> (a, n) t -> (b, mn) t -> c option =
 fun mn p f xs ys ->
  match (mn, xs, ys) with
  | Zero, _, _ -> None
  | Suc mn, Snoc (xs, x), Snoc (ys, y) ->
      if p x then Some (f (N.to_int (length ys)) y) else find2l mn p f xs ys

(* Amusingly, appending *reversed* vectors is a closer match to addition of natural numbers defined by recursion on its right argument that appending non-reversed vectors would be. *)
let rec append : type a m n mn. (m, n, mn) N.plus -> (a, m) t -> (a, n) t -> (a, mn) t =
 fun mn xs ys ->
  match (mn, ys) with
  | Zero, Emp -> xs
  | Suc mn, Snoc (ys, y) -> Snoc (append mn xs ys, y)

(* Conversely, we can split a vector of length m+n into one of length m and one of length n. *)
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

let rec fold2_left : type n a b c. (a -> b -> c -> a) -> a -> (b, n) t -> (c, n) t -> a =
 fun f start xs ys ->
  match (xs, ys) with
  | Emp, Emp -> start
  | Snoc (xs, x), Snoc (ys, y) -> f (fold2_left f start xs ys) x y

(* A version of fold2_left where the accumulator type 'a is itself replaced by a vector, which starts at length m and results of length m+n.  This requires that the function being applied at each step is polymorphic over the length of the vector, and hence it must be wrapped in a record.  *)
type ('a, 'b, 'c) fold2_left_mapper = { f : 'n. ('a, 'n) t -> 'b -> 'c -> 'a }

let rec fold2_left_map_append :
    type m n mn a b c.
    (m, n, mn) N.plus ->
    (a, b, c) fold2_left_mapper ->
    (a, m) t ->
    (b, n) t ->
    (c, n) t ->
    (a, mn) t =
 fun mn f start xs ys ->
  match (mn, xs, ys) with
  | Zero, Emp, Emp -> start
  | Suc mn, Snoc (xs, x), Snoc (ys, y) ->
      let zs = fold2_left_map_append mn f start xs ys in
      Snoc (zs, f.f zs x y)

(* Constant-length bind: given a vector of elements of 'a of length n, and a function mapping 'a to vectors of type 'b of length m, we get a vector of type 'b of length m*n.  *)
let rec bind : type a b m n mn. (m, n, mn) N.times -> (a, n) t -> (a -> (b, m) t) -> (b, mn) t =
 fun mn xs f ->
  match (mn, xs) with
  | Zero _, Emp -> Emp
  | Suc (mn, mnm), Snoc (xs, x) -> append mnm (bind mn xs f) (f x)

(* Conversely, a vector of length m*n can be split into a length-n vector of length-m vectors. *)
let rec unbind : type a b m n mn. (m, n, mn) N.times -> (b, mn) t -> ((b, m) t, n) t =
 fun mn xss ->
  match mn with
  | Zero _ -> Emp
  | Suc (mn, mnm) ->
      let xss, xs = unappend mnm xss in
      Snoc (unbind mn xss, xs)
