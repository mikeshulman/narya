(* Forwards vectors, indexed by type-level forwards natural numbers.  This module should not be opened, but used qualified. *)

type (_, _) t = [] : ('a, Fwn.zero) t | ( :: ) : 'a * ('a, 'n) t -> ('a, 'n Fwn.suc) t

let nil : type a. (a, Fwn.zero) t = []
let cons : type a n. a -> (a, n) t -> (a, n Fwn.suc) t = fun x xs -> x :: xs

let rec map : type a b n. (a -> b) -> (a, n) t -> (b, n) t =
 fun f xs ->
  match xs with
  | [] -> []
  | x :: xs -> f x :: map f xs
