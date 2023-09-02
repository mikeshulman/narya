open Bwd

(* ********************
   Parse Trees
   *********************)

type 'n t = Leaf of string | Node of 'n * 'n t Bwd.t

let leaf x : 'notn t = Leaf x
let node x y : 'notn t = Node (x, y)

let rec map (f : 'a -> 'b) (tr : 'a t) : 'b t =
  match tr with
  | Leaf str -> Leaf str
  | Node (n, kids) -> Node (f n, Bwd.map (map f) kids)
