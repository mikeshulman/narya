(* Heterogeneous lists, parametrized by a type-level list that specifies the types of their elements. *)

(* The constructors of type-level lists *)
type nil = Dummy_nil
type ('x, 'xs) cons = Dummy_cons

(* A predicate for "being a type-level list" *)
type _ tlist = Nil : nil tlist | Cons : 'xs tlist -> ('x, 'xs) cons tlist

(* A heterogeneous list of elements of some type-level list *)
type _ hlist = [] : nil hlist | ( :: ) : 'x * 'xs hlist -> ('x, 'xs) cons hlist

let nil : nil hlist = []
let cons : type x xs. x -> xs hlist -> (x, xs) cons hlist = fun x xs -> x :: xs

(* Every hlist has a valid type *)
let rec tlist_of_hlist : type xs. xs hlist -> xs tlist = function
  | [] -> Nil
  | _ :: xs -> Cons (tlist_of_hlist xs)
