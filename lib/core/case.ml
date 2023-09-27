open Util
open Term

type _ tree =
  | Lam : 'a N.suc tree -> 'a tree
  | Leaf : 'a term -> 'a tree
  | Branches : 'a N.index * 'a branch list -> 'a tree
  | Cobranches : 'a tree Field.Map.t -> 'a tree

and _ branch = Branch : Constr.t * ('a, 'b, 'ab) N.plus * 'ab tree -> 'a branch
