open Util
open Dim
open Term

type _ tree =
  | Lam : ('k, 'f) count_faces * ('a, 'f, 'af) N.plus * 'af tree ref -> 'a tree
  | Leaf : 'a term -> 'a tree
  | Branches : 'a N.index * 'a branch Constr.Map.t -> 'a tree
  | Cobranches : 'a tree ref Field.Map.t -> 'a tree
  | Empty : 'a tree

and _ branch = Branch : ('a, 'b, 'ab) N.plus * 'ab tree ref -> 'a branch
