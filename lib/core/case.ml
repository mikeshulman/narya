open Util
open Term

type _ tree =
  | Lam : ('a, 'b, 'ab) N.plus * 'ab tree -> 'a tree
  | Leaf : 'a term -> 'a tree
  | Branch : 'a N.index * 'a branch list -> 'a tree
  | Cobranch : (Field.t * 'a tree) list -> 'a tree

and _ branch =
  | Branch : Constant.t * ('b, 'c) N.subset * ('a, 'b, 'ab) N.plus * 'ab tree -> 'a branch
