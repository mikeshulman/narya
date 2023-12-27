open Dim
open Term
open Hctx

type _ tree =
  (* As in a term, a lambda binds a full cube of variables, although we might allow the user to specify one variable that represents the full cube. *)
  | Lam : 'n D.t * 'n variables * ('a, 'n) ext tree ref -> 'a tree
  | Leaf : 'a term -> 'a tree
  | Branches : 'a index * 'n D.t * ('a, 'n) branch Constr.Map.t -> 'a tree
  | Cobranches : 'a tree ref Field.Map.t -> 'a tree
  | Empty : 'a tree

(* A branch of a match binds a number of new variables.  If it is a higher-dimensional match, then each of those "variables" is actually a full cube of variables. *)
and (_, _) branch = Branch : ('a, 'b, 'ab, 'n) exts * 'ab tree ref -> ('a, 'n) branch
