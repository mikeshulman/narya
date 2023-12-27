open Bwd
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

(* Find the name of the (n+1)st abstracted variable, where n is the length of a supplied argument list.  Doesn't "look through" branches or cobranches or into leaves. *)
let rec nth_var : type a b. a tree -> b Bwd.t -> any_variables option =
 fun tr args ->
  match tr with
  | Lam (_, x, body) -> (
      match args with
      | Emp -> Some (Any x)
      | Snoc (args, _) -> nth_var !body args)
  | _ -> None
