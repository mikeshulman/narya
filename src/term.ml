open Dim

(* Typechecked, but unevaluated, terms.  Still using intrinsically well-scoped De Bruijn indices, but no longer separated by synthesizing/checking, hence without type ascriptions.

   Incorporates information appropriate to the internal syntax that is constructed during typechecking, e.g. applications and abstractions are grouped by a dimension, since this can be inferred during typechecking, from the synthesized type of a function being applied and from the pi-type the lambda is being checked against, respectively.  Similarly, we have instantiations of higher-dimensional types obtained by applying them to a tube of boundary terms.

   On the other hand, pi-types are still only unary: higher-dimensional pi-types are created only in internal values by substitution and operator action.  Similarly, there is still only one (zero-dimensional) universe, and the only operator actions are refl and sym. *)

type _ term =
  | Var : 'a N.index -> 'a term
  | Const : Constant.t -> 'a term
  | Field : 'a term * Field.t -> 'a term
  | UU : 'a term
  | Inst : 'a term * ('m, 'n, 'mn, 'a term) TubeOf.t -> 'a term
  | Pi : 'a term * 'a N.suc term -> 'a term
  | App : 'a term * ('n, 'a term) CubeOf.t -> 'a term
  | Lam : ('n, 'f) count_faces * ('a, 'f, 'af) N.plus * 'af term -> 'a term
  | Struct : 'a term Field.Map.t -> 'a term
  | Refl : 'a term -> 'a term
  | Sym : 'a term -> 'a term
