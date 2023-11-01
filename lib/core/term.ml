open Bwd
open Dim
open Hctx

(* Typechecked, but unevaluated, terms.  Use De Bruijn indices that are intrinsically well-scoped by hctxs, but are no longer separated into synthesizing and checking; hence without type ascriptions.  Note that extending an hctx by a dimension 'k means adding a whole cube of new variables, which are indexed by the position of that dimension together with a strict face of it.  (At user-level, those variables may all be accessed as faces of one "cube variable", or they may have independent names, but internally there is no difference.)

   Incorporates information appropriate to the internal syntax that is constructed during typechecking, e.g. applications and abstractions are grouped by a dimension, since this can be inferred during typechecking, from the synthesized type of a function being applied and from the pi-type the lambda is being checked against, respectively.  Similarly, we have instantiations of higher-dimensional types obtained by applying them to a tube of boundary terms.

   Typechecking of user syntax still produces only unary pi-types and zero-dimensional universes, but we include arbitrary-dimensional ones here so that they can also be the output of readback from internal values.  We likewise include arbitrary degeneracy actions, since these can appear in readback. *)

(* The codomain of a higher-dimensional pi-type is a cube of terms with bound variables whose number varies with the face of the cube.  We can enforce this with a parametrized instance of Cube, but it has to be defined recursively with term using a recursive module (like BindCube in Value; see there for more commentary). *)
module rec Term : sig
  module CodFam : sig
    type ('k, 'a) t = ('a, 'k) ext Term.term
  end

  module CodCube : module type of Cube (CodFam)

  type _ term =
    | Var : 'a index -> 'a term
    | Const : Constant.t -> 'a term
    | Field : 'a term * Field.t -> 'a term
    | UU : 'n D.t -> 'a term
    | Inst : 'a term * ('m, 'n, 'mn, 'a term) TubeOf.t -> 'a term
    | Pi : ('n, 'a term) CubeOf.t * ('n, 'a) CodCube.t -> 'a term
    | App : 'a term * ('n, 'a term) CubeOf.t -> 'a term
    | Lam : 'n D.t * ('a, 'n) ext Term.term -> 'a term
    | Struct : 'a term Field.Map.t -> 'a term
    | Constr : Constr.t * 'n D.t * ('n, 'a term) CubeOf.t Bwd.t -> 'a term
    | Act : 'a term * ('m, 'n) deg -> 'a term
    | Let : 'a term * ('a, D.zero) ext term -> 'a term
end = struct
  module CodFam = struct
    type ('k, 'a) t = ('a, 'k) ext Term.term
  end

  module CodCube = Cube (CodFam)

  type _ term =
    | Var : 'a index -> 'a term
    | Const : Constant.t -> 'a term (* TODO: Should separate out canonicals? *)
    | Field : 'a term * Field.t -> 'a term
    | UU : 'n D.t -> 'a term
    | Inst : 'a term * ('m, 'n, 'mn, 'a term) TubeOf.t -> 'a term
    | Pi : ('n, 'a term) CubeOf.t * ('n, 'a) CodCube.t -> 'a term
    | App : 'a term * ('n, 'a term) CubeOf.t -> 'a term
    | Lam : 'n D.t * ('a, 'n) ext Term.term -> 'a term
    | Struct : 'a term Field.Map.t -> 'a term
    | Constr : Constr.t * 'n D.t * ('n, 'a term) CubeOf.t Bwd.t -> 'a term
    | Act : 'a term * ('m, 'n) deg -> 'a term
    | Let : 'a term * ('a, D.zero) ext term -> 'a term
end

include Term

let rec term_lam : type a b ab. (a, b, ab, D.zero) exts -> ab term -> a term =
 fun ab tm ->
  match ab with
  | Zero -> tm
  | Suc ab -> term_lam ab (Lam (D.zero, tm))

let pi dom cod = Pi (CubeOf.singleton dom, CodCube.singleton cod)
let app fn arg = App (fn, CubeOf.singleton arg)
let apps fn args = List.fold_left app fn args
let constr name args = Constr (name, D.zero, Bwd.map CubeOf.singleton args)
