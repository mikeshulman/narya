open Bwd
open Util
open Dim

(* Typechecked, but unevaluated, terms.  Still using intrinsically well-scoped De Bruijn indices, but no longer separated by synthesizing/checking, hence without type ascriptions.

   Incorporates information appropriate to the internal syntax that is constructed during typechecking, e.g. applications and abstractions are grouped by a dimension, since this can be inferred during typechecking, from the synthesized type of a function being applied and from the pi-type the lambda is being checked against, respectively.  Similarly, we have instantiations of higher-dimensional types obtained by applying them to a tube of boundary terms.

   Typechecking of user syntax still produces only unary pi-types and zero-dimensional universes, but we include arbitrary-dimensional ones here so that they can also be the output of readback from internal values.  The only operator actions are refl and sym. *)

(* The codomain of a higher-dimensional pi-type is a cube of terms with bound variables whose number varies with the face of the cube.  We can enforce this with a parametrized instance of Cube, but it has to be defined recursively with term using a recursive module (like BindCube in Value; see there for more commentary). *)
module rec Term : sig
  type ('k, 'a) binder =
    | Bind : ('k, 'f) count_faces * ('a, 'f, 'af) N.plus * 'af Term.term -> ('k, 'a) binder

  module CodFam : sig
    type ('k, 'a) t = ('k, 'a) binder
  end

  module CodCube : module type of Cube (CodFam)

  type _ term =
    | Var : 'a N.index -> 'a term
    | Const : Constant.t -> 'a term
    | Field : 'a term * Field.t -> 'a term
    | UU : 'n D.t -> 'a term
    | Inst : 'a term * ('m, 'n, 'mn, 'a term) TubeOf.t -> 'a term
    | Pi : ('n, 'a term) CubeOf.t * ('n, 'a) CodCube.t -> 'a term
    | App : 'a term * ('n, 'a term) CubeOf.t -> 'a term
    | Lam : ('n, 'a) binder -> 'a term
    | Struct : 'a term Field.Map.t -> 'a term
    | Constr : Constr.t * 'n D.t * ('n, 'a term) CubeOf.t Bwd.t -> 'a term
    | Act : 'a term * ('m, 'n) deg -> 'a term
    | Let : 'a term * 'a N.suc term -> 'a term
end = struct
  type ('k, 'a) binder =
    | Bind : ('k, 'f) count_faces * ('a, 'f, 'af) N.plus * 'af Term.term -> ('k, 'a) binder

  module CodFam = struct
    type ('k, 'a) t = ('k, 'a) binder
  end

  module CodCube = Cube (CodFam)

  type _ term =
    | Var : 'a N.index -> 'a term
    | Const : Constant.t -> 'a term (* TODO: Should separate out canonicals? *)
    | Field : 'a term * Field.t -> 'a term
    | UU : 'n D.t -> 'a term
    | Inst : 'a term * ('m, 'n, 'mn, 'a term) TubeOf.t -> 'a term
    | Pi : ('n, 'a term) CubeOf.t * ('n, 'a) CodCube.t -> 'a term
    | App : 'a term * ('n, 'a term) CubeOf.t -> 'a term
    | Lam : ('n, 'a) binder -> 'a term
    | Struct : 'a term Field.Map.t -> 'a term
    | Constr : Constr.t * 'n D.t * ('n, 'a term) CubeOf.t Bwd.t -> 'a term
    | Act : 'a term * ('m, 'n) deg -> 'a term
    | Let : 'a term * 'a N.suc term -> 'a term
end

include Term

let rec term_lam : type a b ab. (a, b, ab) N.plus -> ab term -> a term =
 fun ab tm ->
  match ab with
  | Zero -> tm
  | Suc ab -> term_lam ab (Lam (Bind (faces_zero, Suc Zero, tm)))

let pi dom cod = Pi (CubeOf.singleton dom, CodCube.singleton (Bind (faces_zero, Suc Zero, cod)))
let app fn arg = App (fn, CubeOf.singleton arg)
let apps fn args = List.fold_left app fn args
let constr name args = Constr (name, D.zero, Bwd.map CubeOf.singleton args)
