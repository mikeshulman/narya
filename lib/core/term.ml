open Bwd
open Util
open Dim
open Hctx

(* ******************** Raw (unchecked) terms ******************** *)

module Raw = struct
  (* Raw (unchecked) terms, using intrinsically well-scoped De Bruijn indices, and separated into synthesizing terms and checking terms.  These match the user-facing syntax rather than the internal syntax.  In particular, applications, abstractions, and pi-types are all unary, there is only one universe, and the only operator actions are refl (including Id) and sym. *)

  (* A raw De Bruijn index is a well-scoped natural number together with a possible face.  During typechecking we will verify that the face, if given, is applicable to the variable as a "cube variable", and compile the combination into a more strongly well-scoped kind of index. *)
  type 'a index = 'a N.index * any_sface option

  type _ synth =
    | Var : 'a index -> 'a synth
    | Const : Constant.t -> 'a synth
    | Field : 'a synth * Field.t -> 'a synth
    | Pi : string option * 'a check * 'a N.suc check -> 'a synth
    | App : 'a synth * 'a check -> 'a synth
    | Asc : 'a check * 'a check -> 'a synth
    | Let : string option * 'a synth * 'a N.suc synth -> 'a synth
    | UU : 'a synth
    | Act : string * ('m, 'n) deg * 'a synth -> 'a synth

  and _ check =
    | Synth : 'a synth -> 'a check
    | Lam : string option * [ `Cube | `Normal ] * 'a N.suc check -> 'a check
    | Struct : 'a check Field.Map.t -> 'a check
    | Constr : Constr.t * 'a check Bwd.t -> 'a check
    | Match : 'a index * 'a branch list -> 'a check

  and _ branch = Branch : Constr.t * ('a, 'b, 'ab) N.plus * 'ab check -> 'a branch

  let rec raw_lam :
      type a b ab.
      (string option, ab) Bwv.t -> [ `Cube | `Normal ] -> (a, b, ab) N.plus -> ab check -> a check =
   fun names cube ab tm ->
    match (names, ab) with
    | _, Zero -> tm
    | Snoc (names, x), Suc ab -> raw_lam names cube ab (Lam (x, cube, tm))
end

(* ******************** Names ******************** *)

type 'n variables = [ `Normal of ('n, string option) CubeOf.t | `Cube of string option ]
type any_variables = Any : 'n variables -> any_variables

let singleton_variables : type n. n D.t -> string option -> n variables =
 fun n x ->
  match compare n D.zero with
  | Eq -> `Normal (CubeOf.singleton x)
  | Neq -> `Cube x

let singleton_named_variables : type n. n D.t -> string option -> n variables =
 fun n x ->
  let x = Option.value x ~default:"x" in
  match compare n D.zero with
  | Eq -> `Normal (CubeOf.singleton (Some x))
  | Neq -> `Cube (Some x)

(* ******************** Typechecked terms ******************** *)

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
    (* Since the user doesn't write higher-dimensional pi-types explicitly, there is always only one variable name. *)
    | Pi : string option * ('n, 'a term) CubeOf.t * ('n, 'a) CodCube.t -> 'a term
    | App : 'a term * ('n, 'a term) CubeOf.t -> 'a term
    | Lam : 'n D.t * 'n variables * ('a, 'n) ext Term.term -> 'a term
    | Struct : 'a term Field.Map.t -> 'a term
    | Constr : Constr.t * 'n D.t * ('n, 'a term) CubeOf.t Bwd.t -> 'a term
    | Act : 'a term * ('m, 'n) deg -> 'a term
    | Let : string option * 'a term * ('a, D.zero) ext term -> 'a term
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
    | Pi : string option * ('n, 'a term) CubeOf.t * ('n, 'a) CodCube.t -> 'a term
    | App : 'a term * ('n, 'a term) CubeOf.t -> 'a term
    | Lam : 'n D.t * 'n variables * ('a, 'n) ext Term.term -> 'a term
    | Struct : 'a term Field.Map.t -> 'a term
    | Constr : Constr.t * 'n D.t * ('n, 'a term) CubeOf.t Bwd.t -> 'a term
    | Act : 'a term * ('m, 'n) deg -> 'a term
    | Let : string option * 'a term * ('a, D.zero) ext term -> 'a term
end

include Term

let pi x dom cod = Pi (x, CubeOf.singleton dom, CodCube.singleton cod)
let app fn arg = App (fn, CubeOf.singleton arg)
let apps fn args = List.fold_left app fn args
let constr name args = Constr (name, D.zero, Bwd.map CubeOf.singleton args)
