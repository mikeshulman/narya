open Bwd
open Util
open Dim
open Hctx

type eta = [ `Eta | `Noeta ]

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

open Term

let pi x dom cod = Pi (x, CubeOf.singleton dom, CodCube.singleton cod)
let app fn arg = App (fn, CubeOf.singleton arg)
let apps fn args = List.fold_left app fn args
let constr name args = Constr (name, D.zero, Bwd.map CubeOf.singleton args)

(* ******************** Values ******************** *)

(* Internal values, the result of evaluation, with closures for abstractions.  Use De Bruijn *levels*, so that weakening is implicit.  Fully internal unbiased syntax lives here: in addition to higher-dimensional applications and abstractions, we also have higher-dimensional pi-types, higher-dimensional universes, and instantiations of higher-dimensional types.  Separated into neutrals and normals, so that there are no beta-redexes.  Explicit substitutions (environments) are stored on binders, for NBE. *)

(* The codomains of a pi-type are stored as a Cube of binders, and since binders are a type family this dependence has to be specified by applying a module functor (rather than just parametrizing a type).  Since values are defined mutually with binders, we need to "apply the functor Cube" mutually with the definition of these types.  This is possible using a recursive module. *)
module rec Value : sig
  (* A recursive module is required to specify its module type explicitly.  We make this as transparent as possible, so the module type is nearly a copy of the module itself.  For the comments, see the actual definition below. *)
  module BindFam : sig
    type ('k, 'b) t = 'k Value.binder
  end

  module BindCube : module type of Cube (BindFam)

  type head =
    | Var : { level : level; deg : ('m, 'n) deg } -> head
    | Const : { name : Constant.t; dim : 'n D.t } -> head

  and 'n arg = Arg of ('n, normal) CubeOf.t | Field of Field.t
  and app = App : 'n arg * ('m, 'n, 'k) insertion -> app

  and _ binder =
    | Bind : {
        env : ('m, 'a) env;
        perm : 'mn perm;
        plus_dim : ('m, 'n, 'mn) D.plus;
        body : ('a, 'n) ext term;
        args : ('n, ('m, 'mn face_of) CubeOf.t) CubeOf.t;
      }
        -> 'mn binder

  and uninst =
    | UU : 'n D.t -> uninst
    | Pi : string option * ('k, value) CubeOf.t * ('k, unit) BindCube.t -> uninst
    | Neu : head * app Bwd.t -> uninst
    | Canonical : Constant.t * ('n, normal) CubeOf.t Bwd.t * ('m, 'n, 'k) insertion -> uninst

  and value =
    | Uninst : uninst * value Lazy.t -> value
    | Inst : {
        tm : uninst;
        dim : 'k D.pos;
        args : ('n, 'k, 'nk, normal) TubeOf.t;
        tys : (D.zero, 'n, 'n, value) TubeOf.t;
      }
        -> value
    | Lam : 'k variables * 'k binder -> value
    | Struct : value Field.Map.t * ('m, 'n, 'k) insertion -> value
    | Constr : Constr.t * 'n D.t * ('n, value) CubeOf.t Bwd.t -> value

  and normal = { tm : value; ty : value }

  and (_, _) env =
    | Emp : 'n D.t -> ('n, emp) env
    | Ext : ('n, 'b) env * ('k, ('n, value) CubeOf.t) CubeOf.t -> ('n, ('b, 'k) ext) env
    | Act : ('n, 'b) env * ('m, 'n) op -> ('m, 'b) env
end = struct
  (* Here is the recursive application of the functor Cube.  First we define a module to pass as its argument, with type defined to equal the yet-to-be-defined binder, referred to recursively. *)
  module BindFam = struct
    type ('k, 'b) t = 'k Value.binder
  end

  module BindCube = Cube (BindFam)

  (* The head of an elimination spine is either a variable or a constant. *)
  type head =
    (* A variable is determined by a De Bruijn LEVEL, and stores a neutral degeneracy applied to it. *)
    | Var : { level : level; deg : ('m, 'n) deg } -> head
    (* A constant occurs at a specified dimension. *)
    | Const : { name : Constant.t; dim : 'n D.t } -> head

  (* An application contains the data of an n-dimensional argument and its boundary, together with a neutral insertion applied outside that can't be pushed in.  This represents the *argument list* of a single application, not the function.  Thus, an application spine will be a head together with a list of apps. *)
  and 'n arg =
    | Arg of ('n, normal) CubeOf.t
    (* Fields don't store the dimension explicitly; the same field name is used at all dimensions.  But the dimension is implicitly stored in the insertion that appears on an "app". *)
    | Field of Field.t

  and app = App : 'n arg * ('m, 'n, 'k) insertion -> app

  (* Lambdas and Pis both bind a variable, along with its dependencies.  These are recorded as defunctionalized closures.  Since they are produced by higher-dimensional substitutions and operator actions, the dimension of the binder can be different than the dimension of the environment that closes its body.  Accordingly, in addition to the environment and degeneracy to close its body, we store information about how to map the eventual arguments into the bound variables in the body.  *)
  and _ binder =
    | Bind : {
        env : ('m, 'a) env;
        perm : 'mn perm;
        plus_dim : ('m, 'n, 'mn) D.plus;
        body : ('a, 'n) ext term;
        args : ('n, ('m, 'mn face_of) CubeOf.t) CubeOf.t;
      }
        -> 'mn binder

  (* An (m+n)-dimensional type is "instantiated" by applying it a "boundary tube" to get an m-dimensional type.  This operation is supposed to be functorial in dimensions, so in the normal forms we prevent it from being applied more than once in a row.  We have a separate class of "uninstantiated" values, and then every actual value is instantiated exactly once.  This means that even non-type neutrals must be "instantiated", albeit trivially. *)
  and uninst =
    | UU : 'n D.t -> uninst
    (* Pis must store not just the domain type but all its boundary types.  These domain and boundary types are not fully instantiated.  Note the codomains are stored in a cube of binders. *)
    | Pi : string option * ('k, value) CubeOf.t * ('k, unit) BindCube.t -> uninst
    (* A neutral is an application spine: a head with a list of applications.  Note that when we inject it into 'value' with Uninst below, it also stores its type (as do all the other uninsts).  *)
    | Neu : head * app Bwd.t -> uninst
    (* A canonical type has a name, a degenerated/substituted dimension, and a list of arguments all of that dimension, plus a possible outside insertion like an application.  It can be applied to fewer than the "correct" number of arguments that would be necessary to produce a type.  The dimension is stored implicitly and can be recovered from cod_left_ins.  Note that a canonical type can also have a nonzero "intrinsic" dimension (the main example are the Gel/Glue record types), which appears in the dimension 'k of the insertion; thus if the intrinsic dimension is zero, the insertion must be trivial. *)
    | Canonical : Constant.t * ('n, normal) CubeOf.t Bwd.t * ('m, 'n, 'k) insertion -> uninst

  and value =
    (* An uninstantiated term, together with its type.  The 0-dimensional universe is morally an infinite data structure Uninst (UU 0, (Uninst (UU 0, Uninst (UU 0, ... )))), so we make the type lazy. *)
    | Uninst : uninst * value Lazy.t -> value
    (* A term with some nonzero instantiation *)
    | Inst : {
        (* The uninstantiated term being instantiated *)
        tm : uninst;
        (* Require at least one dimension to be instantiated *)
        dim : 'k D.pos;
        (* The arguments for a tube of some dimensions *)
        args : ('n, 'k, 'nk, normal) TubeOf.t;
        (* The types of the arguments remaining to be supplied.  In other words, the type *of* this instantiation is "Inst (UU k, tys)". *)
        tys : (D.zero, 'n, 'n, value) TubeOf.t;
      }
        -> value
    (* Lambda-abstractions are never types, so they can never be nontrivially instantiated.  Thus we may as well make them values directly. *)
    | Lam : 'k variables * 'k binder -> value
    (* The same is true for anonymous structs.  These have to store an insertion outside, like an application. *)
    | Struct : value Field.Map.t * ('m, 'n, 'k) insertion -> value
    (* A constructor has a name, a dimension, and a list of arguments of that dimension.  It must always be applied to the correct number of arguments (otherwise it can be eta-expanded).  It doesn't have an outer insertion because a primitive datatype is always 0-dimensional (it has higher-dimensional versions, but degeneracies can always be pushed inside these).  *)
    | Constr : Constr.t * 'n D.t * ('n, value) CubeOf.t Bwd.t -> value

  (* A "normal form" is a value paired with its type.  The type is used for eta-expansion and equality-checking. *)
  and normal = { tm : value; ty : value }

  (* This is a context morphism *from* a De Bruijn LEVEL context *to* a (typechecked) De Bruijn INDEX context.  Specifically, an ('n, 'a) env is an 'n-dimensional substitution from a level context to an index context indexed by the hctx 'a.  Since the index context could have some variables that are labeled by integers together with faces, the values also have to allow that. *)
  and (_, _) env =
    | Emp : 'n D.t -> ('n, emp) env
    (* Here the k-cube denotes a "cube variable" consisting of some number of "real" variables indexed by the faces of a k-cube, while each of them has an n-cube of values representing a value and its boundaries. *)
    | Ext : ('n, 'b) env * ('k, ('n, value) CubeOf.t) CubeOf.t -> ('n, ('b, 'k) ext) env
    | Act : ('n, 'b) env * ('m, 'n) op -> ('m, 'b) env
end

open Value

(* Given a De Bruijn level and a type, build the variable of that level having that type. *)
let var : level -> value -> value =
 fun level ty -> Uninst (Neu (Var { level; deg = id_deg D.zero }, Emp), Lazy.from_val ty)

(* Every context morphism has a valid dimension. *)
let rec dim_env : type n b. (n, b) env -> n D.t = function
  | Emp n -> n
  | Ext (e, _) -> dim_env e
  | Act (_, op) -> dom_op op

(* And likewise every binder *)
let dim_binder : type m. m binder -> m D.t = function
  | Bind b -> D.plus_out (dim_env b.env) b.plus_dim

(* Project out a cube or tube of values from a cube or tube of normals *)
let val_of_norm_cube : type n. (n, normal) CubeOf.t -> (n, value) CubeOf.t =
 fun arg -> CubeOf.mmap { map = (fun _ [ { tm; ty = _ } ] -> tm) } [ arg ]

let val_of_norm_tube : type n k nk. (n, k, nk, normal) TubeOf.t -> (n, k, nk, value) TubeOf.t =
 fun arg -> TubeOf.mmap { map = (fun _ [ { tm; ty = _ } ] -> tm) } [ arg ]
