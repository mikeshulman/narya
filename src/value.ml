open Dim
open Term
open Bwd

(* Internal values, the result of evaluation with closures for abstractions.  Use De Bruijn *levels*, so that weakening is implicit.  Fully internal unbiased syntax lives here: in addition to higher-dimensional applications and abstractions, we also have higher-dimensional pi-types, higher-dimensional universes, and floors of higher-dimensional types.  Separated into neutrals and normals, so that there are no beta-redexes.  Explicit substitutions (environments) are stored on binders, for NBE.  Operator actions are treated as a mix between substitutions and syntax. *)

(* The codomains of a pi-type are stored as a Cube of binders, and since binders are a type family this dependence has to be specified by applying a module functor (rather than just parametrizing a type).  Since values are defined mutually with binders, we need to "apply the functor Cube" mutually with the definition of these types.  This is possible using a recursive module. *)
module rec Value : sig
  (* A recursive module is required to specify its module type explicitly.  We make this as transparent as possible, so the module type is nearly a copy of the module itself.  For the comments, see the actual definition below. *)
  module BindFam : sig
    type ('k, 'b) t = 'k Value.binder
  end

  module BindCube : module type of Cube (BindFam)

  type head =
    | Var : { level : int; deg : ('m, 'n) deg } -> head

  and app = App : ('n, normal) ConstCube.t * ('m, 'n, 'k) insertion -> app

  and _ binder =
    | Bind : {
        env : ('m, 'a) env;
        perm : 'mn perm;
        plus_dim : ('m, 'n, 'mn) D.plus;
        bound_faces : ('n, 'fn) count_faces;
        plus_faces : ('a, 'fn, 'afn) N.plus;
        body : 'afn term;
        args : (('m, 'mn) FaceCube.t, 'fn) Bwv.t;
      }
        -> 'mn binder

  and uninst =
    | UU : 'n D.t -> uninst
    | Pi : ('k, value) ConstCube.t * ('k, unit) BindCube.t -> uninst
    | Neu : { fn : head; args : app Bwd.t; ty : value } -> uninst

  and value =
    | Uninst : uninst -> value
    | Inst : { tm : uninst; dim : 'k D.pos; args : ('n, 'k, 'nk, value) ConstTube.t } -> value
    | Lam : 'k binder -> value

  and normal = { tm : value; ty : value }

  and (_, _) env =
    | Emp : 'n D.t -> ('n, N.zero) env
    | Ext : ('n, 'b) env * ('n, value) ConstCube.t -> ('n, 'b N.suc) env
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
    | Var : { level : int; deg : ('m, 'n) deg } -> head

  (* An application contains the data of an n-dimensional argument and its boundary, together with a neutral insertion applied outside that can't be pushed in.  This represents the *argument list* of a single application, not the function.  Thus, an application spine will be a head together with a list of apps. *)
  and app = App : ('n, normal) ConstCube.t * ('m, 'n, 'k) insertion -> app

  (* Lambdas and Pis both bind a variable, along with its dependencies.  These are recorded as defunctionalized closures.  Since they are produced by higher-dimensional substitutions and operator actions, the dimension of the binder can be different than the dimension of the environment that closes its body.  Accordingly, in addition to the environment and degeneracy to close its body, we store information about how to map the eventual arguments into the bound variables in the body.  *)
  and _ binder =
    | Bind : {
        env : ('m, 'a) env;
        perm : 'mn perm;
        plus_dim : ('m, 'n, 'mn) D.plus;
        bound_faces : ('n, 'fn) count_faces;
        plus_faces : ('a, 'fn, 'afn) N.plus;
        body : 'afn term;
        (* TODO: Can this be just a ('mn,'mn) FaceCube.t, by adding the faces? *)
        args : (('m, 'mn) FaceCube.t, 'fn) Bwv.t;
      }
        -> 'mn binder

  (* An (m+n)-dimensional type is "instantiated" by applying it a "boundary tube" to get an m-dimensional type.  This operation is supposed to be functorial, so in the normal forms we prevent it from being applied more than once in a row.  We have a separate class of "uninstantiated" values, and then every actual value is instantiated exactly once.  This means that even non-types must be "instantiated", albeit trivially. *)
  and uninst =
    | UU : 'n D.t -> uninst
    (* Pis must store not just the domain type but all its boundary types.  These domain and boundary types are not fully instantiated.  Note the codomains are stored in a face tree of binders. *)
    | Pi : ('k, value) ConstCube.t * ('k, unit) BindCube.t -> uninst
    (* A neutral is an application spine -- a head with a list of applications -- as well as a stored type for it. *)
    | Neu : { fn : head; args : app Bwd.t; ty : value } -> uninst

  and value =
    (* An uninstantiated term *)
    | Uninst : uninst -> value
    (* A term with some nonzero instantiation *)
    | Inst : {
        (* The uninstantiated term being instantiated *)
        tm : uninst;
        (* Require at least one dimension to be instantiated *)
        dim : 'k D.pos;
        (* The arguments for a tube of some dimensions *)
        args : ('n, 'k, 'nk, value) ConstTube.t;
      }
        -> value
    (* Lambda-abstractions are never types, so they can never be nontrivially instantiated.  Thus we may as well make them values directly. *)
    | Lam : 'k binder -> value

  (* A "normal form" is a value paired with its type.  The type is used for eta-expansion and equality-checking. *)
  and normal = { tm : value; ty : value }

  (* This is a context morphism *from* a De Bruijn LEVEL context *to* a De Bruijn INDEX context.  Specifically, an ('n, 'a) env is a substitution from a level context to an index context of length 'a of dimension 'n. *)
  and (_, _) env =
    | Emp : 'n D.t -> ('n, N.zero) env
    | Ext : ('n, 'b) env * ('n, value) ConstCube.t -> ('n, 'b N.suc) env
    | Act : ('n, 'b) env * ('m, 'n) op -> ('m, 'b) env
end

(* Now we "include" everything we defined in the above recursive module, so callers in other files don't have to qualify or re-open it. *)
include Value
module FaceConstCubeMap = CubeMap (FaceFam) (ConstFam)

(* Given a De Bruijn level and a type, build the variable of that level having that type. *)
let var : int -> value -> value =
 fun i ty -> Uninst (Neu { fn = Var { level = i; deg = id_deg D.zero }; args = Emp; ty })

(* Every context morphism has a valid dimension. *)
let rec dim_env : type n b. (n, b) env -> n D.t = function
  | Emp n -> n
  | Ext (e, _) -> dim_env e
  | Act (_, op) -> dom_op op

(* And likewise every binder *)
let dim_binder : type m. m binder -> m D.t = function
  | Bind b -> D.plus_out (dim_env b.env) b.plus_dim

(* Instantiate an arbitrary value, combining tubes. *)
let inst : type m n mn f. value -> (m, n, mn, value) ConstTube.t -> value =
 fun tm args2 ->
  match D.compare_zero (ConstTube.inst args2) with
  | Zero -> tm
  | Pos dim2 -> (
      match tm with
      | Inst { tm; dim = _; args = args1 } -> (
          match compare (ConstTube.out args2) (ConstTube.uninst args1) with
          | Neq -> raise (Failure "Dimension mismatch in instantiation")
          | Eq ->
              let (Plus nk) = D.plus (ConstTube.inst args1) in
              let args = ConstTube.plus_tube { lift = (fun x -> x) } nk args1 args2 in
              Inst { tm; dim = D.pos_plus dim2 nk; args })
      | Uninst tm -> Inst { tm; dim = dim2; args = args2 }
      | Lam _ -> raise (Failure "Can't instantiate lambda-abstraction"))

(* Look up a value in an environment by variable index.  Since the result has to have a degeneracy action applied (from the actions stored in the environment), this depends on being able to act on a value by a degeneracy.  We make that action function a parameter so as not to have to move this after its definition.  *)
let lookup : type n b. (value -> any_deg -> value) -> (n, b) env -> b N.index -> value =
 fun act_value env v ->
  (* We traverse the environment, accumulating operator actions as we go, until we find the specified index. *)
  let rec lookup : type m n b. (n, b) env -> b N.index -> (m, n) op -> value =
   fun env v op ->
    match (env, v) with
    | Emp _, _ -> .
    | Ext (_, entry), Top ->
        (* When we find our variable, we decompose the accumulated operator into a strict face and degeneracy. *)
        let (Op (f, s)) = op in
        act_value (ConstCube.find entry f) (Any s)
    | Ext (env, _), Pop v -> lookup env v op
    | Act (env, op'), _ -> lookup env v (comp_op op' op) in
  lookup env v (id_op (dim_env env))

let rec env_append :
    type n a b ab.
    (a, b, ab) N.plus -> (n, a) env -> ((n, value) ConstCube.t, b) Bwv.t -> (n, ab) env =
 fun ab env xss ->
  match (ab, xss) with
  | Zero, Emp -> env
  | Suc ab, Snoc (xss, xs) -> Ext (env_append ab env xss, xs)
