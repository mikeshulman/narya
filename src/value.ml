open Dim
open Term

(* Internal values, the result of evaluation with closures for abstractions.  Use De Bruijn *levels*, so that weakening is implicit.  Fully internal unbiased syntax lives here: in addition to higher-dimensional applications and abstractions, we also have higher-dimensional pi-types, higher-dimensional universes, and floors of higher-dimensional types.  Separated into neutrals and normals, so that there are no beta-redexes.  Explicit substitutions (environments) are stored on binders, for NBE.  Operator actions are treated as a mix between substitutions and syntax. *)

(* The codomains of a pi-type are stored as a face tree of binders.  Since values are defined mutually with binders, we need to "apply the functor Tree" mutually with the definition of these types.  This is possible using a recursive module. *)
module rec Value : sig
  (* A recursive module is required to specify its module type.  We make it as transparent as possible, so the module type is nearly a copy of the module itself.  For the comments, see the actual definition below. *)
  module BindFam : sig
    type ('k, 'b) t = 'k Value.binder
  end

  module BindTree : module type of Tree (BindFam)

  module ValFam : sig
    type ('k, 'b) t = Value.value
  end

  module ValTree : module type of Tree (ValFam)

  type neu =
    | Var : { level : int; deg : ('m, 'n) deg } -> neu
    | App : {
        fn : neu;
        app_faces : ('n, 'f) count_faces;
        args : (normal, 'f) Bwv.t;
        ins : ('m, 'n, 'k) insertion;
      }
        -> neu

  and _ binder =
    | Bind : {
        env : ('m, 'a) env;
        perm : 'mn perm;
        plus_dim : ('m, 'n, 'mn) D.plus;
        bound_faces : ('n, 'fn) count_faces;
        plus_faces : ('a, 'fn, 'afn) N.plus;
        body : 'afn term;
        args : (('m, 'mn) FaceTree.t, 'fn) Bwv.t;
      }
        -> 'mn binder

  and uninst =
    | UU : 'n D.t -> uninst
    | Pi : ('k, 'f) count_faces * (value, 'f) Bwv.t * ('k, unit) BindTree.t -> uninst
    | Neu : neu * value -> uninst

  and value =
    | Uninst : uninst -> value
    | Inst : {
        tm : uninst;
        dim : 'n D.pos;
        tube : ('m, 'n, 'f) count_tube;
        args : (value, 'f) Bwv.t;
      }
        -> value
    | Lam : 'k binder -> value

  and normal = { tm : value; ty : value }

  and (_, _) env =
    | Emp : 'n D.t -> ('n, N.zero) env
    | Ext : ('n, 'b) env * ('n, unit) ValTree.t -> ('n, 'b N.suc) env
    | Act : ('n, 'b) env * ('m, 'n) op -> ('m, 'b) env
end = struct
  (* Here is the recursive application of the functor Tree.  First we define a module to pass as its argument, with type defined to equal the yet-to-be-defined binder, referred to recursively. *)
  module BindFam = struct
    type ('k, 'b) t = 'k Value.binder
  end

  module BindTree = Tree (BindFam)

  module ValFam = struct
    type ('k, 'b) t = Value.value
  end

  module ValTree = Tree (ValFam)

  (* Neutrals are as usual, except that they have a nonreducible degeneracy applied outside. *)
  type neu =
    | Var : {
        level : int; (* De Bruijn level *)
        deg : ('m, 'n) deg; (* Neutral degeneracy applied outside *)
      }
        -> neu
    | App : {
        (* Function being applied *)
        fn : neu;
        (* The dimension of the application, and count the resulting arguments *)
        app_faces : ('n, 'f) count_faces;
        (* The arguments *)
        args : (normal, 'f) Bwv.t;
        (* A neutral degeneracy applied outside that can't be pushed inside *)
        ins : ('m, 'n, 'k) insertion;
      }
        -> neu

  (* Lambdas and Pis both bind a variable, along with its dependencies.  These are recorded as defunctionalized closures.  Since they are produced by higher-dimensional substitutions and operator actions, the dimension of the binder can be different than the dimension of the environment that closes its body.  Accordingly, in addition to the environment and degeneracy to close its body, we store information about how to map the eventual arguments into the bound variables in the body.  *)
  and _ binder =
    | Bind : {
        env : ('m, 'a) env;
        perm : 'mn perm;
        plus_dim : ('m, 'n, 'mn) D.plus;
        bound_faces : ('n, 'fn) count_faces;
        plus_faces : ('a, 'fn, 'afn) N.plus;
        body : 'afn term;
        args : (('m, 'mn) FaceTree.t, 'fn) Bwv.t;
      }
        -> 'mn binder

  (* An (m+n)-dimensional type is "instantiated" by applying it a "boundary tube" to get an m-dimensional type.  This operation is supposed to be functorial, so in the normal forms we prevent it from being applied more than once in a row.  We have a separate class of "uninstantiated" values, and then every actual value is instantiated exactly once.  This means that even non-types must be "instantiated", albeit trivially. *)
  and uninst =
    | UU : 'n D.t -> uninst
    (* Pis must store not just the domain type but all its boundary types.  These domain and boundary types are not fully instantiated.  Note the codomains are stored in a face tree of binders. *)
    | Pi : ('k, 'f) count_faces * (value, 'f) Bwv.t * ('k, unit) BindTree.t -> uninst
    | Neu : neu * value -> uninst (* Neutral terms store their type *)

  and value =
    (* An uninstantiated term *)
    | Uninst : uninst -> value
    (* A term with some nonzero instantiation *)
    | Inst : {
        (* The uninstantiated term being instantiated *)
        tm : uninst;
        (* Require at least one dimension to be instantiated *)
        dim : 'n D.pos;
        (* Count the number of arguments for a tube of some dimensions *)
        tube : ('m, 'n, 'f) count_tube;
        (* And list those arguments *)
        args : (value, 'f) Bwv.t;
      }
        -> value
    (* Lambda-abstractions are never types, so they can never be nontrivially instantiated, so we may as well make them values directly. *)
    | Lam : 'k binder -> value

  (* A "normal form" is a value paired with its type.  The type is used for eta-expansion and equality-checking. *)
  and normal = { tm : value; ty : value }

  (* This is a context morphism *from* a De Bruijn LEVEL context *to* a De Bruijn INDEX context.  Specifically, an ('n, 'a) env is a substitution from a level context to an index context of length 'a of dimension 'n. *)
  and (_, _) env =
    | Emp : 'n D.t -> ('n, N.zero) env
    | Ext : ('n, 'b) env * ('n, unit) ValTree.t -> ('n, 'b N.suc) env
    | Act : ('n, 'b) env * ('m, 'n) op -> ('m, 'b) env
end

(* Now we include everything we defined above, so callers in other files don't have to qualify or re-open it.x *)
include Value
module FaceValTreeMap = TreeMap (FaceFam) (ValFam)

(* Given a De Bruijn level and a type, build the variable of that level having that type. *)
let var : int -> value -> value =
 fun i ty -> Uninst (Neu (Var { level = i; deg = id_deg D.zero }, ty))

(* Every context morphism has a valid dimension. *)
let rec dim_env : type n b. (n, b) env -> n D.t = function
  | Emp n -> n
  | Ext (e, _) -> dim_env e
  | Act (_, op) -> dom_op op

(* And likewise every binder *)
let dim_binder : type m. m binder -> m D.t = function
  | Bind b -> D.plus_out (dim_env b.env) b.plus_dim

(* Instantiate an arbitrary value, combining tubes. *)
let inst : type m n f. value -> (m, n, f) count_tube -> (value, f) Bwv.t -> value =
 fun tm (Tube tube2) args2 ->
  match D.compare_zero (tube_inst (Tube tube2)) with
  | Zero -> tm
  | Pos dim2 -> (
      match tm with
      | Inst { tm; dim = _; tube = Tube tube1; args = args1 } -> (
          match
            compare
              (D.plus_out (tube_uninst (Tube tube2)) tube2.plus_dim)
              (tube_uninst (Tube tube1))
          with
          | Neq -> raise (Failure "Dimension mismatch in instantiation")
          | Eq ->
              let (Tube_plus_tube (nk, tube, _, args)) =
                tube_plus_tube tube2.plus_dim (Tube tube1) (Tube tube2) args1 args2 in
              Inst { tm; dim = D.pos_plus dim2 nk; tube; args })
      | Uninst tm -> Inst { tm; dim = dim2; tube = Tube tube2; args = args2 }
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
        act_value (ValTree.nth entry f) (Any s)
    | Ext (env, _), Pop v -> lookup env v op
    | Act (env, op'), _ -> lookup env v (comp_op op' op) in
  lookup env v (id_op (dim_env env))

let rec env_append :
    type n a b ab. (a, b, ab) N.plus -> (n, a) env -> ((n, unit) ValTree.t, b) Bwv.t -> (n, ab) env
    =
 fun ab env xss ->
  match (ab, xss) with
  | Zero, Emp -> env
  | Suc ab, Snoc (xss, xs) -> Ext (env_append ab env xss, xs)
