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
    | Const : { name : Constant.t; dim : 'n D.t } -> head

  and 'n arg = Arg of ('n, normal) CubeOf.t | Field of Field.t
  and app = App : 'n arg * ('m, 'n, 'k) insertion -> app

  and _ binder =
    | Bind : {
        env : ('m, 'a) env;
        perm : 'mn perm;
        plus_dim : ('m, 'n, 'mn) D.plus;
        bound_faces : ('n, 'fn) count_faces;
        plus_faces : ('a, 'fn, 'afn) N.plus;
        body : 'afn term;
        args : (('m, 'mn face_of) CubeOf.t, 'fn) Bwv.t;
      }
        -> 'mn binder

  and uninst =
    | UU : 'n D.t -> uninst
    | Pi : ('k, value) CubeOf.t * ('k, unit) BindCube.t -> uninst
    | Neu : { fn : head; args : app Bwd.t; ty : value } -> uninst

  and value =
    | Uninst : uninst -> value
    | Inst : { tm : uninst; dim : 'k D.pos; args : ('n, 'k, 'nk, value) TubeOf.t } -> value
    | Lam : 'k binder -> value

  and normal = { tm : value; ty : value }

  and (_, _) env =
    | Emp : 'n D.t -> ('n, N.zero) env
    | Ext : ('n, 'b) env * ('n, value) CubeOf.t -> ('n, 'b N.suc) env
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
    (* A constant occurs at a specified dimension. *)
    | Const : { name : Constant.t; dim : 'n D.t } -> head

  (* An application contains the data of an n-dimensional argument and its boundary, together with a neutral insertion applied outside that can't be pushed in.  This represents the *argument list* of a single application, not the function.  Thus, an application spine will be a head together with a list of apps. *)
  and 'n arg = Arg of ('n, normal) CubeOf.t | Field of Field.t
  and app = App : 'n arg * ('m, 'n, 'k) insertion -> app

  (* Lambdas and Pis both bind a variable, along with its dependencies.  These are recorded as defunctionalized closures.  Since they are produced by higher-dimensional substitutions and operator actions, the dimension of the binder can be different than the dimension of the environment that closes its body.  Accordingly, in addition to the environment and degeneracy to close its body, we store information about how to map the eventual arguments into the bound variables in the body.  *)
  and _ binder =
    | Bind : {
        env : ('m, 'a) env;
        perm : 'mn perm;
        plus_dim : ('m, 'n, 'mn) D.plus;
        bound_faces : ('n, 'fn) count_faces;
        plus_faces : ('a, 'fn, 'afn) N.plus;
        body : 'afn term;
        (* TODO: Can this be just a ('mn,'mn face_of) CubeOf.t, by adding the faces? *)
        args : (('m, 'mn face_of) CubeOf.t, 'fn) Bwv.t;
      }
        -> 'mn binder

  (* An (m+n)-dimensional type is "instantiated" by applying it a "boundary tube" to get an m-dimensional type.  This operation is supposed to be functorial, so in the normal forms we prevent it from being applied more than once in a row.  We have a separate class of "uninstantiated" values, and then every actual value is instantiated exactly once.  This means that even non-types must be "instantiated", albeit trivially. *)
  and uninst =
    | UU : 'n D.t -> uninst
    (* Pis must store not just the domain type but all its boundary types.  These domain and boundary types are not fully instantiated.  Note the codomains are stored in a face tree of binders. *)
    | Pi : ('k, value) CubeOf.t * ('k, unit) BindCube.t -> uninst
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
        args : ('n, 'k, 'nk, value) TubeOf.t;
      }
        -> value
    (* Lambda-abstractions are never types, so they can never be nontrivially instantiated.  Thus we may as well make them values directly. *)
    | Lam : 'k binder -> value

  (* A "normal form" is a value paired with its type.  The type is used for eta-expansion and equality-checking. *)
  and normal = { tm : value; ty : value }

  (* This is a context morphism *from* a De Bruijn LEVEL context *to* a De Bruijn INDEX context.  Specifically, an ('n, 'a) env is a substitution from a level context to an index context of length 'a of dimension 'n. *)
  and (_, _) env =
    | Emp : 'n D.t -> ('n, N.zero) env
    | Ext : ('n, 'b) env * ('n, value) CubeOf.t -> ('n, 'b N.suc) env
    | Act : ('n, 'b) env * ('m, 'n) op -> ('m, 'b) env
end

(* Now we "include" everything we defined in the above recursive module, so callers in other files don't have to qualify or re-open it. *)
include Value

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
let inst : type m n mn f. value -> (m, n, mn, value) TubeOf.t -> value =
 fun tm args2 ->
  match D.compare_zero (TubeOf.inst args2) with
  | Zero -> tm
  | Pos dim2 -> (
      match tm with
      | Inst { tm; dim = _; args = args1 } -> (
          match compare (TubeOf.out args2) (TubeOf.uninst args1) with
          | Neq -> raise (Failure "Dimension mismatch in instantiation")
          | Eq ->
              let (Plus nk) = D.plus (TubeOf.inst args1) in
              let args = TubeOf.plus_tube { lift = (fun x -> x) } nk args1 args2 in
              Inst { tm; dim = D.pos_plus dim2 nk; args })
      | Uninst tm -> Inst { tm; dim = dim2; args = args2 }
      | Lam _ -> raise (Failure "Can't instantiate lambda-abstraction"))

(* Ensure that a value is a fully instantiated type, and extract its relevant pieces.  Optionally, raise an error if it isn't. *)
type full_inst = Fullinst : uninst * (D.zero, 'k, 'k, value) TubeOf.t -> full_inst

let full_inst : type n. value -> string -> full_inst =
 fun ty err ->
  match ty with
  (* Since we expect fully instantiated types, in the uninstantiated case the dimension must be zero. *)
  | Uninst ty -> Fullinst (ty, TubeOf.empty D.zero)
  | Inst { tm = ty; dim = _; args } -> (
      match compare (TubeOf.uninst args) D.zero with
      | Eq ->
          let Eq = D.plus_uniq (TubeOf.plus args) (D.zero_plus (TubeOf.inst args)) in
          Fullinst (ty, args)
      | Neq -> raise (Failure ("Type not fully instantiated in " ^ err)))
  | _ -> raise (Failure ("Fully instantiated type missing in " ^ err))

(* A version that returns errors rather than throwing exceptions. *)
let full_inst_opt : type n. value -> full_inst option =
 fun ty ->
  match full_inst ty "" with
  | exception _ -> None
  | res -> Some res

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
        act_value (CubeOf.find entry f) (Any s)
    | Ext (env, _), Pop v -> lookup env v op
    | Act (env, op'), _ -> lookup env v (comp_op op' op) in
  lookup env v (id_op (dim_env env))

let rec env_append :
    type n a b ab. (a, b, ab) N.plus -> (n, a) env -> ((n, value) CubeOf.t, b) Bwv.t -> (n, ab) env
    =
 fun ab env xss ->
  match (ab, xss) with
  | Zero, Emp -> env
  | Suc ab, Snoc (xss, xs) -> Ext (env_append ab env xss, xs)

let val_of_norm_cube : type n. (n, normal) CubeOf.t -> (n, value) CubeOf.t =
 fun arg -> CubeOf.mmap { map = (fun _ [ { tm; ty = _ } ] -> tm) } [ arg ]

let val_of_norm_tube : type n k nk. (n, k, nk, normal) TubeOf.t -> (n, k, nk, value) TubeOf.t =
 fun arg -> TubeOf.mmap { map = (fun _ [ { tm; ty = _ } ] -> tm) } [ arg ]

(* Given two families of values, the second intended to be the types of the other, annotate the former by instantiations of the latter to make them into normals. *)
and norm_of_vals : type k. (k, value) CubeOf.t -> (k, value) CubeOf.t -> (k, normal) CubeOf.t =
 fun tms tys ->
  (* Since we have to instantiate the types at the *normal* version of the terms, which is what we are computing, we also add the results to a hashtable as we create them so we can access them randomly later. *)
  let new_tms =
    CubeOf.mmap
      {
        map =
          (fun fab [ tm; ty ] ->
            let newtm =
              {
                tm;
                ty =
                  inst ty
                    (TubeOf.build D.zero
                       (D.zero_plus (dom_sface fab))
                       { build = (fun fc -> CubeOf.find tms (comp_sface fab (sface_of_tface fc))) });
              } in
            newtm);
      }
      [ tms; tys ] in
  new_tms

(* Require that the supplied app Bwd.t has exactly c elements, all of them applications of dimension n, take a specified b of them, and add them to an environment of dimension n. *)
let rec take_args :
    type n a b ab c. (n, a) env -> (b, c) N.subset -> app Bwd.t -> (a, b, ab) N.plus -> (n, ab) env
    =
 fun env sub dargs plus ->
  match (sub, dargs, plus) with
  | Zero, Emp, Zero -> env
  | Omit sub, Snoc (dargs, _), _ -> take_args env sub dargs plus
  | Take sub, Snoc (dargs, App (Arg arg, ins)), Suc plus -> (
      (* We can only take arguments that have no degeneracy applied, since case trees are specified at dimension zero. *)
      match is_id_deg (perm_of_ins ins) with
      | None -> raise (Failure "Nonidentity degeneracy inside argument list")
      | Some () -> (
          (* Since dargs is a backwards list, we have to first take all the other arguments and then our current one.  *)
          let env = take_args env sub dargs plus in
          (* Again, since case trees are specified at dimension zero, all the applications must be the same dimension. *)
          match compare (CubeOf.dim arg) (dim_env env) with
          | Eq ->
              (* Why is this type annotation necessary? *)
              Ext (env, (val_of_norm_cube arg : (n, value) CubeOf.t))
          | Neq -> raise (Failure "Different dimensions in argument list")))
  | _ -> raise (Failure "Wrong number of arguments in argument list")

(* A version of take_args that returns errors rather than throwing exceptions. *)
let take_args_opt :
    type n a b ab c.
    (n, a) env -> (b, c) N.subset -> app Bwd.t -> (a, b, ab) N.plus -> (n, ab) env option =
 fun env sub dargs plus ->
  match take_args env sub dargs plus with
  | exception _ -> None
  | res -> Some res
