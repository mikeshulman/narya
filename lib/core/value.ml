open Util
open Reporter
open Dim
open Term
open Bwd
open Hctx

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
    | Pi : ('k, value) CubeOf.t * ('k, unit) BindCube.t -> uninst
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
    | Lam : 'k binder -> value
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
    | Pi : ('k, value) CubeOf.t * ('k, unit) BindCube.t -> uninst
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
    | Lam : 'k binder -> value
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

(* Now we "include" everything we defined in the above recursive module, so callers in other files don't have to qualify or re-open it. *)
include Value

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

(* Ensure that a value is a fully instantiated type, and extract its relevant pieces.  In most situations, the failure of this is a bug, but we allow the caller to specify it differently, since during typechecking it could be a user error. *)
type full_inst = Fullinst : uninst * (D.zero, 'k, 'k, normal) TubeOf.t -> full_inst

let full_inst ?severity (ty : value) (err : string) : full_inst =
  match ty with
  (* Since we expect fully instantiated types, in the uninstantiated case the dimension must be zero. *)
  | Uninst (ty, (lazy (Uninst (UU n, _)))) -> (
      match compare n D.zero with
      | Eq -> Fullinst (ty, TubeOf.empty D.zero)
      | Neq -> fatal ?severity (Type_not_fully_instantiated err))
  | Inst { tm = ty; dim = _; args; tys = _ } -> (
      match compare (TubeOf.uninst args) D.zero with
      | Eq ->
          let Eq = D.plus_uniq (TubeOf.plus args) (D.zero_plus (TubeOf.inst args)) in
          Fullinst (ty, args)
      | Neq -> fatal ?severity (Type_not_fully_instantiated err))
  | _ -> fatal ?severity (Type_not_fully_instantiated err)

(* Instantiate an arbitrary value, combining tubes. *)
let rec inst : type m n mn. value -> (m, n, mn, normal) TubeOf.t -> value =
 fun tm args2 ->
  let n = TubeOf.inst args2 in
  match D.compare_zero n with
  | Zero -> tm
  | Pos dim2 -> (
      match tm with
      | Inst { tm; dim = _; args = args1; tys = tys1 } -> (
          match compare (TubeOf.out args2) (TubeOf.uninst args1) with
          | Neq ->
              fatal
                (Dimension_mismatch
                   ( "instantiating a partially instantiated type",
                     TubeOf.out args2,
                     TubeOf.uninst args1 ))
          | Eq ->
              let (Plus nk) = D.plus (TubeOf.inst args1) in
              let args = TubeOf.plus_tube nk args1 args2 in
              let tys = TubeOf.middle (D.zero_plus (TubeOf.uninst args2)) (TubeOf.plus args2) tys1 in
              let tys = inst_args args2 tys in
              Inst { tm; dim = D.pos_plus dim2 nk; args; tys })
      | Uninst (tm, (lazy ty)) -> (
          (* In this case, the type must be a fully instantiated universe of the right dimension, and the remaining types come from its instantiation arguments. *)
          let (Fullinst (ty, tyargs)) = full_inst ty "inst" in
          match ty with
          | UU k -> (
              match (compare k (TubeOf.out args2), compare k (TubeOf.out tyargs)) with
              | Neq, _ ->
                  fatal
                    (Dimension_mismatch ("instantiating an uninstantiated type", k, TubeOf.out args2))
              | _, Neq ->
                  fatal
                    (Dimension_mismatch
                       ("instantiating an uninstantiated type", k, TubeOf.out tyargs))
              | Eq, Eq ->
                  let tys =
                    val_of_norm_tube
                      (TubeOf.middle (D.zero_plus (TubeOf.uninst args2)) (TubeOf.plus args2) tyargs)
                  in
                  let tys = inst_args args2 tys in
                  Inst { tm; dim = dim2; args = args2; tys })
          | _ -> fatal (Anomaly "can't instantiate non-type"))
      | Lam _ -> fatal (Anomaly "can't instantiate lambda-abstraction")
      | Struct _ -> fatal (Anomaly "can't instantiate struct")
      | Constr _ -> fatal (Anomaly "can't instantiate constructor"))

and inst_args :
    type m n mn.
    (m, n, mn, normal) TubeOf.t -> (D.zero, m, m, value) TubeOf.t -> (D.zero, m, m, value) TubeOf.t
    =
 fun args2 tys ->
  let n = TubeOf.inst args2 in
  TubeOf.mmap
    {
      map =
        (fun fe [ ty ] ->
          let j = dom_tface fe in
          let (Plus jn) = D.plus n in
          let args =
            TubeOf.build j jn
              {
                build =
                  (fun fa ->
                    let (PFace_of_plus (pq, fc, fd)) = pface_of_plus fa in
                    let fec = comp_sface (sface_of_tface fe) fc in
                    let fecd = sface_plus_pface fec (TubeOf.plus args2) pq fd in
                    TubeOf.find args2 fecd);
              } in
          inst ty args);
    }
    [ tys ]

(* Given a *type*, hence an element of a fully instantiated universe, extract the arguments of the instantiation of that universe.  These were stored in the extra arguments of Uninst and Inst. *)
type inst_tys = Inst_tys : (D.zero, 'n, 'n, value) TubeOf.t -> inst_tys

let inst_tys : value -> inst_tys = function
  | Uninst (_, (lazy (Uninst (UU z, _)))) -> (
      match compare z D.zero with
      | Eq -> Inst_tys (TubeOf.empty D.zero)
      | Neq -> fatal (Anomaly "higher universe must be instantiated to be a type"))
  | Uninst (_, (lazy (Inst { tm = UU _; dim = _; args = tys; tys = _ }))) -> (
      match compare (TubeOf.uninst tys) D.zero with
      | Eq ->
          let Eq = D.plus_uniq (D.zero_plus (TubeOf.inst tys)) (TubeOf.plus tys) in
          Inst_tys (val_of_norm_tube tys)
      | Neq -> fatal (Anomaly "universe must be fully instantiated to be a type"))
  | Inst { tm = _; dim = _; args = _; tys } -> Inst_tys tys
  | _ -> fatal (Anomaly "invalid type, has no instantiation arguments")

(* Given two families of values, the second intended to be the types of the other, annotate the former by instantiations of the latter to make them into normals. *)
and norm_of_vals : type k. (k, value) CubeOf.t -> (k, value) CubeOf.t -> (k, normal) CubeOf.t =
 fun tms tys ->
  (* Since we have to instantiate the types at the *normal* version of the terms, which is what we are computing, we also add the results to a hashtable as we create them so we can access them randomly later. *)
  let new_tm_tbl = Hashtbl.create 10 in
  let new_tms =
    CubeOf.mmap
      {
        map =
          (fun fab [ tm; ty ] ->
            let args =
              TubeOf.build D.zero
                (D.zero_plus (dom_sface fab))
                {
                  build =
                    (fun fc ->
                      Hashtbl.find new_tm_tbl (SFace_of (comp_sface fab (sface_of_tface fc))));
                } in
            let ty = inst ty args in
            let newtm = { tm; ty } in
            Hashtbl.add new_tm_tbl (SFace_of fab) newtm;
            newtm);
      }
      [ tms; tys ] in
  new_tms

(* Assemble an environment from a Bwv of values. *)
let rec env_of_bwv :
    type n a ea.
    n D.t -> ((n, normal) CubeOf.t, a) Bwv.t -> (emp, a, ea, D.zero) exts -> (n, ea) env =
 fun n xs ea ->
  match (xs, ea) with
  | Emp, Zero -> Emp n
  | Snoc (xs, x), Suc ea -> Ext (env_of_bwv n xs ea, CubeOf.singleton (val_of_norm_cube x))

(* Require that the supplied Bwd contains exactly b arguments, rearrange each mn-cube argument into an n-cube of m-cubes, and add all of them to the given environment. *)
let rec take_args :
    type m n mn a b ab.
    (m, a) env ->
    (m, n, mn) D.plus ->
    (mn, value) CubeOf.t Bwd.t ->
    (a, b, ab, n) exts ->
    (m, ab) env =
 fun env mn dargs plus ->
  let m = dim_env env in
  let n = D.plus_right mn in
  match (dargs, plus) with
  | Emp, Zero -> env
  | Snoc (args, arg), Suc plus ->
      let env = take_args env mn args plus in
      Ext
        ( env,
          CubeOf.build n
            {
              build =
                (fun fb ->
                  CubeOf.build m
                    {
                      build =
                        (fun fa ->
                          let (Plus jk) = D.plus (dom_sface fb) in
                          let fab = sface_plus_sface fa mn jk fb in
                          CubeOf.find arg fab);
                    });
            } )
  | _ -> fatal (Anomaly "wrong number of arguments in argument list")

(* A version of take_args that takes some number of actual arguments without insertions from a Bwd, adds a specified number of them to the environment, and returns the others in a Bwv of specified length.  *)
let rec take_canonical_args :
    type n a b ab c.
    (n, a) env ->
    (n, normal) CubeOf.t Bwd.t ->
    (a, b, ab, D.zero) exts ->
    c N.t ->
    (n, ab) env * ((n, normal) CubeOf.t, c) Bwv.t =
 fun env args ab c ->
  match c with
  | Nat (Suc c) -> (
      match args with
      | Snoc (args, arg) ->
          let env, rest = take_canonical_args env args ab (Nat c) in
          (env, Snoc (rest, arg))
      | Emp -> fatal (Anomaly "not enough arguments in canonical argument list"))
  | Nat Zero -> (
      match (args, ab) with
      | Snoc (args, arg), Suc ab ->
          let env, Emp = take_canonical_args env args ab (Nat Zero) in
          (Ext (env, CubeOf.singleton (val_of_norm_cube arg)), Emp)
      | Emp, Zero -> (env, Emp)
      | _ -> fatal (Anomaly "wrong number of arguments in canonical argument list"))

(* The universe of any dimension belongs to an instantiation of itself.  Note that the result is not itself a type (i.e. in the 0-dimensional universe) unless n=0. *)
let rec universe : type n. n D.t -> value =
 fun n ->
  match D.compare_zero n with
  | Zero ->
      (* Without lazy this would be an infinite loop *)
      Uninst (UU D.zero, lazy (universe D.zero))
  | Pos n' ->
      Uninst
        ( UU n,
          lazy
            (let args =
               TubeOf.build D.zero (D.zero_plus n)
                 {
                   build =
                     (fun fa ->
                       let m = dom_tface fa in
                       universe_nf m);
                 } in
             Inst { tm = UU n; dim = n'; args; tys = TubeOf.empty D.zero }) )

and universe_nf : type n. n D.t -> normal =
 fun n ->
  let uun = universe n in
  match uun with
  | Uninst (_, (lazy uunty)) -> { tm = uun; ty = uunty }
  | _ -> fatal (Anomaly "impossible result from universe")

(* Given a type belonging to the m+n dimensional universe instantiated at tyargs, compute the instantiation of the m-dimensional universe that its instantiation belongs to. *)
let rec tyof_inst :
    type m n mn. (D.zero, mn, mn, normal) TubeOf.t -> (m, n, mn, normal) TubeOf.t -> value =
 fun tyargs eargs ->
  let m = TubeOf.uninst eargs in
  let n = TubeOf.inst eargs in
  let mn = TubeOf.plus eargs in
  let margs =
    TubeOf.build D.zero (D.zero_plus m)
      {
        build =
          (fun fe ->
            let j = dom_tface fe in
            let (Plus jn) = D.plus (D.plus_right mn) in
            let jnargs =
              TubeOf.build j jn
                {
                  build =
                    (fun fa ->
                      let (PFace_of_plus (pq, fc, fd)) = pface_of_plus fa in
                      TubeOf.find eargs
                        (sface_plus_tface
                           (comp_sface (sface_of_tface fe) fc)
                           (D.plus_zero m) mn pq fd));
                } in
            (* We need to able to look things up in tyargs that are indexed by a composite of tfaces.  TODO: Actually define composites of tfaces, with each other and/or with sfaces on one side or the other, so that this works.  For the moment, we punt and use a hashtbl indexed by sfaces. *)
            let tyargtbl = Hashtbl.create 10 in
            TubeOf.miter
              { it = (fun fa [ ty ] -> Hashtbl.add tyargtbl (SFace_of (sface_of_tface fa)) ty) }
              [ tyargs ];
            let jntyargs =
              TubeOf.build D.zero
                (D.zero_plus (D.plus_out j jn))
                {
                  build =
                    (fun fa ->
                      let fb = sface_plus_sface (sface_of_tface fe) mn jn (id_sface n) in
                      Hashtbl.find tyargtbl (SFace_of (comp_sface fb (sface_of_tface fa))));
                } in
            let tm = inst (TubeOf.find tyargs (tface_plus fe mn mn jn)).tm jnargs in
            let ty = tyof_inst jntyargs jnargs in
            { tm; ty });
      } in
  inst (universe m) margs

(* To typecheck a lambda, do an eta-expanding equality check, check pi-types for equality, or read back a pi-type or a term at a pi-type, we must create one new variable for each argument in the boundary.  Sometimes we need these variables as values and other times as normals. *)
let dom_vars :
    type m. int -> (m, value) CubeOf.t -> (m, value) CubeOf.t * (m, level option * normal) CubeOf.t
    =
 fun i doms ->
  (* To make these variables into values, we need to annotate them with their types, which in general are instantiations of the domains at previous variables.  Thus, we assemble them in a hashtable as we create them for random access to the previous ones. *)
  let argtbl = Hashtbl.create 10 in
  let j = ref 0 in
  let [ args; nfs ] =
    CubeOf.pmap
      {
        map =
          (fun fa [ dom ] ->
            let ty =
              inst dom
                (TubeOf.build D.zero
                   (D.zero_plus (dom_sface fa))
                   {
                     build =
                       (fun fc ->
                         Hashtbl.find argtbl (SFace_of (comp_sface fa (sface_of_tface fc))));
                   }) in
            let level = (i, !j) in
            j := !j + 1;
            let v = { tm = var level ty; ty } in
            Hashtbl.add argtbl (SFace_of fa) v;
            [ v.tm; (Some level, v) ]);
      }
      [ doms ] (Cons (Cons Nil)) in
  (args, nfs)
