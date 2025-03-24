open Bwd
open Util
open Tbwd
open Dim
open Dimbwd
include Energy
open Term

(* ******************** Values ******************** *)

(* A De Bruijn level is a pair of integers: one for the position (counting in) of the cube-variable-bundle in the context, and one that counts through the faces of that bundle. *)
type level = int * int

(* Internal values, the result of evaluation, with closures for abstractions.  Use De Bruijn *levels*, so that weakening is implicit.  Fully internal unbiased syntax lives here: in addition to higher-dimensional applications and abstractions, we also have higher-dimensional pi-types, higher-dimensional universes, and instantiations of higher-dimensional types.  Separated into neutrals and normals, so that there are no beta-redexes.  Explicit substitutions (environments) are stored on binders, for NBE. *)

(* The codomains of a pi-type are stored as a Cube of binders, and since binders are a type family this dependence has to be specified by applying a module functor (rather than just parametrizing a type).  Since values are defined mutually with binders, we need to "apply the functor Cube" mutually with the definition of these types.  This is possible using a recursive module. *)
module rec Value : sig
  (* A recursive module is required to specify its module type explicitly.  We make this as transparent as possible, so the module type is nearly a copy of the module itself.  For the comments, see the actual definition below. *)
  module BindFam : sig
    type ('k, 'b) t = ('k, kinetic) Value.binder
  end

  module BindCube : module type of Cube (BindFam)

  module Structfield : sig
    type (_, _) t =
      (* We remember which fields are labeled, for readback purposes, and we store the value of each field lazily, so that corecursive definitions don't try to compute an entire infinite structure.  And since in the non-kinetic case, evaluation can produce more data than just a term (e.g. whether a case tree has yet reached a leaf), what we store lazily is the result of evaluation. *)
      | Lower : 's Value.lazy_eval * [ `Labeled | `Unlabeled ] -> (D.zero, 'n * 's * 'et) t
      (* In the higher case, they are always labeled.  There are multiple values are indexed by insertions, regarded as partial bijections with zero remaining dimensions; the 'evaluation dimension is the substitution dimension 'n and the 'intrinsic dimension is associated to the field.  We also store the original terms as a closure, since they may be needed to evaluate fields of degeneracies. *)
      | Higher : ('m, 'n, 'mn, 'p, 'i, 'a) higher_data -> ('i, 'p * potential * no_eta) t

    and ('m, 'n, 'mn, 'p, 'i, 'a) higher_data = {
      vals : ('p, 'i, potential Value.lazy_eval option) InsmapOf.t;
      intrinsic : 'i D.t;
      plusdim : ('m, 'n, 'mn) D.plus;
      env : ('m, 'a) Value.env;
      deg : ('p, 'mn) deg;
      terms : ('n, 'i, 'a) PlusPbijmap.t;
    }
  end

  module StructfieldAbwd : module type of Field.Abwd (Structfield)

  type head =
    | Var : { level : level; deg : ('m, 'n) deg } -> head
    | Const : { name : Constant.t; ins : ('a, 'b, 'c) insertion } -> head
    | Meta : {
        meta : ('a, 'b, 's) Meta.t;
        env : ('m, 'b) env;
        ins : ('mn, 'm, 'n) insertion;
      }
        -> head

  and app = App : 'n arg * ('nk, 'n, 'k) insertion -> app

  and 'n arg =
    | Arg : ('n, normal) CubeOf.t -> 'n arg
    | Field : 'i Field.t * ('t, 'i, 'n) D.plus -> 't arg

  and (_, _) binder =
    | Bind : {
        env : ('m, 'a) env;
        body : (('a, 'n) snoc, 's) term;
        ins : ('mn, 'm, 'n) insertion;
      }
        -> ('mn, 's) binder

  and uninst =
    | UU : 'n D.t -> uninst
    | Pi : string option * ('k, kinetic value) CubeOf.t * ('k, unit) BindCube.t -> uninst
    | Neu : { head : head; args : app Bwd.t; value : potential lazy_eval } -> uninst

  and _ value =
    | Uninst : uninst * kinetic value Lazy.t -> kinetic value
    | Inst : {
        tm : uninst;
        dim : 'k D.pos;
        args : ('n, 'k, 'nk, normal) TubeOf.t;
        tys : (D.zero, 'n, 'n, kinetic value) TubeOf.t;
      }
        -> kinetic value
    | Constr : Constr.t * 'n D.t * ('n, kinetic value) CubeOf.t list -> kinetic value
    | Lam : 'k variables * ('k, 's) binder -> 's value
    | Struct : ('p * 's * 'et) StructfieldAbwd.t * ('pk, 'p, 'k) insertion * 's energy -> 's value

  and _ evaluation =
    | Val : 's value -> 's evaluation
    | Realize : kinetic value -> potential evaluation
    | Unrealized : potential evaluation
    | Canonical : 'm canonical -> potential evaluation

  and _ canonical =
    | Data : ('m, 'j, 'ij) data_args -> 'm canonical
    | Codata : ('mn, 'm, 'n, 'c, 'a, 'et) codata_args -> 'mn canonical

  and ('m, 'j, 'ij) data_args = {
    dim : 'm D.t;
    tyfam : normal Lazy.t option ref;
    indices : (('m, normal) CubeOf.t, 'j, 'ij) Fillvec.t;
    constrs : (Constr.t, ('m, 'ij) dataconstr) Abwd.t;
    discrete : [ `Yes | `Maybe | `No ];
  }

  and ('mn, 'm, 'n, 'c, 'a, 'et) codata_args = {
    eta : (potential, 'et) eta;
    opacity : opacity;
    env : ('m, 'a) env;
    termctx : ('c, ('a, 'n) snoc) termctx option Lazy.t;
    ins : ('mn, 'm, 'n) insertion;
    fields : ('a * 'n * 'et) Term.CodatafieldAbwd.t;
  }

  and (_, _) dataconstr =
    | Dataconstr : {
        env : ('m, 'a) env;
        args : ('a, 'p, 'ap) Telescope.t;
        indices : (('ap, kinetic) term, 'ij) Vec.t;
      }
        -> ('m, 'ij) dataconstr

  and normal = { tm : kinetic value; ty : kinetic value }

  and (_, _) env =
    | Emp : 'n D.t -> ('n, emp) env
    | LazyExt :
        ('n, 'b) env * ('n, 'k, 'nk) D.plus * ('nk, kinetic lazy_eval) CubeOf.t
        -> ('n, ('b, 'k) snoc) env
    | Ext :
        ('n, 'b) env
        * ('n, 'k, 'nk) D.plus
        * (('nk, kinetic value) CubeOf.t, Reporter.Code.t) Result.t
        -> ('n, ('b, 'k) snoc) env
    | Act : ('n, 'b) env * ('m, 'n) op -> ('m, 'b) env
    | Permute : ('a, 'b) Tbwd.permute * ('n, 'b) env -> ('n, 'a) env
    | Shift : ('mn, 'b) env * ('m, 'n, 'mn) D.plus * ('n, 'b, 'nb) Plusmap.t -> ('m, 'nb) env

  and 's lazy_state =
    | Deferred_eval :
        ('m, 'b) env * ('b, 's) term * ('mn, 'm, 'n) insertion * app Bwd.t
        -> 's lazy_state
    | Deferred : (unit -> 's evaluation) * ('m, 'n) deg * app Bwd.t -> 's lazy_state
    | Ready : 's evaluation -> 's lazy_state

  and 's lazy_eval = 's lazy_state ref
end = struct
  (* Here is the recursive application of the functor Cube.  First we define a module to pass as its argument, with type defined to equal the yet-to-be-defined binder, referred to recursively. *)
  module BindFam = struct
    type ('k, 'b) t = ('k, kinetic) Value.binder
  end

  module BindCube = Cube (BindFam)

  module Structfield = struct
    type (_, _) t =
      (* We remember which fields are labeled, for readback purposes, and we store the value of each field lazily, so that corecursive definitions don't try to compute an entire infinite structure.  And since in the non-kinetic case, evaluation can produce more data than just a term (e.g. whether a case tree has yet reached a leaf), what we store lazily is the result of evaluation. *)
      | Lower : 's Value.lazy_eval * [ `Labeled | `Unlabeled ] -> (D.zero, 'n * 's * 'et) t
      (* In the higher case, they are always labeled.  There are multiple values are indexed by insertions, regarded as partial bijections with zero remaining dimensions; the 'evaluation dimension is the substitution dimension 'n and the 'intrinsic dimension is associated to the field.  We also store the original terms as a closure, since they may be needed to evaluate fields of degeneracies. *)
      | Higher : ('m, 'n, 'mn, 'p, 'i, 'a) higher_data -> ('i, 'p * potential * no_eta) t

    and ('m, 'n, 'mn, 'p, 'i, 'a) higher_data = {
      vals : ('p, 'i, potential Value.lazy_eval option) InsmapOf.t;
      intrinsic : 'i D.t;
      plusdim : ('m, 'n, 'mn) D.plus;
      env : ('m, 'a) Value.env;
      deg : ('p, 'mn) deg;
      terms : ('n, 'i, 'a) PlusPbijmap.t;
    }
  end

  module StructfieldAbwd = Field.Abwd (Structfield)

  (* The head of an elimination spine is a variable, a constant, or a substituted metavariable.  *)
  type head =
    (* A variable is determined by a De Bruijn LEVEL, and stores a neutral degeneracy applied to it. *)
    | Var : { level : level; deg : ('m, 'n) deg } -> head
    (* A constant also stores a dimension that it is substituted to and a neutral insertion applied to it.  Many constants are zero-dimensional, meaning that 'c' is zero, and hence a=b is just a dimension and the insertion is trivial.  The dimension of a constant is its dimension as a term standing on its own; so in particular if it has any parameters, then it belongs to an ordinary, 0-dimensional, pi-type and therefore is 0-dimensional, even if the eventual codomain of the pi-type is higher-dimensional.  Note also that when nonidentity insertions end up getting stored here, e.g. by Act, the dimension 'c gets extended as necessary; so it is always okay to create a constant with the (0,0,0) insertion to start with, even if you don't know what its actual dimension is. *)
    | Const : { name : Constant.t; ins : ('a, 'b, 'c) insertion } -> head
    (* A metavariable (i.e. flexible) head stores the metavariable along with a delayed substitution applied to it. *)
    | Meta : {
        meta : ('a, 'b, 's) Meta.t;
        env : ('m, 'b) env;
        ins : ('mn, 'm, 'n) insertion;
      }
        -> head

  (* An application contains the data of an n-dimensional argument and its boundary, together with a neutral insertion applied outside that can't be pushed in.  This represents the *argument list* of a single application, not the function.  Thus, an application spine will be a head together with a list of apps. *)
  and app = App : 'n arg * ('nk, 'n, 'k) insertion -> app

  and 'n arg =
    | Arg : ('n, normal) CubeOf.t -> 'n arg
    (* For a higher field with ('n, 't, 'i) insertion, the actual evaluation dimension is 'n, but the result dimension is only 't.  So the dimension of the arg is 't, since that's the output dimension that a degeneracy acting on could be pushed through.  However, since a degeneracy of dimension up to 'n can act on the inside, we can push in the whole insertion and store only a plus outside. *)
    | Field : 'i Field.t * ('t, 'i, 'n) D.plus -> 't arg

  (* Lambdas and Pis both bind a variable, along with its dependencies.  These are recorded as defunctionalized closures.  Since they are produced by higher-dimensional substitutions and operator actions, the dimension of the binder can be different than the dimension of the environment that closes its body.  Accordingly, in addition to the environment and degeneracy to close its body, we store information about how to map the eventual arguments into the bound variables in the body.  *)
  and (_, _) binder =
    | Bind : {
        env : ('m, 'a) env;
        body : (('a, 'n) snoc, 's) term;
        ins : ('mn, 'm, 'n) insertion;
      }
        -> ('mn, 's) binder

  (* An (m+n)-dimensional type is "instantiated" by applying it a "boundary tube" to get an m-dimensional type.  This operation is supposed to be functorial in dimensions, so in the normal forms we prevent it from being applied more than once in a row.  We have a separate class of "uninstantiated" values, and then every actual value is instantiated exactly once.  This means that even non-type neutrals must be "instantiated", albeit trivially. *)
  and uninst =
    | UU : 'n D.t -> uninst
    (* Pis must store not just the domain type but all its boundary types.  These domain and boundary types are not fully instantiated.  Note the codomains are stored in a cube of binders. *)
    | Pi : string option * ('k, kinetic value) CubeOf.t * ('k, unit) BindCube.t -> uninst
    (* A neutral is an application spine: a head with a list of applications.  Note that when we inject it into 'value' with Uninst below, it also stores its type (as do all the other uninsts).  It also stores (lazily) the up-to-now result of evaluating that application spine.  If that result is "Unrealized", then it is a "true neutral", the sort of neutral that is permanently stuck and usually appears in paper proofs of normalization.  If it is "Val" then the spine is still waiting for further arguments for its case tree to compute, while if it is "Canonical" then the case tree has already evaluated to a canonical type.  If it is "Realized" then the case tree has already evaluated to an ordinary value; this should only happen when glued evaluation is in effect. *)
    | Neu : { head : head; args : app Bwd.t; value : potential lazy_eval } -> uninst

  and _ value =
    (* An uninstantiated term, together with its type.  The 0-dimensional universe is morally an infinite data structure Uninst (UU 0, (Uninst (UU 0, Uninst (UU 0, ... )))), so we make the type lazy. *)
    | Uninst : uninst * kinetic value Lazy.t -> kinetic value
    (* A term with some nonzero instantiation *)
    | Inst : {
        (* The uninstantiated term being instantiated *)
        tm : uninst;
        (* Require at least one dimension to be instantiated *)
        dim : 'k D.pos;
        (* The arguments for a tube of some dimensions *)
        args : ('n, 'k, 'nk, normal) TubeOf.t;
        (* The types of the arguments remaining to be supplied.  In other words, the type *of* this instantiation is "Inst (UU n, tys)". *)
        tys : (D.zero, 'n, 'n, kinetic value) TubeOf.t;
      }
        -> kinetic value
    (* A constructor has a name, a dimension, and a list of arguments of that dimension.  It must always be applied to the correct number of arguments (otherwise it can be eta-expanded).  It doesn't have an outer insertion because a primitive datatype is always 0-dimensional (it has higher-dimensional versions, but degeneracies can always be pushed inside these).  *)
    | Constr : Constr.t * 'n D.t * ('n, kinetic value) CubeOf.t list -> kinetic value
    (* Lambda-abstractions are never types, so they can never be nontrivially instantiated.  Thus we may as well make them values directly. *)
    | Lam : 'k variables * ('k, 's) binder -> 's value
    (* The same is true for anonymous structs.  They have to store an insertion outside, like an application, to deal with higher-dimensional record types like Gel.  Here 'k is the Gel dimension, with 'n the substitution dimension and 'nk the total dimension. *)
    | Struct : ('p * 's * 'et) StructfieldAbwd.t * ('pk, 'p, 'k) insertion * 's energy -> 's value

  (* This is the result of evaluating a term with a given kind of energy.  Evaluating a kinetic term just produces a (kinetic) value, whereas evaluating a potential term might be a potential value (waiting for more arguments), or else the information that the case tree has reached a leaf and the resulting kinetic value or canonical type, or else the information that the case tree is permanently stuck.  *)
  and _ evaluation =
    (* When 's = potential, a Val means the case tree is not yet fully applied; while when 's = kinetic, it is the only possible kind of result.  Collapsing these two together seems to unify the code for Lam and Struct as much as possible. *)
    | Val : 's value -> 's evaluation
    | Realize : kinetic value -> potential evaluation
    | Unrealized : potential evaluation
    | Canonical : 'm canonical -> potential evaluation

  (* A canonical type value is either a datatype or a codatatype/record.  It is parametrized by its dimension as a type, which might be larger than its evaluation dimension if it has an intrinsic dimension (e.g. Gel). *)
  and _ canonical =
    (* We define a named record type to encapsulate the arguments of Data, rather than using an inline one, so that we can bind its existential variables (https://discuss.ocaml.org/t/annotating-by-an-existential-type/14721).  See the definition below. *)
    | Data : ('m, 'j, 'ij) data_args -> 'm canonical
    (* A codatatype value has an eta flag, an environment that it was evaluated at, an insertion that relates its intrinsic dimension (such as for Gel) to the dimension it was evaluated at, and its fields as unevaluted terms that depend on one additional variable belonging to the codatatype itself (usually through its previous fields).  Note that combining env, ins, and any of the field terms in a *lower* codatafield produces the data of a binder; so in the absence of higher codatatypes we can think of this as a family of binders, one for each field, that share the same environment and insertion.  (But with higher fields this is no longer the case, as the context of the types gets degenerated by their dimension.) *)
    | Codata : ('mn, 'm, 'n, 'c, 'a, 'et) codata_args -> 'mn canonical

  (* A datatype value stores: *)
  and ('m, 'j, 'ij) data_args = {
    (* The dimension to which it is substituted *)
    dim : 'm D.t;
    (* The datatype family after being applied to the parameters but not the indices, e.g. "Vec A".  This is an option ref because it gets set a little later than the rest of the fields are computed, since only when working with the embedding of neutrals into normals do we have the application spine and its type available.  *)
    tyfam : normal Lazy.t option ref;
    (* The indices applied so far, and the number remaining *)
    indices : (('m, normal) CubeOf.t, 'j, 'ij) Fillvec.t;
    (* All the constructors *)
    constrs : (Constr.t, ('m, 'ij) dataconstr) Abwd.t;
    (* Whether it is discrete.  The value `Maybe means that it could be discrete based on its own parameters, indices, and constructor arguments, but either is waiting for its mutual companions to be typechecked, or at least one of them failed to be discrete.  Thus for equality-testing purposes, `Maybe is treated like `No. *)
    discrete : [ `Yes | `Maybe | `No ];
  }

  and ('mn, 'm, 'n, 'c, 'a, 'et) codata_args = {
    eta : (potential, 'et) eta;
    opacity : opacity;
    env : ('m, 'a) env;
    termctx : ('c, ('a, 'n) snoc) termctx option Lazy.t;
    ins : ('mn, 'm, 'n) insertion;
    fields : ('a * 'n * 'et) Term.CodatafieldAbwd.t;
  }

  (* Each constructor stores the telescope of types of its arguments, as a closure, and the index values as function values taking its arguments. *)
  and (_, _) dataconstr =
    | Dataconstr : {
        env : ('m, 'a) env;
        args : ('a, 'p, 'ap) Telescope.t;
        indices : (('ap, kinetic) term, 'ij) Vec.t;
      }
        -> ('m, 'ij) dataconstr

  (* A "normal form" is a value paired with its type.  The type is used for eta-expansion and equality-checking. *)
  and normal = { tm : kinetic value; ty : kinetic value }

  (* An "environment" is a context morphism *from* a De Bruijn LEVEL context *to* a (typechecked) De Bruijn INDEX context.  Specifically, an ('n, 'a) env is an 'n-dimensional substitution from a level context to an index context indexed by the hctx 'a.  Since the index context could have some variables that are labeled by integers together with faces, the values also have to allow that. *)
  and (_, _) env =
    | Emp : 'n D.t -> ('n, emp) env
    (* The (n+k)-cube here is morally a k-cube of n-cubes, representing a k-dimensional "cube variable" consisting of some number of "real" variables indexed by the faces of a k-cube, each of which has an n-cube of values representing a value and its boundaries.  But this contains the same data as an (n+k)-cube since a strict face of (n+k) decomposes uniquely as a strict face of n plus a strict face of k, and it seems to be more convenient to store it as a single (n+k)-cube. *)
    (* We have two kinds of variable bindings in an environment: lazy and non-lazy. *)
    | LazyExt :
        ('n, 'b) env * ('n, 'k, 'nk) D.plus * ('nk, kinetic lazy_eval) CubeOf.t
        -> ('n, ('b, 'k) snoc) env
    (* We also allow Error binding in an environment, indicating that that variable is not actually usable, usually due to an earlier error in typechecking that we've continued on from anyway.  *)
    | Ext :
        ('n, 'b) env
        * ('n, 'k, 'nk) D.plus
        * (('nk, kinetic value) CubeOf.t, Reporter.Code.t) Result.t
        -> ('n, ('b, 'k) snoc) env
    | Act : ('n, 'b) env * ('m, 'n) op -> ('m, 'b) env
    | Permute : ('a, 'b) Tbwd.permute * ('n, 'b) env -> ('n, 'a) env
    (* Adding a dimension 'n to all the dimensions in a dimension list 'b is the power/cotensor in the dimension-enriched category of contexts.  Shifting an environment (substitution) implements its universal property: an (m+n)-dimensional substitution with codomain b is equivalent to an m-dimensional substitution with codomain n+b. *)
    | Shift : ('mn, 'b) env * ('m, 'n, 'mn) D.plus * ('n, 'b, 'nb) Plusmap.t -> ('m, 'nb) env

  (* An 's lazy_eval behaves from the outside like an 's evaluation Lazy.t.  But internally, in addition to being able to store an arbitrary thunk, it can also store a term and an environment in which to evaluate it (plus an outer insertion that can't be pushed into the environment).  This allows it to accept degeneracy actions and incorporate them into the environment, so that when it's eventually forced the term only has to be traversed once.  It can also accumulate degeneracies on an arbitrary thunk (which could, of course, be a constant value that was already forced, but now is deferred again until it's done accumulating degeneracy actions).  Both kinds of deferred values can also store more arguments and field projections for it to be applied to; this is only used in glued evaluation. *)
  and 's lazy_state =
    | Deferred_eval :
        ('m, 'b) env * ('b, 's) term * ('mn, 'm, 'n) insertion * app Bwd.t
        -> 's lazy_state
    | Deferred : (unit -> 's evaluation) * ('m, 'n) deg * app Bwd.t -> 's lazy_state
    | Ready : 's evaluation -> 's lazy_state

  and 's lazy_eval = 's lazy_state ref
end

include Value

type any_canonical = Any : 'm canonical -> any_canonical

(* Every context morphism has a valid dimension. *)
let rec dim_env : type n b. (n, b) env -> n D.t = function
  | Emp n -> n
  | Ext (e, _, _) -> dim_env e
  | LazyExt (e, _, _) -> dim_env e
  | Act (_, op) -> dom_op op
  | Permute (_, e) -> dim_env e
  | Shift (e, mn, _) -> D.plus_left mn (dim_env e)

(* And likewise every binder *)
let dim_binder : type m s. (m, s) binder -> m D.t = function
  | Bind b -> dom_ins b.ins

let dim_canonical : type m. m canonical -> m D.t = function
  | Data { dim; _ } -> dim
  | Codata { ins; _ } -> dom_ins ins

(* The length of an environment is a tbwd of dimensions. *)
let rec length_env : type n b. (n, b) env -> b Dbwd.t = function
  | Emp _ -> Word Zero
  | Ext (env, nk, _) ->
      let (Word le) = length_env env in
      Word (Suc (le, D.plus_right nk))
  | LazyExt (env, nk, _) ->
      let (Word le) = length_env env in
      Word (Suc (le, D.plus_right nk))
  | Act (env, _) -> length_env env
  | Permute (p, env) -> Plusmap.OfDom.permute p (length_env env)
  | Shift (env, mn, nb) -> Plusmap.out (D.plus_right mn) (length_env env) nb

(* Smart constructor that composes actions and cancels identities *)
let rec act_env : type m n b. (n, b) env -> (m, n) op -> (m, b) env =
 fun env s ->
  match env with
  | Act (env, s') -> act_env env (comp_op s' s)
  | _ -> (
      match is_id_op s with
      | Some Eq -> env
      | None -> Act (env, s))

(* Create a lazy evaluation *)
let lazy_eval : type n b s. (n, b) env -> (b, s) term -> s lazy_eval =
 fun env tm -> ref (Deferred_eval (env, tm, ins_zero (dim_env env), Emp))

let defer : type s. (unit -> s evaluation) -> s lazy_eval =
 fun tm -> ref (Deferred (tm, id_deg D.zero, Emp))

let ready : type s. s evaluation -> s lazy_eval = fun ev -> ref (Ready ev)

let apply_lazy : type n s. s lazy_eval -> (n, normal) CubeOf.t -> s lazy_eval =
 fun lev xs ->
  let xs = App (Arg xs, ins_zero (CubeOf.dim xs)) in
  match !lev with
  | Deferred_eval (env, tm, ins, apps) -> ref (Deferred_eval (env, tm, ins, Snoc (apps, xs)))
  | Deferred (tm, ins, apps) -> ref (Deferred (tm, ins, Snoc (apps, xs)))
  | Ready tm -> ref (Deferred ((fun () -> tm), id_deg D.zero, Snoc (Emp, xs)))

(* We defer "field_lazy" to act.ml, since it requires pushing a permutation inside the apps. *)

(* Given a De Bruijn level and a type, build the variable of that level having that type. *)
let var : level -> kinetic value -> kinetic value =
 fun level ty ->
  Uninst
    ( Neu { head = Var { level; deg = id_deg D.zero }; args = Emp; value = ready Unrealized },
      Lazy.from_val ty )

(* Project out a cube or tube of values from a cube or tube of normals *)
let val_of_norm_cube : type n. (n, normal) CubeOf.t -> (n, kinetic value) CubeOf.t =
 fun arg -> CubeOf.mmap { map = (fun _ [ { tm; ty = _ } ] -> tm) } [ arg ]

let val_of_norm_tube : type n k nk.
    (n, k, nk, normal) TubeOf.t -> (n, k, nk, kinetic value) TubeOf.t =
 fun arg -> TubeOf.mmap { map = (fun _ [ { tm; ty = _ } ] -> tm) } [ arg ]

(* Remove an entry from an environment *)
let rec remove_env : type a k b n. (n, b) env -> (a, k, b) Tbwd.insert -> (n, a) env =
 fun env v ->
  match (env, v) with
  | Emp _, _ -> .
  | Act (env, op), _ -> Act (remove_env env v, op)
  | Permute (p, env), _ ->
      let (Permute_insert (v', p')) = Tbwd.permute_insert v p in
      Permute (p', remove_env env v')
  | Ext (env, nk, xs), Later v -> Ext (remove_env env v, nk, xs)
  | LazyExt (env, nk, xs), Later v -> LazyExt (remove_env env v, nk, xs)
  | Ext (env, _, _), Now -> env
  | LazyExt (env, _, _), Now -> env
  | Shift (env, mn, nb), _ ->
      let (Unmap_insert (_, v', na)) = Plusmap.unmap_insert v nb in
      Shift (remove_env env v', mn, na)

(* The universe of any dimension belongs to an instantiation of itself.  Note that the result is not itself a type (i.e. in the 0-dimensional universe) unless n=0. *)
let rec universe : type n. n D.t -> kinetic value = fun n -> Uninst (UU n, lazy (universe_ty n))
and universe_nf : type n. n D.t -> normal = fun n -> { tm = universe n; ty = universe_ty n }

and universe_ty : type n. n D.t -> kinetic value =
 fun n ->
  match D.compare_zero n with
  | Zero -> universe D.zero
  | Pos n' ->
      let args =
        TubeOf.build D.zero (D.zero_plus n)
          {
            build =
              (fun fa ->
                let m = dom_tface fa in
                universe_nf m);
          } in
      Inst { tm = UU n; dim = n'; args; tys = TubeOf.empty D.zero }

(* Glued evaluation is basically implemented, but currently disabled because it is very slow -- too much memory allocation, and OCaml 5 doesn't have memory profiling tools available yet to debug it.  So we disable it globally with this flag.  But all the regular tests pass with the flag enabled, and should continue to be run and to pass, so that once we are able to debug it it is still otherwise working. *)
module GluedEval = struct
  let toggle = false
  let read () = toggle
end
