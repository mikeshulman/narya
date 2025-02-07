open Bwd
open Util
open Tbwd
open Dim
include Energy

(* ******************** Names ******************** *)

(* An element of "mn variables" is an mn-dimensional cube of variables where mn = m + n and the user specified names for n dimensions, with the other m dimensions being named with face suffixes.  *)
type _ variables =
  | Variables :
      'm D.t * ('m, 'n, 'mn) D.plus * (N.zero, 'n, string option, 'f) NICubeOf.t
      -> 'mn variables

type any_variables = Any : 'n variables -> any_variables

let dim_variables : type m. m variables -> m D.t = function
  | Variables (m, mn, _) -> D.plus_out m mn

let singleton_variables : type m. m D.t -> string option -> m variables =
 fun m x -> Variables (m, D.plus_zero m, NICubeOf.singleton x)

(* ******************** Typechecked terms ******************** *)

(* Typechecked, but unevaluated, terms.  Use De Bruijn indices that are intrinsically well-scoped by hctxs, but are no longer separated into synthesizing and checking; hence without type ascriptions.  Note that extending an hctx by a dimension 'k means adding a whole cube of new variables, which are indexed by the position of that dimension together with a strict face of it.  (At user-level, those variables may all be accessed as faces of one "cube variable", or they may have independent names, but internally there is no difference.)

   Incorporates information appropriate to the internal syntax that is constructed during typechecking, e.g. applications and abstractions are grouped by a dimension, since this can be inferred during typechecking, from the synthesized type of a function being applied and from the pi-type the lambda is being checked against, respectively.  Similarly, we have instantiations of higher-dimensional types obtained by applying them to a tube of boundary terms.

   Typechecking of user syntax still produces only unary pi-types and zero-dimensional universes, but we include arbitrary-dimensional ones here so that they can also be the output of readback from internal values.  We likewise include arbitrary degeneracy actions, since these can appear in readback. *)

(* The codomain of a higher-dimensional pi-type is a cube of terms with bound variables whose number varies with the face of the cube.  We can enforce this with a parametrized instance of Cube, but it has to be defined recursively with term using a recursive module (like BindCube in Value; see there for more commentary). *)
module rec Term : sig
  module CodFam : sig
    type ('k, 'a) t = (('a, 'k) snoc, kinetic) Term.term
  end

  module CodCube : module type of Cube (CodFam)

  type _ index = Index : ('a, 'n, 'b) Tbwd.insert * ('k, 'n) sface -> 'b index

  type (_, _) term =
    | Var : 'a index -> ('a, kinetic) term
    | Const : Constant.t -> ('a, kinetic) term
    | Meta : ('x, 'b, 'l) Meta.t * 's energy -> ('b, 's) term
    | MetaEnv : ('x, 'b, 's) Meta.t * ('a, 'n, 'b) env -> ('a, kinetic) term
    | Field : ('a, kinetic) term * Field.t * ('nk, 'n, 'k) insertion -> ('a, kinetic) term
    | UU : 'n D.t -> ('a, kinetic) term
    | Inst : ('a, kinetic) term * ('m, 'n, 'mn, ('a, kinetic) term) TubeOf.t -> ('a, kinetic) term
    | Pi :
        string option * ('n, ('a, kinetic) term) CubeOf.t * ('n, 'a) CodCube.t
        -> ('a, kinetic) term
    | App : ('a, kinetic) term * ('n, ('a, kinetic) term) CubeOf.t -> ('a, kinetic) term
    | Constr : Constr.t * 'n D.t * ('n, ('a, kinetic) term) CubeOf.t list -> ('a, kinetic) term
    | Act : ('a, kinetic) term * ('m, 'n) deg -> ('a, kinetic) term
    | Let : string option * ('a, kinetic) term * (('a, D.zero) snoc, 's) term -> ('a, 's) term
    | Lam : 'n variables * (('a, 'n) snoc, 's) Term.term -> ('a, 's) term
    | Struct :
        's eta
        * 'n D.t
        * ( Field.t,
            ('n, (('a, 's) term * [ `Labeled | `Unlabeled ]) option) PbijmapOf.wrapped )
          Abwd.t
        * 's energy
        -> ('a, 's) term
    | Match : {
        tm : ('a, kinetic) term;
        dim : 'n D.t;
        branches : ('a, 'n) branch Constr.Map.t;
      }
        -> ('a, potential) term
    | Realize : ('a, kinetic) term -> ('a, potential) term
    | Canonical : 'a canonical -> ('a, potential) term

  and (_, _) branch =
    | Branch :
        ('a, 'b, 'n, 'ab) Tbwd.snocs * ('c, 'ab) Tbwd.permute * ('c, potential) term
        -> ('a, 'n) branch
    | Refute

  and _ canonical =
    | Data : {
        indices : 'i Fwn.t;
        constrs : (Constr.t, ('a, 'i) dataconstr) Abwd.t;
        discrete : [ `Yes | `Maybe | `No ];
      }
        -> 'a canonical
    | Codata : {
        eta : potential eta;
        opacity : opacity;
        dim : 'n D.t;
        fields : (Field.t, ('a, 'n) codatafield) Abwd.t;
      }
        -> 'a canonical

  and (_, _) dataconstr =
    | Dataconstr : {
        args : ('p, 'a, 'pa) tel;
        indices : (('pa, kinetic) term, 'i) Vec.t;
      }
        -> ('p, 'i) dataconstr

  and (_, _) codatafield =
    | Lower_codatafield : (('a, 'n) snoc, kinetic) term -> ('a, 'n) codatafield
    | Higher_codatafield :
        'k D.pos * ('k, ('a, D.zero) snoc, 'kan) Plusmap.t * ('kan, kinetic) term
        -> ('a, D.zero) codatafield

  and ('a, 'b, 'ab) tel =
    | Emp : ('a, Fwn.zero, 'a) tel
    | Ext :
        string option * ('a, kinetic) term * (('a, D.zero) snoc, 'b, 'ab) tel
        -> ('a, 'b Fwn.suc, 'ab) tel

  and (_, _, _) env =
    | Emp : 'n D.t -> ('a, 'n, emp) env
    | Ext :
        ('a, 'n, 'b) env * ('n, 'k, 'nk) D.plus * ('nk, ('a, kinetic) term) CubeOf.t
        -> ('a, 'n, ('b, 'k) snoc) env
end = struct
  module CodFam = struct
    type ('k, 'a) t = (('a, 'k) snoc, kinetic) Term.term
  end

  module CodCube = Cube (CodFam)

  (* A typechecked De Bruijn index is a well-scoped natural number together with a definite strict face (the top face, if none was supplied explicitly).  Unlike a raw De Bruijn index, the scoping is by a tbwd rather than a type-level nat.  This allows the face to also be well-scoped: its codomain must be the dimension appearing in the hctx at that position.  And since we already have defined Tbwd.insert, we can re-use that instead of re-defining this inductively. *)
  type _ index = Index : ('a, 'n, 'b) Tbwd.insert * ('k, 'n) sface -> 'b index

  type (_, _) term =
    (* Most term-formers only appear in kinetic (ordinary) terms. *)
    | Var : 'a index -> ('a, kinetic) term
    | Const : Constant.t -> ('a, kinetic) term
    | Meta : ('x, 'b, 'l) Meta.t * 's energy -> ('b, 's) term
    (* Normally, checked metavariables don't require an environment attached, but they do when they arise by readback from a value metavariable. *)
    | MetaEnv : ('x, 'b, 's) Meta.t * ('a, 'n, 'b) env -> ('a, kinetic) term
    | Field : ('a, kinetic) term * Field.t * ('nk, 'n, 'k) insertion -> ('a, kinetic) term
    | UU : 'n D.t -> ('a, kinetic) term
    | Inst : ('a, kinetic) term * ('m, 'n, 'mn, ('a, kinetic) term) TubeOf.t -> ('a, kinetic) term
    (* Since the user doesn't write higher-dimensional pi-types explicitly, there is always only one variable name in a pi-type. *)
    | Pi :
        string option * ('n, ('a, kinetic) term) CubeOf.t * ('n, 'a) CodCube.t
        -> ('a, kinetic) term
    | App : ('a, kinetic) term * ('n, ('a, kinetic) term) CubeOf.t -> ('a, kinetic) term
    | Constr : Constr.t * 'n D.t * ('n, ('a, kinetic) term) CubeOf.t list -> ('a, kinetic) term
    | Act : ('a, kinetic) term * ('m, 'n) deg -> ('a, kinetic) term
    (* The term being bound in a 'let' is always kinetic.  Thus, if the supplied bound term is potential, the "bound term" here must be the metavariable whose value is set to that term rather than to the (potential) term itself.  We don't need a term-level "letrec" since recursion is implemented in the typechecker by creating a new global metavariable. *)
    | Let : string option * ('a, kinetic) term * (('a, D.zero) snoc, 's) term -> ('a, 's) term
    (* Abstractions and structs can appear in any kind of term.  The dimension 'n is the substitution dimension of the type being checked against (function-type or codata/record).  *)
    | Lam : 'n variables * (('a, 'n) snoc, 's) Term.term -> ('a, 's) term
    | Struct :
        's eta
        * 'n D.t
        (* TODO: I think the 'a here is wrong: it should have a Plusmap of the 'remaining dimension of the pbij applied to it.  In particular, that's what I would expect to get out when typechecking higher fields, since that is done in a degenerated context.  If so, that means Pbijmap needs to be a functor depending on a Fam depending on the 'remaining dimension, and be applied here in the recursive module like CodCube.  It also means the definition of eval on Struct is wrong, since the types won't match, but I'm not sure how to fix it.  Perhaps a Value.Struct has to store fields separately from their closure environment rather than as individual lazy_evals, since some of them won't be evaluable unless a big enough degeneracy is applied?  *)
        * ( Field.t,
            ('n, (('a, 's) term * [ `Labeled | `Unlabeled ]) option) PbijmapOf.wrapped )
          Abwd.t
        * 's energy
        -> ('a, 's) term
    (* Matches can only appear in non-kinetic terms.  The dimension 'n is the substitution dimension of the type of the variable being matched against. *)
    | Match : {
        tm : ('a, kinetic) term;
        dim : 'n D.t;
        branches : ('a, 'n) branch Constr.Map.t;
      }
        -> ('a, potential) term
    (* A potential term is "realized" by kinetic terms, or canonical types, at its leaves. *)
    | Realize : ('a, kinetic) term -> ('a, potential) term
    | Canonical : 'a canonical -> ('a, potential) term

  (* A branch of a match binds a number of new variables.  If it is a higher-dimensional match, then each of those "variables" is actually a full cube of variables.  In addition, its context must be permuted to put those new variables before the existing variables that are now defined in terms of them. *)
  and (_, _) branch =
    | Branch :
        ('a, 'b, 'n, 'ab) Tbwd.snocs * ('c, 'ab) Tbwd.permute * ('c, potential) term
        -> ('a, 'n) branch
    (* A branch that was refuted during typechecking doesn't need a body to compute with, but we still mark its presence as a signal that it should be stuck (this can occur when normalizing in an inconsistent context). *)
    | Refute

  (* A canonical type is either a datatype or a codatatype/record. *)
  and _ canonical =
    (* A datatype stores its family of constructors, and also its number of indices.  (The former is not determined in the latter if there happen to be zero constructors). *)
    | Data : {
        indices : 'i Fwn.t;
        constrs : (Constr.t, ('a, 'i) dataconstr) Abwd.t;
        discrete : [ `Yes | `Maybe | `No ];
      }
        -> 'a canonical
    (* A codatatype has an eta flag, an intrinsic dimension (like Gel), and a family of fields, each with a type that depends on one additional variable belonging to the codatatype itself (usually by way of its previous fields).  We retain the order of the fields by storing them in an Abwd rather than a Map so as to enable positional access as well as named access. *)
    | Codata : {
        eta : potential eta;
        opacity : opacity;
        dim : 'n D.t;
        fields : (Field.t, ('a, 'n) codatafield) Abwd.t;
      }
        -> 'a canonical

  (* A datatype constructor has a telescope of arguments and a list of index values depending on those arguments. *)
  and (_, _) dataconstr =
    | Dataconstr : {
        args : ('p, 'a, 'pa) tel;
        indices : (('pa, kinetic) term, 'i) Vec.t;
      }
        -> ('p, 'i) dataconstr

  (* A codatafield has an intrinsic dimension, and a type that depends on one additional variable, but in a degenerated context.  If it is zero-dimensional, the degeneration does nothing, but we store that case separately so we don't need to construct and carry around lots of trivial Plusmaps. *)
  and (_, _) codatafield =
    | Lower_codatafield : (('a, 'n) snoc, kinetic) term -> ('a, 'n) codatafield
    (* For the present, we don't allow higher fields in higher-dimensional codatatypes, just for simplicity. *)
    | Higher_codatafield :
        'k D.pos * ('k, ('a, D.zero) snoc, 'kan) Plusmap.t * ('kan, kinetic) term
        -> ('a, D.zero) codatafield

  (* A telescope is a list of types, each dependent on the previous ones.  Note that 'a and 'ab are lists of dimensions, but 'b is just a forwards natural number counting the number of *zero-dimensional* variables added to 'a to get 'ab.  *)
  and ('a, 'b, 'ab) tel =
    | Emp : ('a, Fwn.zero, 'a) tel
    | Ext :
        string option * ('a, kinetic) term * (('a, D.zero) snoc, 'b, 'ab) tel
        -> ('a, 'b Fwn.suc, 'ab) tel

  (* A version of an environment (see below) that involves terms rather than values.  Used mainly when reading back metavariables. *)
  and (_, _, _) env =
    | Emp : 'n D.t -> ('a, 'n, emp) env
    | Ext :
        ('a, 'n, 'b) env * ('n, 'k, 'nk) D.plus * ('nk, ('a, kinetic) term) CubeOf.t
        -> ('a, 'n, ('b, 'k) snoc) env
end

open Term

(* Find the name of the (n+1)st abstracted variable, where n is the length of a supplied argument list.  Doesn't "look through" branches or cobranches or into leaves. *)
let rec nth_var : type a b s. (a, s) term -> b Bwd.t -> any_variables option =
 fun tr args ->
  match tr with
  | Lam (x, body) -> (
      match args with
      | Emp -> Some (Any x)
      | Snoc (args, _) -> nth_var body args)
  | _ -> None

let pi x dom cod = Pi (x, CubeOf.singleton dom, CodCube.singleton cod)
let app fn arg = App (fn, CubeOf.singleton arg)
let apps fn args = List.fold_left app fn args
let constr name args = Constr (name, D.zero, List.map CubeOf.singleton args)

module Telescope = struct
  type ('a, 'b, 'ab) t = ('a, 'b, 'ab) Term.tel

  let rec length : type a b ab. (a, b, ab) t -> b Fwn.t = function
    | Emp -> Zero
    | Ext (_, _, tel) -> Suc (length tel)

  let rec pis : type a b ab. (a, b, ab) t -> (ab, kinetic) term -> (a, kinetic) term =
   fun doms cod ->
    match doms with
    | Emp -> cod
    | Ext (x, dom, doms) -> pi x dom (pis doms cod)

  let rec lams : type a b ab. (a, b, ab) t -> (ab, kinetic) term -> (a, kinetic) term =
   fun doms body ->
    match doms with
    | Emp -> body
    | Ext (x, _, doms) -> Lam (singleton_variables D.zero x, lams doms body)

  let rec snocs : type a b ab. (a, b, ab) t -> (a, b, D.zero, ab) Tbwd.snocs = function
    | Emp -> Zero
    | Ext (_, _, tel) -> Suc (snocs tel)
end

let rec dim_term_env : type a n b. (a, n, b) env -> n D.t = function
  | Emp n -> n
  | Ext (e, _, _) -> dim_term_env e

let dim_codatafield : type a n. (a, n) codatafield -> dim_wrapped = function
  | Lower_codatafield _ -> Wrap D.zero
  | Higher_codatafield (k, _, _) -> Wrap (D.pos k)

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

  type head =
    | Var : { level : level; deg : ('m, 'n) deg } -> head
    | Const : { name : Constant.t; ins : ('a, 'b, 'c) insertion } -> head
    | Meta : {
        meta : ('a, 'b, 's) Meta.t;
        env : ('m, 'b) env;
        ins : ('mn, 'm, 'n) insertion;
      }
        -> head

  and 'n arg =
    | Arg : ('n, normal) CubeOf.t -> 'n arg
    | Field : Field.t * ('n, 'k, 'nk) D.plus -> 'n arg

  and app = App : 'n arg * ('m, 'n, 'k) insertion -> app

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
    | Struct :
        (Field.t, ('n, ('s lazy_eval * [ `Labeled | `Unlabeled ]) option) PbijmapOf.wrapped) Abwd.t
        * ('nk, 'n, 'k) insertion
        * 's energy
        -> 's value

  and _ evaluation =
    | Val : 's value -> 's evaluation
    | Realize : kinetic value -> potential evaluation
    | Unrealized : potential evaluation
    | Canonical : 'm canonical -> potential evaluation

  and _ canonical =
    | Data : ('m, 'j, 'ij) data_args -> 'm canonical
    | Codata : {
        eta : potential eta;
        opacity : opacity;
        env : ('m, 'a) env;
        ins : ('mn, 'm, 'n) insertion;
        fields : (Field.t, ('a, 'n) codatafield) Abwd.t;
      }
        -> 'mn canonical

  and ('m, 'j, 'ij) data_args = {
    dim : 'm D.t;
    tyfam : normal Lazy.t option ref;
    indices : (('m, normal) CubeOf.t, 'j, 'ij) Fillvec.t;
    constrs : (Constr.t, ('m, 'ij) dataconstr) Abwd.t;
    discrete : [ `Yes | `Maybe | `No ];
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
  and 'n arg =
    | Arg : ('n, normal) CubeOf.t -> 'n arg
    (* For a higher field, the actual evaluation dimension is 'nk, but the result dimension is only 'n.  So the dimension of the arg is 'n, since that's the output dimension that a degeneracy acting on could be pushed through.  However, since a degeneracy of dimension up to 'nk can act on the inside, we can push in the whole insertion and store only a plus outside. *)
    | Field : Field.t * ('n, 'k, 'nk) D.plus -> 'n arg

  and app = App : 'n arg * ('m, 'n, 'k) insertion -> app

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
    (* The same is true for anonymous structs.  These have to store an insertion outside, like an application, to deal with higher-dimensional record types like Gel (here 'k would be the Gel dimension, with 'n the substitution dimension and 'nk the total dimension).  We also remember which fields are labeled, for readback purposes.  We store the value of each field lazily, so that corecursive definitions don't try to compute an entire infinite structure.  And since in the non-kinetic case, evaluation can produce more data than just a term (e.g. whether a case tree has yet reached a leaf), what we store lazily is the result of evaluation.  Finally, each field name is associated with a partial bijection in the case of a higher codatatype. *)
    | Struct :
        (Field.t, ('n, ('s lazy_eval * [ `Labeled | `Unlabeled ]) option) PbijmapOf.wrapped) Abwd.t
        * ('nk, 'n, 'k) insertion
        * 's energy
        -> 's value

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
    | Codata : {
        eta : potential eta;
        opacity : opacity;
        env : ('m, 'a) env;
        ins : ('mn, 'm, 'n) insertion;
        (* TODO: When it's used, this should really be a forwards list.  But it's naturally constructed backwards, and it has to be used *as* it's being constructed when typechecking the later terms. *)
        fields : (Field.t, ('a, 'n) codatafield) Abwd.t;
      }
        -> 'mn canonical

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

open Value

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
let rec length_env : type n b. (n, b) env -> b Plusmap.OfDom.t = function
  | Emp _ -> Of_emp
  | Ext (env, nk, _) -> Of_snoc (length_env env, D.plus_right nk)
  | LazyExt (env, nk, _) -> Of_snoc (length_env env, D.plus_right nk)
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

let val_of_norm_tube :
    type n k nk. (n, k, nk, normal) TubeOf.t -> (n, k, nk, kinetic value) TubeOf.t =
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
