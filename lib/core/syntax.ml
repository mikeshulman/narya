open Bwd
open Util
open Tbwd
open Dim
open Asai.Range
open Reporter

(* ******************** Groups of terms ******************** *)

(* At both the checked and the value level we have actually two different types to define: ordinary terms and case trees.  However, there is some overlap in the types of constructors and operations that these support: they can both contain lambda-abstractions and structs.  Thus, to avoid duplication of code, we actually define both together as one GADT type family, indexed by a two-element type to distinguish them.  We name the two groups after the two kinds of energy:

   - Ordinary terms are "kinetic", because ordinary computation applies directly to them.
   - Case trees are "potential", because they don't compute until enough arguments are applied to reach a leaf of the case tree.  That leaf can be either a kinetic term or information about a canonical type (which is not a computation, just a specification of behavior).
*)

type kinetic = Dummy_kinetic
type potential = Dummy_potential
type _ energy = Kinetic : kinetic energy | Potential : potential energy

(* Structs can have or lack eta-conversion, but the only kinetic ones are the ones with eta (records). *)
type _ eta = Eta : 's eta | Noeta : potential eta

(* ******************** Raw (unchecked) terms ******************** *)

module Raw = struct
  (* Raw (unchecked) terms, using intrinsically well-scoped De Bruijn indices, and separated into synthesizing terms and checking terms.  These match the user-facing syntax rather than the internal syntax.  In particular, applications, abstractions, and pi-types are all unary, there is only one universe, and the only operator actions are refl (including Id) and sym. *)

  (* A raw De Bruijn index is a well-scoped natural number together with a possible face.  During typechecking we will verify that the face, if given, is applicable to the variable as a "cube variable", and compile the combination into a more strongly well-scoped kind of index. *)
  type 'a index = 'a N.index * any_sface option

  type _ synth =
    | Var : 'a index -> 'a synth
    | Const : Constant.t -> 'a synth
    | Field : 'a synth located * Field.or_index -> 'a synth
    | Pi : string option * 'a check located * 'a N.suc check located -> 'a synth
    | App : 'a synth located * 'a check located -> 'a synth
    | Asc : 'a check located * 'a check located -> 'a synth
    | Let : string option * 'a synth located * 'a N.suc synth located -> 'a synth
    | UU : 'a synth
    | Act : string * ('m, 'n) deg * 'a synth located -> 'a synth

  and _ check =
    | Synth : 'a synth -> 'a check
    | Lam : string option located * [ `Cube | `Normal ] * 'a N.suc check located -> 'a check
    (* A "Struct" is our current name for both tuples and comatches, which share a lot of their implementation even though they are conceptually and syntactically distinct.  Those with eta=`Eta are tuples, those with eta=`Noeta are comatches.  We index them by a "Field.t option" so as to include any unlabeled fields, with their relative order to the labeled ones. *)
    | Struct : 's eta * (Field.t option, 'a check located) Abwd.t -> 'a check
    | Constr : Constr.t located * 'a check located Bwd.t -> 'a check
    | Match : 'a index * 'a branch list -> 'a check
    (* "[]", which could be either an empty match or an empty comatch *)
    | Empty_co_match : 'a check
    | Data : (Constr.t, 'a dataconstr located) Abwd.t -> 'a check
    | Codata :
        potential eta * ('a, 'ac) codata_vars * (Field.t, 'ac check located) Abwd.t
        -> 'a check

  and _ branch =
    (* The location of the third argument is that of the entire pattern. *)
    | Branch :
        Constr.t located
        * (string option, 'b) Vec.t
        * ('a, 'b, 'ab) Fwn.bplus located
        * 'ab check located
        -> 'a branch

  and _ dataconstr = Dataconstr : ('a, 'b, 'ab) tel * 'ab check located -> 'a dataconstr

  (* A normal codatatype binds one more "self" variable in the types of its fields.  A normal record type does the same, except that the user doesn't have a name for that variable and instead accesses it by lexical variables that postprocess to its fields using Varscope. *)
  and (_, _) codata_vars =
    | Cube : string option -> ('a, 'a N.suc) codata_vars
    (* A higher-dimensional codatatype simply binds a "self" cube of variables, but unfortunately a higher-dimensional record type doesn't have any variable to make a cube.  So we allow the user to specify either a single cube variable name (thereby also accidentally giving access to the internal previously unnamed variable) or a list of ordinary variables to be its boundary only.  Thus, in practice below 'c must be a number of faces associated to a dimension, but the parser doesn't know the dimension, so it can't ensure that.  The unnamed internal variable is included as the last one.  (TODO: This Bwv really ought to be a forwards Vec, but that would require changing too much else for now, such as making count_faces return a Fwn.) *)
    | Normal : ('a, 'c, 'ac) N.plus located * (string option, 'c) Bwv.t -> ('a, 'ac) codata_vars

  (* An ('a, 'b, 'ab) tel is a raw telescope of length 'b in context 'a, with 'ab = 'a+'b the extended context. *)
  and (_, _, _) tel =
    | Emp : ('a, Fwn.zero, 'a) tel
    | Ext : string option * 'a check located * ('a N.suc, 'b, 'ab) tel -> ('a, 'b Fwn.suc, 'ab) tel

  let rec dataconstr_of_pi : type a. a check located -> a dataconstr =
   fun ty ->
    match ty.value with
    | Synth (Pi (x, dom, cod)) ->
        let (Dataconstr (tel, out)) = dataconstr_of_pi cod in
        Dataconstr (Ext (x, dom, tel), out)
    | _ -> Dataconstr (Emp, ty)
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
    type ('k, 'a) t = (('a, 'k) snoc, kinetic) Term.term
  end

  module CodCube : module type of Cube (CodFam)

  type 'a index =
    | Top : ('k, 'n) sface -> ('a, 'n) snoc index
    | Pop : 'xs index -> ('xs, 'x) snoc index

  type (_, _) term =
    | Var : 'a index -> ('a, kinetic) term
    | Const : Constant.t -> ('a, kinetic) term
    | Field : ('a, kinetic) term * Field.t -> ('a, kinetic) term
    | UU : 'n D.t -> ('a, kinetic) term
    | Inst : ('a, kinetic) term * ('m, 'n, 'mn, ('a, kinetic) term) TubeOf.t -> ('a, kinetic) term
    | Pi :
        string option * ('n, ('a, kinetic) term) CubeOf.t * ('n, 'a) CodCube.t
        -> ('a, kinetic) term
    | App : ('a, kinetic) term * ('n, ('a, kinetic) term) CubeOf.t -> ('a, kinetic) term
    | Constr : Constr.t * 'n D.t * ('n, ('a, kinetic) term) CubeOf.t Bwd.t -> ('a, kinetic) term
    | Act : ('a, kinetic) term * ('m, 'n) deg -> ('a, kinetic) term
    | Let :
        string option * ('a, kinetic) term * (('a, D.zero) snoc, kinetic) term
        -> ('a, kinetic) term
    | Lam : 'n D.t * 'n variables * (('a, 'n) snoc, 's) Term.term -> ('a, 's) term
    | Struct : 's eta * (Field.t, ('a, 's) term * [ `Labeled | `Unlabeled ]) Abwd.t -> ('a, 's) term
    | Match : 'a index * 'n D.t * ('a, 'n) branch Constr.Map.t -> ('a, potential) term
    | Realize : ('a, kinetic) term -> ('a, potential) term
    | Canonical : 'a canonical -> ('a, potential) term

  and (_, _) branch =
    | Branch :
        ('a, 'b, 'n, 'ab) Tbwd.snocs * ('c, 'ab) Tbwd.permute * ('c, potential) term
        -> ('a, 'n) branch

  and _ canonical =
    | Data : 'i N.t * ('a, 'i) dataconstr Constr.Map.t -> 'a canonical
    | Codata :
        potential eta * 'n D.t * (Field.t, (('a, 'n) snoc, kinetic) term) Abwd.t
        -> 'a canonical

  and (_, _) dataconstr =
    | Dataconstr : {
        args : ('p, 'a, 'pa) tel;
        indices : (('pa, kinetic) term, 'i) Bwv.t;
      }
        -> ('p, 'i) dataconstr

  and ('a, 'b, 'ab) tel =
    | Emp : ('a, Fwn.zero, 'a) tel
    | Ext :
        string option * ('a, kinetic) term * (('a, D.zero) snoc, 'b, 'ab) tel
        -> ('a, 'b Fwn.suc, 'ab) tel
end = struct
  module CodFam = struct
    type ('k, 'a) t = (('a, 'k) snoc, kinetic) Term.term
  end

  module CodCube = Cube (CodFam)

  (* A typechecked De Bruijn index is a well-scoped natural number together with a definite strict face (the top face, if none was supplied explicitly).  Unlike a raw De Bruijn index, the scoping is by an hctx rather than a type-level nat.  This allows the face to also be well-scoped: its codomain must be the dimension appearing in the hctx at that position. *)
  type 'a index =
    | Top : ('k, 'n) sface -> ('a, 'n) snoc index
    | Pop : 'xs index -> ('xs, 'x) snoc index

  type (_, _) term =
    (* Most term-formers only appear in kinetic (ordinary) terms. *)
    | Var : 'a index -> ('a, kinetic) term
    | Const : Constant.t -> ('a, kinetic) term
    | Field : ('a, kinetic) term * Field.t -> ('a, kinetic) term
    | UU : 'n D.t -> ('a, kinetic) term
    | Inst : ('a, kinetic) term * ('m, 'n, 'mn, ('a, kinetic) term) TubeOf.t -> ('a, kinetic) term
    (* Since the user doesn't write higher-dimensional pi-types explicitly, there is always only one variable name in a pi-type. *)
    | Pi :
        string option * ('n, ('a, kinetic) term) CubeOf.t * ('n, 'a) CodCube.t
        -> ('a, kinetic) term
    | App : ('a, kinetic) term * ('n, ('a, kinetic) term) CubeOf.t -> ('a, kinetic) term
    | Constr : Constr.t * 'n D.t * ('n, ('a, kinetic) term) CubeOf.t Bwd.t -> ('a, kinetic) term
    | Act : ('a, kinetic) term * ('m, 'n) deg -> ('a, kinetic) term
    | Let :
        string option * ('a, kinetic) term * (('a, D.zero) snoc, kinetic) term
        -> ('a, kinetic) term
    (* Abstractions and structs can appear in any kind of term. *)
    | Lam : 'n D.t * 'n variables * (('a, 'n) snoc, 's) Term.term -> ('a, 's) term
    | Struct : 's eta * (Field.t, ('a, 's) term * [ `Labeled | `Unlabeled ]) Abwd.t -> ('a, 's) term
    (* Matches can only appear in non-kinetic terms. *)
    | Match : 'a index * 'n D.t * ('a, 'n) branch Constr.Map.t -> ('a, potential) term
    (* A potential term is "realized" by kinetic terms, or canonical types, at its leaves. *)
    | Realize : ('a, kinetic) term -> ('a, potential) term
    | Canonical : 'a canonical -> ('a, potential) term

  (* A branch of a match binds a number of new variables.  If it is a higher-dimensional match, then each of those "variables" is actually a full cube of variables.  In addition, its context must be permuted to put those new variables before the existing variables that are now defined in terms of them. *)
  and (_, _) branch =
    | Branch :
        ('a, 'b, 'n, 'ab) Tbwd.snocs * ('c, 'ab) Tbwd.permute * ('c, potential) term
        -> ('a, 'n) branch

  (* A canonical type is either a datatype or a codatatype/record. *)
  and _ canonical =
    (* A datatype stores its family of constructors, and also its number of indices.  (The former is not determined in the latter if there happen to be zero constructors). *)
    | Data : 'i N.t * ('a, 'i) dataconstr Constr.Map.t -> 'a canonical
    (* A codatatype has an eta flag, an intrinsic dimension (like Gel), and a family of fields, each with a type that depends on one additional variable belonging to the codatatype itself (usually by way of its previous fields). *)
    | Codata :
        potential eta * 'n D.t * (Field.t, (('a, 'n) snoc, kinetic) term) Abwd.t
        -> 'a canonical

  (* A datatype constructor has a telescope of arguments and a list of index values depending on those arguments. *)
  and (_, _) dataconstr =
    | Dataconstr : {
        args : ('p, 'a, 'pa) tel;
        indices : (('pa, kinetic) term, 'i) Bwv.t;
      }
        -> ('p, 'i) dataconstr

  (* A telescope is a list of types, each dependent on the previous ones. *)
  and ('a, 'b, 'ab) tel =
    | Emp : ('a, Fwn.zero, 'a) tel
    | Ext :
        string option * ('a, kinetic) term * (('a, D.zero) snoc, 'b, 'ab) tel
        -> ('a, 'b Fwn.suc, 'ab) tel
end

open Term

(* Find the name of the (n+1)st abstracted variable, where n is the length of a supplied argument list.  Doesn't "look through" branches or cobranches or into leaves. *)
let rec nth_var : type a b s. (a, s) term -> b Bwd.t -> any_variables option =
 fun tr args ->
  match tr with
  | Lam (_, x, body) -> (
      match args with
      | Emp -> Some (Any x)
      | Snoc (args, _) -> nth_var body args)
  | _ -> None

let pi x dom cod = Pi (x, CubeOf.singleton dom, CodCube.singleton cod)
let app fn arg = App (fn, CubeOf.singleton arg)
let apps fn args = List.fold_left app fn args
let constr name args = Constr (name, D.zero, Bwd.map CubeOf.singleton args)

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
    | Ext (x, _, doms) -> Lam (D.zero, singleton_variables D.zero x, lams doms body)
end

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

  type var
  type const

  type 'h head =
    | Var : { level : level; deg : ('m, 'n) deg } -> var head
    | Const : { name : Constant.t; ins : ('a, 'b, 'c) insertion } -> const head

  and 'n arg = Arg of ('n, normal) CubeOf.t | Field of Field.t
  and app = App : 'n arg * ('m, 'n, 'k) insertion -> app

  and (_, _) binder =
    | Bind : {
        env : ('m, 'a) env;
        body : (('a, 'n) snoc, 's) term;
        ins : ('mn, 'm, 'n) insertion;
      }
        -> ('mn, 's) binder

  and _ alignment =
    | True : 'h alignment
    | Chaotic : potential value -> const alignment
    | Lawful : canonical -> const alignment

  and uninst =
    | UU : 'n D.t -> uninst
    | Pi : string option * ('k, kinetic value) CubeOf.t * ('k, unit) BindCube.t -> uninst
    | Neu : { head : 'h head; args : app Bwd.t; alignment : 'h alignment } -> uninst

  and _ value =
    | Uninst : uninst * kinetic value Lazy.t -> kinetic value
    | Inst : {
        tm : uninst;
        dim : 'k D.pos;
        args : ('n, 'k, 'nk, normal) TubeOf.t;
        tys : (D.zero, 'n, 'n, kinetic value) TubeOf.t;
      }
        -> kinetic value
    | Constr : Constr.t * 'n D.t * ('n, kinetic value) CubeOf.t Bwd.t -> kinetic value
    | Lam : 'k variables * ('k, 's) binder -> 's value
    | Struct :
        (Field.t, 's evaluation Lazy.t * [ `Labeled | `Unlabeled ]) Abwd.t * ('m, 'n, 'k) insertion
        -> 's value
    | Lazy : 's value Lazy.t -> 's value

  and _ evaluation =
    | Val : 's value -> 's evaluation
    | Realize : kinetic value -> potential evaluation
    | Unrealized : potential evaluation
    | Canonical : canonical -> potential evaluation

  and canonical =
    | Data : {
        dim : 'm D.t;
        indices : (('m, normal) CubeOf.t, 'i) Bwv.t;
        missing : ('i, 'j, 'ij) N.plus;
        constrs : ('m, 'ij) dataconstr Constr.Map.t;
      }
        -> canonical
    | Codata : {
        eta : potential eta;
        env : ('m, 'a) env;
        ins : ('mn, 'm, 'n) insertion;
        fields : (Field.t, (('a, 'n) snoc, kinetic) term) Abwd.t;
      }
        -> canonical

  and (_, _) dataconstr =
    | Dataconstr : {
        env : ('m, 'a) env;
        args : ('a, 'p, 'ap) Telescope.t;
        indices : (('ap, kinetic) term, 'ij) Bwv.t;
      }
        -> ('m, 'ij) dataconstr

  and normal = { tm : kinetic value; ty : kinetic value }

  and (_, _) env =
    | Emp : 'n D.t -> ('n, emp) env
    | Ext : ('n, 'b) env * ('k, ('n, kinetic value) CubeOf.t) CubeOf.t -> ('n, ('b, 'k) snoc) env
    | Act : ('n, 'b) env * ('m, 'n) op -> ('m, 'b) env
end = struct
  (* Here is the recursive application of the functor Cube.  First we define a module to pass as its argument, with type defined to equal the yet-to-be-defined binder, referred to recursively. *)
  module BindFam = struct
    type ('k, 'b) t = ('k, kinetic) Value.binder
  end

  module BindCube = Cube (BindFam)

  type var = private Dummy_var
  type const = private Dummy_const

  (* The head of an elimination spine is either a variable or a constant.  We define this type to be parametrized over a pair of dummy indices indicating which it is, so that most of the time we can treat them equally by parametrizing over the index, but in some places (e.g. alignment) we can specify that only one kind of head is allowed. *)
  type _ head =
    (* A variable is determined by a De Bruijn LEVEL, and stores a neutral degeneracy applied to it. *)
    | Var : { level : level; deg : ('m, 'n) deg } -> var head
    (* A constant also stores a dimension that it is substituted to and a neutral insertion applied to it.  Many constants are zero-dimensional, meaning that 'c' is zero, and hence a=b is just a dimension and the insertion is trivial. *)
    | Const : { name : Constant.t; ins : ('a, 'b, 'c) insertion } -> const head

  (* An application contains the data of an n-dimensional argument and its boundary, together with a neutral insertion applied outside that can't be pushed in.  This represents the *argument list* of a single application, not the function.  Thus, an application spine will be a head together with a list of apps. *)
  and 'n arg =
    | Arg of ('n, normal) CubeOf.t
    (* Fields don't store the dimension explicitly; the same field name is used at all dimensions.  But the dimension is implicitly stored in the insertion that appears on an "app". *)
    | Field of Field.t

  and app = App : 'n arg * ('m, 'n, 'k) insertion -> app

  (* Lambdas and Pis both bind a variable, along with its dependencies.  These are recorded as defunctionalized closures.  Since they are produced by higher-dimensional substitutions and operator actions, the dimension of the binder can be different than the dimension of the environment that closes its body.  Accordingly, in addition to the environment and degeneracy to close its body, we store information about how to map the eventual arguments into the bound variables in the body.  *)
  and (_, _) binder =
    | Bind : {
        env : ('m, 'a) env;
        body : (('a, 'n) snoc, 's) term;
        ins : ('mn, 'm, 'n) insertion;
      }
        -> ('mn, 's) binder

  (* A neutral has an "alignment".
     - A True neutral is an ordinary neutral that will never reduce further, such as an application of a variable or axiom, or of a defined constant with a neutral argument in a matching position.
     - A Chaotic neutral has a head defined by a case tree but isn't fully applied, so it might reduce further if it is applied to further arguments or field projections.  Thus it stores a value that should be either an abstraction or a struct, but does not test as equal to that value.
     - A Lawful neutral has a head defined by a case tree that will doesn't reduce, but if it is applied to enough arguments it obtains a specified behavior as a canonical type (datatype, record type, codatatype, function-type, etc.).
     Alignments are parametrized over the class of head for a neutral that can have such an alignment.  Only constant-headed neutrals can have chaotic or lawful alignments; variables are always true neutral.  This is because alignments are ignored by readback, and so the information they contain must be reconstructible from the read-back term, which is possible for the case tree that is stored with a constant in the global environment, but not for a variable. *)
  and _ alignment =
    | True : 'h alignment
    | Chaotic : potential value -> const alignment
    | Lawful : canonical -> const alignment

  (* An (m+n)-dimensional type is "instantiated" by applying it a "boundary tube" to get an m-dimensional type.  This operation is supposed to be functorial in dimensions, so in the normal forms we prevent it from being applied more than once in a row.  We have a separate class of "uninstantiated" values, and then every actual value is instantiated exactly once.  This means that even non-type neutrals must be "instantiated", albeit trivially. *)
  and uninst =
    | UU : 'n D.t -> uninst
    (* Pis must store not just the domain type but all its boundary types.  These domain and boundary types are not fully instantiated.  Note the codomains are stored in a cube of binders. *)
    | Pi : string option * ('k, kinetic value) CubeOf.t * ('k, unit) BindCube.t -> uninst
    (* A neutral is an application spine: a head with a list of applications.  Note that when we inject it into 'value' with Uninst below, it also stores its type (as do all the other uninsts).  It also has an alignment, which must be an allowed alignment for its class of head. *)
    | Neu : { head : 'h head; args : app Bwd.t; alignment : 'h alignment } -> uninst

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
        (* The types of the arguments remaining to be supplied.  In other words, the type *of* this instantiation is "Inst (UU k, tys)". *)
        tys : (D.zero, 'n, 'n, kinetic value) TubeOf.t;
      }
        -> kinetic value
    (* A constructor has a name, a dimension, and a list of arguments of that dimension.  It must always be applied to the correct number of arguments (otherwise it can be eta-expanded).  It doesn't have an outer insertion because a primitive datatype is always 0-dimensional (it has higher-dimensional versions, but degeneracies can always be pushed inside these).  *)
    | Constr : Constr.t * 'n D.t * ('n, kinetic value) CubeOf.t Bwd.t -> kinetic value
    (* Lambda-abstractions are never types, so they can never be nontrivially instantiated.  Thus we may as well make them values directly. *)
    | Lam : 'k variables * ('k, 's) binder -> 's value
    (* The same is true for anonymous structs.  These have to store an insertion outside, like an application.  We also remember which fields are labeled, for readback purposes.  We store the value of each field lazily, so that corecursive definitions don't try to compute an entire infinite structure.  And since in the non-kinetic case, evaluation can produce more data than just a term (e.g. whether a case tree has yet reached a leaf), what we store lazily is the result of evaluation. *)
    | Struct :
        (Field.t, 's evaluation Lazy.t * [ `Labeled | `Unlabeled ]) Abwd.t * ('m, 'n, 'k) insertion
        -> 's value
    | Lazy : 's value Lazy.t -> 's value

  (* This is the result of evaluating a term with a given kind of energy.  Evaluating a kinetic term just produces a (kinetic) value, whereas evaluating a potential term might be a potential value (waiting for more arguments), or else the information that the case tree has reached a leaf and the resulting kinetic value or canonical type, or else the information that the case tree is permanently stuck.  *)
  and _ evaluation =
    (* When 's = potential, a Val means the case tree is not yet fully applied; while when 's = kinetic, it is the only possible kind of result.  Collapsing these two together seems to unify the code for Lam and Struct as much as possible. *)
    | Val : 's value -> 's evaluation
    | Realize : kinetic value -> potential evaluation
    | Unrealized : potential evaluation
    | Canonical : canonical -> potential evaluation

  (* A canonical type value is either a datatype or a codatatype/record. *)
  and canonical =
    (* A datatype value has a Bwv of some indices to which it has been applied, the number of remaining indices to which it must be applied, and a family of constructors.  Each constructor stores the telescope of types of its arguments, as a closure, and the index values as function values taking its arguments. *)
    | Data : {
        dim : 'm D.t;
        indices : (('m, normal) CubeOf.t, 'i) Bwv.t;
        missing : ('i, 'j, 'ij) N.plus;
        constrs : ('m, 'ij) dataconstr Constr.Map.t;
      }
        -> canonical
    (* A codatatype value has an eta flag, an environment that it was evaluated at, an insertion that relates its intrinsic dimension (such as for Gel) to the dimension it was evaluated at, and its fields as unevaluted terms that depend on one additional variable belonging to the codatatype itself (usually through its previous fields).  Note that combining env, ins, and any of the field terms produces the data of a binder, so we can think of this as a family of binders,  one for each field, that share the same environment and insertion. *)
    | Codata : {
        eta : potential eta;
        env : ('m, 'a) env;
        ins : ('mn, 'm, 'n) insertion;
        (* TODO: When it's used, this should really be a forwards list.  But it's naturally constructed backwards, and it has to be used *as* it's being constructed when typechecking the later terms. *)
        fields : (Field.t, (('a, 'n) snoc, kinetic) term) Abwd.t;
      }
        -> canonical

  and (_, _) dataconstr =
    | Dataconstr : {
        env : ('m, 'a) env;
        args : ('a, 'p, 'ap) Telescope.t;
        indices : (('ap, kinetic) term, 'ij) Bwv.t;
      }
        -> ('m, 'ij) dataconstr

  (* A "normal form" is a value paired with its type.  The type is used for eta-expansion and equality-checking. *)
  and normal = { tm : kinetic value; ty : kinetic value }

  (* An "environment" is a context morphism *from* a De Bruijn LEVEL context *to* a (typechecked) De Bruijn INDEX context.  Specifically, an ('n, 'a) env is an 'n-dimensional substitution from a level context to an index context indexed by the hctx 'a.  Since the index context could have some variables that are labeled by integers together with faces, the values also have to allow that. *)
  and (_, _) env =
    | Emp : 'n D.t -> ('n, emp) env
    (* Here the k-cube denotes a "cube variable" consisting of some number of "real" variables indexed by the faces of a k-cube, while each of them has an n-cube of values representing a value and its boundaries. *)
    | Ext : ('n, 'b) env * ('k, ('n, kinetic value) CubeOf.t) CubeOf.t -> ('n, ('b, 'k) snoc) env
    | Act : ('n, 'b) env * ('m, 'n) op -> ('m, 'b) env
end

open Value

(* Given a De Bruijn level and a type, build the variable of that level having that type. *)
let var : level -> kinetic value -> kinetic value =
 fun level ty ->
  Uninst
    ( Neu { head = Var { level; deg = id_deg D.zero }; args = Emp; alignment = True },
      Lazy.from_val ty )

(* Every context morphism has a valid dimension. *)
let rec dim_env : type n b. (n, b) env -> n D.t = function
  | Emp n -> n
  | Ext (e, _) -> dim_env e
  | Act (_, op) -> dom_op op

(* And likewise every binder *)
let dim_binder : type m s. (m, s) binder -> m D.t = function
  | Bind b -> dom_ins b.ins

(* Project out a cube or tube of values from a cube or tube of normals *)
let val_of_norm_cube : type n. (n, normal) CubeOf.t -> (n, kinetic value) CubeOf.t =
 fun arg -> CubeOf.mmap { map = (fun _ [ { tm; ty = _ } ] -> tm) } [ arg ]

let val_of_norm_tube :
    type n k nk. (n, k, nk, normal) TubeOf.t -> (n, k, nk, kinetic value) TubeOf.t =
 fun arg -> TubeOf.mmap { map = (fun _ [ { tm; ty = _ } ] -> tm) } [ arg ]

(* Ensure that a (backwards) list of arguments consists of function applications at a fixed dimension with only identity insertions, and return them.  This is generally used for the arguments of a canonical type.  Takes an optional error code to report instead of an anomaly if the outer insertion is nonidentity, as this can be a user error (e.g. trying to check a tuple at a degenerated Gel-type).  *)
let rec args_of_apps : type n. ?degerr:Code.t -> n D.t -> app Bwd.t -> (n, normal) CubeOf.t Bwd.t =
 fun ?(degerr = Anomaly "unexpected degeneracy in argument spine") n xs ->
  match xs with
  | Emp -> Emp
  | Snoc (xs, App (Arg arg, ins)) ->
      if Option.is_some (is_id_ins ins) then
        match compare (CubeOf.dim arg) n with
        (* We DON'T pass on ?degerr to the recursive call, since any insertions deeper in the application spine are bugs. *)
        | Eq -> Snoc (args_of_apps n xs, arg)
        | Neq -> fatal (Dimension_mismatch ("args_of_apps", CubeOf.dim arg, n))
      else fatal degerr
  | _ -> fatal (Anomaly "unexpected field projection in argument spine")
