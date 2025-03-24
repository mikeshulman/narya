open Bwd
open Util
open Tbwd
open Dim
open Dimbwd
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

  module PlusFam : sig
    type (_, _) t =
      | PlusFam : (('r, 'b, 'rb) Plusmap.t * ('rb, potential) Term.term) option -> ('r, 'b) t
  end

  module PlusPbijmap : module type of Pbijmap (PlusFam)

  module Codatafield : sig
    type (_, _) t =
      | Lower : (('a, 'n) snoc, kinetic) Term.term -> (D.zero, 'a * 'n * 'et) t
      | Higher :
          ('i, ('a, D.zero) snoc, 'ian) Plusmap.t * ('ian, kinetic) Term.term
          -> ('i, 'a * D.zero * no_eta) t
  end

  module CodatafieldAbwd : module type of Field.Abwd (Codatafield)

  module Structfield : sig
    type (_, _) t =
      | Lower : ('a, 's) Term.term * [ `Labeled | `Unlabeled ] -> (D.zero, 'n * 'a * 's * 'et) t
      | Higher : ('n, 'i, 'a) PlusPbijmap.t -> ('i, 'n * 'a * potential * no_eta) t
  end

  module StructfieldAbwd : module type of Field.Abwd (Structfield)

  type _ index = Index : ('a, 'n, 'b) Tbwd.insert * ('k, 'n) sface -> 'b index

  type (_, _) term =
    | Var : 'a index -> ('a, kinetic) term
    | Const : Constant.t -> ('a, kinetic) term
    | Meta : ('x, 'b, 'l) Meta.t * 's energy -> ('b, 's) term
    | MetaEnv : ('x, 'b, 's) Meta.t * ('a, 'n, 'b) env -> ('a, kinetic) term
    | Field : ('a, kinetic) term * 'i Field.t * ('n, 't, 'i) insertion -> ('a, kinetic) term
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
        ('s, 'et) eta * 'n D.t * ('n * 'a * 's * 'et) StructfieldAbwd.t * 's energy
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
        eta : (potential, 'et) eta;
        opacity : opacity;
        dim : 'n D.t;
        termctx : ('c, ('a, 'n) snoc) termctx option;
        fields : ('a * 'n * 'et) CodatafieldAbwd.t;
      }
        -> 'a canonical

  and (_, _) dataconstr =
    | Dataconstr : {
        args : ('p, 'a, 'pa) tel;
        indices : (('pa, kinetic) term, 'i) Vec.t;
      }
        -> ('p, 'i) dataconstr

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

  and 'b binding = { ty : ('b, kinetic) term; tm : ('b, kinetic) term option }

  and (_, _) has_fields =
    | No_fields : ('m, N.zero) has_fields
    | Has_fields : (D.zero, 'f2) has_fields

  and (_, _, _) entry =
    | Vis : {
        dim : 'm D.t;
        plusdim : ('m, 'n, 'mn) D.plus;
        vars : (N.zero, 'n, string option, 'f1) NICubeOf.t;
        bindings : ('mn, ('b, 'mn) snoc binding) CubeOf.t;
        hasfields : ('m, 'f2) has_fields;
        fields : (D.zero Field.t * string * (('b, 'mn) snoc, kinetic) term, 'f2) Bwv.t;
        fplus : ('f1, 'f2, 'f) N.plus;
      }
        -> ('b, 'f, 'mn) entry
    | Invis : ('n, ('b, 'n) snoc binding) CubeOf.t -> ('b, N.zero, 'n) entry

  and (_, _) ordered_termctx =
    | Emp : (N.zero, emp) ordered_termctx
    | Ext :
        ('a, 'b) ordered_termctx * ('b, 'x, 'n) entry * ('a, 'x, 'ax) N.plus
        -> ('ax, ('b, 'n) snoc) ordered_termctx
    | Lock : ('a, 'b) ordered_termctx -> ('a, 'b) ordered_termctx

  and ('a, 'b) termctx = Permute : ('a, 'i) N.perm * ('i, 'b) ordered_termctx -> ('a, 'b) termctx
end = struct
  module CodFam = struct
    type ('k, 'a) t = (('a, 'k) snoc, kinetic) Term.term
  end

  module CodCube = Cube (CodFam)

  module PlusFam = struct
    type (_, _) t =
      | PlusFam : (('r, 'b, 'rb) Plusmap.t * ('rb, potential) Term.term) option -> ('r, 'b) t
  end

  module PlusPbijmap = Pbijmap (PlusFam)

  module Codatafield = struct
    (* A codatafield has an intrinsic dimension, and a type that depends on one additional variable, but in a degenerated context.  If it is zero-dimensional, the degeneration does nothing, but we store that case separately so we don't need to construct and carry around lots of trivial Plusmaps. *)
    type (_, _) t =
      | Lower : (('a, 'n) snoc, kinetic) Term.term -> (D.zero, 'a * 'n * 'et) t
      (* For the present, we don't allow Gel-like fields in higher-dimensional codatatypes, just for simplicity. *)
      | Higher :
          ('i, ('a, D.zero) snoc, 'ian) Plusmap.t * ('ian, kinetic) Term.term
          -> ('i, 'a * D.zero * no_eta) t
  end

  module CodatafieldAbwd = Field.Abwd (Codatafield)

  module Structfield = struct
    type (_, _) t =
      | Lower : ('a, 's) Term.term * [ `Labeled | `Unlabeled ] -> (D.zero, 'n * 'a * 's * 'et) t
      | Higher : ('n, 'i, 'a) PlusPbijmap.t -> ('i, 'n * 'a * potential * no_eta) t
  end

  module StructfieldAbwd = Field.Abwd (Structfield)

  (* A typechecked De Bruijn index is a well-scoped natural number together with a definite strict face (the top face, if none was supplied explicitly).  Unlike a raw De Bruijn index, the scoping is by a tbwd rather than a type-level nat.  This allows the face to also be well-scoped: its codomain must be the dimension appearing in the hctx at that position.  And since we already have defined Tbwd.insert, we can re-use that instead of re-defining this inductively. *)
  type _ index = Index : ('a, 'n, 'b) Tbwd.insert * ('k, 'n) sface -> 'b index

  type (_, _) term =
    (* Most term-formers only appear in kinetic (ordinary) terms. *)
    | Var : 'a index -> ('a, kinetic) term
    | Const : Constant.t -> ('a, kinetic) term
    | Meta : ('x, 'b, 'l) Meta.t * 's energy -> ('b, 's) term
    (* Normally, checked metavariables don't require an environment attached, but they do when they arise by readback from a value metavariable. *)
    | MetaEnv : ('x, 'b, 's) Meta.t * ('a, 'n, 'b) env -> ('a, kinetic) term
    | Field : ('a, kinetic) term * 'i Field.t * ('n, 't, 'i) insertion -> ('a, kinetic) term
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
        ('s, 'et) eta * 'n D.t * ('n * 'a * 's * 'et) StructfieldAbwd.t * 's energy
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
        eta : (potential, 'et) eta;
        opacity : opacity;
        dim : 'n D.t;
        termctx : ('c, ('a, 'n) snoc) termctx option;
        fields : ('a * 'n * 'et) CodatafieldAbwd.t;
      }
        -> 'a canonical

  (* A datatype constructor has a telescope of arguments and a list of index values depending on those arguments. *)
  and (_, _) dataconstr =
    | Dataconstr : {
        args : ('p, 'a, 'pa) tel;
        indices : (('pa, kinetic) term, 'i) Vec.t;
      }
        -> ('p, 'i) dataconstr

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

  (* A termctx is a data structure analogous to a Ctx.t, but using terms rather than values (and thus we will not explain its structure here; see ctx.ml).  This is used to store the context of a metavariable, as the value context containing level variables is too volatile to store there.  We also store it (lazily) with a codatatype that has higher fields, so we can use it to read back the closure environment to degenerate it. *)
  and 'b binding = { ty : ('b, kinetic) term; tm : ('b, kinetic) term option }

  and (_, _) has_fields =
    | No_fields : ('m, N.zero) has_fields
    | Has_fields : (D.zero, 'f2) has_fields

  and (_, _, _) entry =
    | Vis : {
        dim : 'm D.t;
        plusdim : ('m, 'n, 'mn) D.plus;
        vars : (N.zero, 'n, string option, 'f1) NICubeOf.t;
        (* The reason for the "snoc" here is so that some of the terms and types in these bindings can refer to other ones.  Of course it should really be only the *later* ones that can refer to the *earlier* ones, but we don't have a way to specify that in the type parameters. *)
        bindings : ('mn, ('b, 'mn) snoc binding) CubeOf.t;
        hasfields : ('m, 'f2) has_fields;
        fields : (D.zero Field.t * string * (('b, 'mn) snoc, kinetic) term, 'f2) Bwv.t;
        fplus : ('f1, 'f2, 'f) N.plus;
      }
        -> ('b, 'f, 'mn) entry
    | Invis : ('n, ('b, 'n) snoc binding) CubeOf.t -> ('b, N.zero, 'n) entry

  and (_, _) ordered_termctx =
    | Emp : (N.zero, emp) ordered_termctx
    | Ext :
        ('a, 'b) ordered_termctx * ('b, 'x, 'n) entry * ('a, 'x, 'ax) N.plus
        -> ('ax, ('b, 'n) snoc) ordered_termctx
    | Lock : ('a, 'b) ordered_termctx -> ('a, 'b) ordered_termctx

  and ('a, 'b) termctx = Permute : ('a, 'i) N.perm * ('i, 'b) ordered_termctx -> ('a, 'b) termctx
end

include Term

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

let dim_entry : type b f n. (b, f, n) entry -> n D.t = function
  | Vis { bindings; _ } | Invis bindings -> CubeOf.dim bindings

let rec ordered_dbwd : type a b. (a, b) ordered_termctx -> b Dbwd.t = function
  | Emp -> Word Zero
  | Ext (ctx, e, _) ->
      let (Word b) = ordered_dbwd ctx in
      Word (Suc (b, dim_entry e))
  | Lock ctx -> ordered_dbwd ctx

let dbwd (Permute (_, ctx)) = ordered_dbwd ctx

let ordered_ext_let : type a b.
    (a, b) ordered_termctx ->
    string option ->
    (b, D.zero) snoc binding ->
    (a N.suc, (b, D.zero) snoc) ordered_termctx =
 fun ctx x b ->
  Ext
    ( ctx,
      Vis
        {
          dim = D.zero;
          plusdim = D.plus_zero D.zero;
          vars = NICubeOf.singleton x;
          bindings = CubeOf.singleton b;
          hasfields = No_fields;
          fields = Emp;
          fplus = Zero;
        },
      Suc Zero )

let ext_let (Permute (p, ctx)) xs b =
  let ctx = ordered_ext_let ctx xs b in
  Permute (Insert (p, Top), ctx)

let ext (Permute (p, ctx)) xs ty =
  let ctx = ordered_ext_let ctx xs { ty; tm = None } in
  Permute (Insert (p, Top), ctx)
