open Util
open Dim
include Energy

type 'a located = 'a Asai.Range.located

let locate_opt = Asai.Range.locate_opt
let locate_map f ({ value; loc } : 'a located) = locate_opt loc (f value)

(* Raw (unchecked) terms, using intrinsically well-scoped De Bruijn indices, and separated into synthesizing terms and checking terms.  These match the user-facing syntax rather than the internal syntax.  In particular, applications, abstractions, and pi-types are all unary, there is only one universe, and the only operator actions are refl (including Id) and sym. *)

(* In general, we parametrize the type of raw terms over a notion of "index", along with successors and addition.  Narya proper only uses ordinary type-level natural numbers here, but other frontends may want a notion of raw term that uses explicit names or something else.  *)
module type Indices = sig
  type name
  type 'a index
  type 'a suc
  type ('a, 'b, 'ab) bplus
end

module Make (I : Indices) = struct
  (* A raw De Bruijn index is a well-scoped natural number together with a possible face.  During typechecking we will verify that the face, if given, is applicable to the variable as a "cube variable", and compile the combination into a more strongly well-scoped kind of index. *)
  type 'a index = 'a I.index * any_sface option

  type _ synth =
    | Var : 'a index -> 'a synth
    | Const : Constant.t -> 'a synth
    | Field : 'a synth located * Field.or_index -> 'a synth
    | Pi : I.name * 'a check located * 'a I.suc check located -> 'a synth
    | App : 'a synth located * 'a check located -> 'a synth
    | Asc : 'a check located * 'a check located -> 'a synth
    | UU : 'a synth
    (* A Let can either synthesize or (sometimes) check.  It synthesizes only if its body also synthesizes, but we wait until typechecking type to look for that, so that if it occurs in a checking context the body can also be checking.  Thus, we make it a "synthesizing term".  The term being bound must also synthesize; the shorthand notation "let x : A := M" is expanded during parsing to "let x := M : A". *)
    | Let : I.name * 'a synth located * 'a I.suc check located -> 'a synth
    (* Letrec has a telescope of types, so that each can depend on the previous ones, and an equal-length vector of bound terms, all in the context extended by all the variables being bound, plus a body that is also in that context. *)
    | Letrec : ('a, 'b, 'ab) tel * ('ab check located, 'b) Vec.t * 'ab check located -> 'a synth
    (* An Act can also sometimes check, if its body checks and the degeneracy is a pure permutation.  But otherwise, it synthesizes and so must its body.  *)
    | Act : string * ('m, 'n) deg * 'a check located -> 'a synth
    (* A Match can also sometimes check, but synthesizes if it has an explicit return type or if it is nondependent and its first branch synthesizes. *)
    | Match : {
        tm : 'a synth located;
        (* Implicit means no "return" statement was given, so Narya has to guess what to do.  Explicit means a "return" statement was given with a motive.  "Nondep" means a placeholder return statement like "_ ↦ _" was given, indicating that a non-dependent matching is intended (to silence hints about fallback from the implicit case). *)
        sort : [ `Implicit | `Explicit of 'a check located | `Nondep of int located ];
        branches : (Constr.t, 'a branch) Abwd.t;
        refutables : 'a refutables;
      }
        -> 'a synth
    | Fail : Reporter.Code.t -> 'a synth

  and _ check =
    | Synth : 'a synth -> 'a check
    | Lam : I.name located * [ `Cube | `Normal ] * 'a I.suc check located -> 'a check
    (* A "Struct" is our current name for both tuples and comatches, which share a lot of their implementation even though they are conceptually and syntactically distinct.  Those with eta=`Eta are tuples, those with eta=`Noeta are comatches.  We index them by a "Field.t option" so as to include any unlabeled fields, with their relative order to the labeled ones. *)
    | Struct : 's eta * (Field.t option, 'a check located) Abwd.t -> 'a check
    | Constr : Constr.t located * 'a check located list -> 'a check
    (* "[]", which could be either an empty pattern-matching lambda or an empty comatch *)
    | Empty_co_match : 'a check
    | Data : (Constr.t, 'a dataconstr located) Abwd.t -> 'a check
    (* A codatatype binds one more "self" variable in the types of each of its fields.  For a higher-dimensional codatatype (like a codata version of Gel), this becomes a cube of variables. *)
    | Codata : (Field.t, I.name * 'a I.suc check located) Abwd.t -> 'a check
    (* A record type binds its "self" variable namelessly, exposing it to the user by additional variables that are bound locally to its fields.  This can't be "cubeified" as easily, so we have the user specify a list of ordinary variables to be its boundary.  Thus, in practice below 'c must be a number of faces associated to a dimension, but the parser doesn't know the dimension, so it can't ensure that.  The unnamed internal variable is included as the last one. *)
    | Record :
        ('a, 'c, 'ac) I.bplus located * (I.name, 'c) Vec.t * ('ac, 'd, 'acd) tel * opacity
        -> 'a check
    (* Empty match against the first one of the arguments belonging to an empty type. *)
    | Refute : 'a synth located list * [ `Explicit | `Implicit ] -> 'a check
    (* A hole must store the entire "state" from when it was entered, so that the user can later go back and fill it with a term that would have been valid in its original position.  This includes the variables in lexical scope, which are available only during parsing, so we store them here at that point.  During typechecking, when the actual metavariable is created, we save the lexical scope along with its other context and type data.  A hole also stores its source location so that proofgeneral can create an overlay at that place. *)
    | Hole : (I.name, 'a) Bwv.t * unit located -> 'a check
    (* Force a leaf of the case tree *)
    | Realize : 'a check -> 'a check

  and _ branch =
    (* The location of the third argument is that of the entire pattern. *)
    | Branch : (I.name, 'b) Vec.t * ('a, 'b, 'ab) I.bplus located * 'ab check located -> 'a branch

  and _ dataconstr = Dataconstr : ('a, 'b, 'ab) tel * 'ab check located option -> 'a dataconstr

  (* A raw match stores the information about the pattern variables available from previous matches that could be used to refute missing cases.  But it can't store them as raw terms, since they have to be in the correct context extended by the new pattern variables generated in any such case.  So it stores them as a callback that puts them in any such extended context. *)
  and 'a refutables = { refutables : 'b 'ab. ('a, 'b, 'ab) I.bplus -> 'ab synth located list }

  (* An ('a, 'b, 'ab) tel is a raw telescope of length 'b in context 'a, with 'ab = 'a+'b the extended context. *)
  and (_, _, _) tel =
    | Emp : ('a, Fwn.zero, 'a) tel
    | Ext : I.name * 'a check located * ('a I.suc, 'b, 'ab) tel -> ('a, 'b Fwn.suc, 'ab) tel

  let rec fwn_of_tel : type a b c. (a, b, c) tel -> b Fwn.t = function
    | Emp -> Zero
    | Ext (_, _, tel) -> Suc (fwn_of_tel tel)
end

(* This is the standard instantiation that uses type-level nats as De Bruijn indices. *)
include Make (struct
  type name = string option
  type 'a index = 'a N.index
  type 'a suc = 'a N.suc
  type ('a, 'b, 'ab) bplus = ('a, 'b, 'ab) Fwn.bplus
end)

(* We supply a generic name-resolution module that turns explicit names into De Bruijn indices, threading through a scope of bound variables.  For this to work, the type of names needs a bit of extra structure. *)
module type NamesType = sig
  type t
  type scope_t

  val equals : t -> scope_t -> bool
  val none : scope_t
  val to_string_opt : scope_t -> string option
  val scope_error : t -> Reporter.Code.t
  val visit_scope : Asai.Range.t option -> (scope_t, 'a) Bwv.t -> unit
end

(* This is an implementation instead using explicit names that belong to some arbitrary type.  Here the type parameters carry no information. *)
module NameIndices (Names : NamesType) = struct
  type name = Names.scope_t
  type 'a index = Names.t
  type 'a suc = 'a
  type ('a, 'b, 'ab) bplus = unit
end

(* Here's the name-resolution module.  This is basically a straightforward structural induction that walks the terms, extending the scope as it goes. *)
module Resolve (Names : NamesType) = struct
  module Indices = NameIndices (Names)
  module T = Make (Indices)

  let rec synth : type a x. (Names.scope_t, a) Bwv.t -> x T.synth located -> a synth located =
   fun ctx tm ->
    Names.visit_scope tm.loc ctx;
    locate_opt tm.loc
      (match tm.value with
      | Var (name, fa) -> (
          (* Here's the interesting resolution bit: we look up names in the scope, and insert an error in case of failure.  Note that we store the error in the term rather than raising it immediately; a caller who wants to raise it immediately can do that in the function 'scope_error' instead of returning it. *)
          match Bwv.find_opt (fun x -> Names.equals name x) ctx with
          | Some (_, ix) -> Var (ix, fa)
          | None -> Fail (Names.scope_error name))
      | Const c -> Const c
      | Field (tm, fld) -> Field (synth ctx tm, fld)
      | Pi (x, dom, cod) -> Pi (Names.to_string_opt x, check ctx dom, check (Snoc (ctx, x)) cod)
      | App (fn, arg) -> App (synth ctx fn, check ctx arg)
      | Asc (tm, ty) -> Asc (check ctx tm, check ctx ty)
      | UU -> UU
      | Let (x, tm, body) -> Let (Names.to_string_opt x, synth ctx tm, (check (Snoc (ctx, x))) body)
      | Letrec (tys, tms, body) ->
          let (Bplus ab) = Fwn.bplus (Vec.length tms) in
          let tys2, ctx2 = tel ctx ab tys in
          let tms2 = Vec.map (check ctx2) tms in
          Letrec (tys2, tms2, check ctx2 body)
      | Act (s, fa, tm) -> Act (s, fa, check ctx tm)
      | Match { tm; sort; branches; refutables = r } ->
          let tm = synth ctx tm in
          let sort =
            match sort with
            | `Explicit ty -> `Explicit (check ctx ty)
            | `Nondep i -> `Nondep i
            | `Implicit -> `Implicit in
          let branches = Abwd.map (branch ctx) branches in
          let refutables = refutables ctx r in
          Match { tm; sort; branches; refutables }
      | Fail e -> Fail e)

  and check : type a x. (Names.scope_t, a) Bwv.t -> x T.check located -> a check located =
   fun ctx tm ->
    Names.visit_scope tm.loc ctx;
    locate_opt tm.loc
      (match tm.value with
      | Synth x -> Synth (synth ctx (locate_opt tm.loc x)).value
      | Lam (x, sort, body) ->
          Lam (locate_map Names.to_string_opt x, sort, check (Snoc (ctx, x.value)) body)
      | Struct (eta, fields) -> Struct (eta, Abwd.map (check ctx) fields)
      | Constr (c, args) -> Constr (c, List.map (check ctx) args)
      | Empty_co_match -> Empty_co_match
      | Data constrs -> Data (Abwd.map (locate_map (dataconstr ctx)) constrs)
      | Codata fields ->
          Codata
            (Abwd.map (fun (x, fld) -> (Names.to_string_opt x, check (Snoc (ctx, x)) fld)) fields)
      | Record (ac, xs, fields, opaq) ->
          let (Bplus ac2) = Fwn.bplus (Vec.length xs) in
          let xs2 = Vec.map Names.to_string_opt xs in
          let ctx2 = Bwv.append ac2 ctx xs in
          let (Bplus ad) = Fwn.bplus (T.fwn_of_tel fields) in
          let fields2, _ = tel ctx2 ad fields in
          Record (locate_opt ac.loc ac2, xs2, fields2, opaq)
      | Refute (args, sort) -> Refute (List.map (synth ctx) args, sort)
      | Hole (_, loc) ->
          (* We ignore the provided scope, as it (and in particular its length) is meaningless, and store instead the scope currently being used for resolution. *)
          Hole (Bwv.map Names.to_string_opt ctx, loc)
      | Realize x -> Realize (check ctx (locate_opt tm.loc x)).value)

  and branch : type a x. (Names.scope_t, a) Bwv.t -> x T.branch -> a branch =
   fun ctx (Branch (xs, _, body)) ->
    let (Bplus ab) = Fwn.bplus (Vec.length xs) in
    let xs2 = Vec.map Names.to_string_opt xs in
    let ctx2 = Bwv.append ab ctx xs in
    Branch (xs2, locate_opt None ab, check ctx2 body)

  and dataconstr : type a x. (Names.scope_t, a) Bwv.t -> x T.dataconstr -> a dataconstr =
   fun ctx (Dataconstr (args, body)) ->
    let (Bplus ab) = Fwn.bplus (T.fwn_of_tel args) in
    let args2, ctx2 = tel ctx ab args in
    Dataconstr (args2, Option.map (check ctx2) body)

  and refutables : type a x. (Names.scope_t, a) Bwv.t -> x T.refutables -> a refutables =
   fun ctx { refutables } ->
    let refutables ab =
      let ctx2 = Bwv.append ab ctx (Vec.init (fun () -> (Names.none, ())) (Fwn.bplus_right ab) ()) in
      List.map (synth ctx2) (refutables ()) in
    { refutables = (fun ab -> refutables ab) }

  and tel :
      type a x b ab y.
      (Names.scope_t, a) Bwv.t ->
      (a, b, ab) Fwn.bplus ->
      (x, b, y) T.tel ->
      (a, b, ab) tel * (Names.scope_t, ab) Bwv.t =
   fun ctx ab tele ->
    match (ab, tele) with
    | Zero, Emp -> (Emp, ctx)
    | Suc ab, Ext (x, ty, rest) ->
        let ctx2 = Bwv.Snoc (ctx, x) in
        let rest3, ctx3 = tel ctx2 ab rest in
        (Ext (Names.to_string_opt x, check ctx ty, rest3), ctx3)
end

(* We end with some useful lemmas. *)

let rec dataconstr_of_pi : type a. a check located -> a dataconstr =
 fun ty ->
  match ty.value with
  | Synth (Pi (x, dom, cod)) ->
      let (Dataconstr (tel, out)) = dataconstr_of_pi cod in
      Dataconstr (Ext (x, dom, tel), out)
  | _ -> Dataconstr (Emp, Some ty)

let rec lams :
    type a b ab.
    (a, b, ab) Fwn.bplus ->
    (string option located, b) Vec.t ->
    ab check located ->
    Asai.Range.t option ->
    a check located =
 fun ab xs tm loc ->
  match (ab, xs) with
  | Zero, [] -> tm
  | Suc ab, x :: xs -> { value = Lam (x, `Normal, lams ab xs tm loc); loc }

let rec bplus_of_tel : type a b c. (a, b, c) tel -> (a, b, c) Fwn.bplus = function
  | Emp -> Zero
  | Ext (_, _, tel) -> Suc (bplus_of_tel tel)
