open Util
open Dim
include Energy

type 'a located = 'a Asai.Range.located

(* ******************** Raw (unchecked) terms ******************** *)

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
  | UU : 'a synth
  (* A Let can either synthesize or (sometimes) check.  It synthesizes only if its body also synthesizes, but we wait until typechecking type to look for that, so that if it occurs in a checking context the body can also be checking.  Thus, we make it a "synthesizing term".  The term being bound must also synthesize; the shorthand notation "let x : A := M" is expanded during parsing to "let x := M : A". *)
  | Let : string option * 'a synth located * 'a N.suc check located -> 'a synth
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

and _ check =
  | Synth : 'a synth -> 'a check
  | Lam : string option located * [ `Cube | `Normal ] * 'a N.suc check located -> 'a check
  (* A "Struct" is our current name for both tuples and comatches, which share a lot of their implementation even though they are conceptually and syntactically distinct.  Those with eta=`Eta are tuples, those with eta=`Noeta are comatches.  We index them by a "Field.t option" so as to include any unlabeled fields, with their relative order to the labeled ones. *)
  | Struct : 's eta * (Field.t option, 'a check located) Abwd.t -> 'a check
  | Constr : Constr.t located * 'a check located list -> 'a check
  (* "[]", which could be either an empty pattern-matching lambda or an empty comatch *)
  | Empty_co_match : 'a check
  | Data : (Constr.t, 'a dataconstr located) Abwd.t -> 'a check
  (* A codatatype binds one more "self" variable in the types of each of its fields.  For a higher-dimensional codatatype (like a codata version of Gel), this becomes a cube of variables. *)
  | Codata : (Field.t, string option * 'a N.suc check located) Abwd.t -> 'a check
  (* A record type binds its "self" variable namelessly, exposing it to the user by additional variables that are bound locally to its fields.  This can't be "cubeified" as easily, so we have the user specify a list of ordinary variables to be its boundary.  Thus, in practice below 'c must be a number of faces associated to a dimension, but the parser doesn't know the dimension, so it can't ensure that.  The unnamed internal variable is included as the last one. *)
  | Record :
      ('a, 'c, 'ac) Fwn.bplus located * (string option, 'c) Vec.t * ('ac, 'd, 'acd) tel * opacity
      -> 'a check
  (* Empty match against the first one of the arguments belonging to an empty type. *)
  | Refute : 'a synth located list * [ `Explicit | `Implicit ] -> 'a check
  (* A hole must store the entire "state" from when it was entered, so that the user can later go back and fill it with a term that would have been valid in its original position.  This includes the variables in lexical scope, which are available only during parsing, so we store them here at that point.  During typechecking, when the actual metavariable is created, we save the lexical scope along with its other context and type data.  A hole also stores its source location so that proofgeneral can create an overlay at that place. *)
  | Hole : (string option, 'a) Bwv.t * unit located -> 'a check
  | Fail : Reporter.Code.t -> 'a check

and _ branch =
  (* The location of the third argument is that of the entire pattern. *)
  | Branch :
      (string option, 'b) Vec.t * ('a, 'b, 'ab) Fwn.bplus located * 'ab check located
      -> 'a branch

and _ dataconstr = Dataconstr : ('a, 'b, 'ab) tel * 'ab check located option -> 'a dataconstr

(* A raw match stores the information about the pattern variables available from previous matches that could be used to refute missing cases.  But it can't store them as raw terms, since they have to be in the correct context extended by the new pattern variables generated in any such case.  So it stores them as a callback that puts them in any such extended context. *)
and 'a refutables = { refutables : 'b 'ab. ('a, 'b, 'ab) Fwn.bplus -> 'ab synth located list }

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
