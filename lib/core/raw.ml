open Bwd
open Util
open Dim

(* Raw (unchecked) terms, using intrinsically well-scoped De Bruijn indices, and separated into synthesizing terms and checking terms.  These match the user-facing syntax rather than the internal syntax.  In particular, applications, abstractions, and pi-types are all unary, there is only one universe, and the only operator actions are refl (including Id) and sym. *)

(* A raw De Bruijn index is a well-scoped natural number together with a possible face.  During typechecking we will verify that the face, if given, is applicable to the variable as a "cube variable", and compile the combination into a more strongly well-scoped kind of index. *)
type 'a index = 'a N.index * any_sface option

type _ synth =
  | Var : 'a index -> 'a synth
  | Const : Constant.t -> 'a synth
  | Field : 'a synth * Field.t -> 'a synth
  | Pi : string option * 'a check * 'a N.suc check -> 'a synth
  | App : 'a synth * 'a check -> 'a synth
  | Asc : 'a check * 'a check -> 'a synth
  | Let : string option * 'a synth * 'a N.suc synth -> 'a synth
  | UU : 'a synth
  | Act : string * ('m, 'n) deg * 'a synth -> 'a synth

and _ check =
  | Synth : 'a synth -> 'a check
  | Lam : string option * [ `Cube | `Normal ] * 'a N.suc check -> 'a check
  | Struct : 'a check Field.Map.t -> 'a check
  | Constr : Constr.t * 'a check Bwd.t -> 'a check
  | Match : 'a index * 'a branch list -> 'a check

and _ branch = Branch : Constr.t * ('a, 'b, 'ab) N.plus * 'ab check -> 'a branch

let rec raw_lam :
    type a b ab.
    (string option, ab) Bwv.t -> [ `Cube | `Normal ] -> (a, b, ab) N.plus -> ab check -> a check =
 fun names cube ab tm ->
  match (names, ab) with
  | _, Zero -> tm
  | Snoc (names, x), Suc ab -> raw_lam names cube ab (Lam (x, cube, tm))
