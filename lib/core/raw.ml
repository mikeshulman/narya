open Bwd
open Util

(* Raw (unchecked) terms, using intrinsically well-scoped De Bruijn indices, and separated into synthesizing terms and checking terms.  These match the user-facing syntax rather than the internal syntax.  In particular, applications, abstractions, and pi-types are all unary, there is only one universe, and the only operator actions are Id, refl, and sym. *)

(* A "symbol" is something that acts like a function in concrete syntax, being applied to its arguments (or perhaps being the output of a notation).  However, unlike a function, it doesn't typecheck unless it's applied to the right number of arguments, and it can require some of its arguments to synthesize.  We parametrize a symbol by the number of arguments it requires.  *)
type _ symbol =
  | Refl : N.one symbol
  | Sym : N.one symbol
  | Id : N.three symbol
  | UU : N.zero symbol

type _ synth =
  | Var : 'a N.index -> 'a synth
  | Const : Constant.t -> 'a synth
  | Field : 'a synth * Field.t -> 'a synth
  | Pi : 'a check * 'a N.suc check -> 'a synth
  | App : 'a synth * 'a check -> 'a synth
  (* In raw syntax, we allow a symbol to be applied to fewer than the correct number of arguments.  This is so that they can be parsed as function applications, with arguments added on one by one as they are parsed.  *)
  | Symbol : 'mn symbol * ('m, 'n, 'mn) N.plus * ('a check, 'm) Bwv.t -> 'a synth
  | Asc : 'a check * 'a check -> 'a synth
  | Let : 'a synth * 'a N.suc synth -> 'a synth

and _ check =
  | Synth : 'a synth -> 'a check
  | Lam : 'a N.suc check -> 'a check
  | Struct : 'a check Field.Map.t -> 'a check
  | Constr : Constr.t * 'a check Bwd.t -> 'a check

let rec raw_lam : type a b ab. (a, b, ab) N.plus -> ab check -> a check =
 fun ab tm ->
  match ab with
  | Zero -> tm
  | Suc ab -> raw_lam ab (Lam tm)
