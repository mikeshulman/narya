(* Raw (unchecked) terms, using intrinsically well-scoped De Bruijn indices, and separated into synthesizing terms and checking terms.  These match the user-facing syntax rather than the internal syntax.  In particular, applications, abstractions, and pi-types are all unary, there is only one universe, and the only operator actions are Id, refl, and sym. *)

type _ synth =
  | Var : 'a N.index -> 'a synth
  | Const : Constant.t -> 'a synth
  | UU : 'a synth
  | Pi : 'a check * 'a N.suc check -> 'a synth
  | App : 'a synth * 'a check -> 'a synth
  | Id : 'a synth * 'a check * 'a check -> 'a synth
  | Refl : 'a synth -> 'a synth
  | Sym : 'a synth -> 'a synth
  | Asc : 'a check * 'a check -> 'a synth

and _ check = Synth : 'a synth -> 'a check | Lam : 'a N.suc check -> 'a check
