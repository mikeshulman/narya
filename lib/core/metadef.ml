(* This module should not be opened, but used qualified. *)

open Term

type ('a, 'b, 's) t = {
  energy : 's energy;
  tm : [ `Defined of ('b, 's) term | `Axiom | `Undefined ];
  (* If a metavariable were "lifted" to top level with pi-types, then its type would be the pi-type over its context of the type in that context.  We instead store them separately without doing the lifting. *)
  termctx : ('a, 'b) Termctx.t;
  ty : ('b, kinetic) term;
}

let make ~energy ~tm ~termctx ~ty = { energy; tm; termctx; ty }

(* Define or redefine a metavariable. *)
let define : type a b s. (b, s) term -> (a, b, s) t -> (a, b, s) t =
 fun tm m ->
  match m with
  | { tm = _; termctx; ty; energy } -> { tm = `Defined tm; termctx; ty; energy }
