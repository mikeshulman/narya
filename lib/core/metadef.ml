(* This module should not be opened, but used qualified. *)

open Util
open Syntax
open Term

type ('b, 's) t =
  | Metadef : {
      energy : 's energy;
      (* We store the parsing vars here because we haven't parametrized metas over their raw context length, so here is the only place we can ensure statically that the vars have the same raw length as the context.  Of course, if the meta has a value, then we don't use the vars any more. *)
      tm : [ `Defined of ('b, 's) term | `Axiom | `Undefined of (string option, 'a) Bwv.t ];
      (* If a metavariable were "lifted" to top level with pi-types, then its type would be composed of its context and the type in that context.  We instead store them separately without doing the lifting. *)
      termctx : ('a, 'b) Termctx.t;
      ty : ('b, kinetic) term;
    }
      -> ('b, 's) t

(* Define or redefine a metavariable. *)
let define : type b s. (b, s) term -> (b, s) t -> (b, s) t =
 fun tm m ->
  match m with
  | Metadef { tm = _; termctx; ty; energy } -> Metadef { tm = `Defined tm; termctx; ty; energy }
