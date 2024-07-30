(* This module should not be opened, but used qualified. *)

open Util
open Syntax
open Term
open Status

type def = Dummy_def
type undef = Dummy_undef

type (_, _, _, _) data =
  | Undef_meta : {
      vars : (string option, 'a) Bwv.t;
      status : ('b, 's) status;
    }
      -> (undef, 'a, 'b, 's) data
  | Def_meta : ('b, 's) term option -> ('d, 'a, 'b, 's) data

type (_, _) t =
  | Metadef : {
      data : ('d, 'a, 'b, 's) data;
      (* If a metavariable were "lifted" to top level with pi-types, then its type would be composed of its context and the type in that context.  We instead store them separately without doing the lifting. *)
      termctx : ('a, 'b) Termctx.t;
      ty : ('b, kinetic) term;
      energy : 's energy;
    }
      (* This weird-looking parametrization is to match the implementation of Meta.Map. *)
      -> ('d, 'b * 's) t

(* Define or redefine a metavariable. *)
let define : type d b s. (b, s) term option -> (d, b * s) t -> (d, b * s) t =
 fun tm m ->
  match m with
  | Metadef { data = Undef_meta _; termctx; ty; energy } ->
      Metadef { data = Def_meta tm; termctx; ty; energy }
  | Metadef { data = Def_meta _; termctx; ty; energy } ->
      Metadef { data = Def_meta tm; termctx; ty; energy }

type (_, _) wrapped = Wrap : ('d, 'b * 's) t -> ('b, 's) wrapped
