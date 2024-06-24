(* This module should not be opened, but used qualified. *)

open Util
open Syntax
open Term
open Status
open Reporter

type def = Dummy_def
type undef = Dummy_undef

type (_, _, _, _) data =
  | Undef_meta : {
      vars : (string option, 'a) Bwv.t;
      status : ('b, 's) status;
    }
      -> (undef, 'a, 'b, 's) data
  | Def_meta : { tm : ('b, 's) term; energy : 's energy } -> ('d, 'a, 'b, 's) data

type (_, _) t =
  | Metadef : {
      data : ('d, 'a, 'b, 's) data;
      termctx : ('a, 'b) Termctx.t;
      ty : ('b, kinetic) term;
    }
      (* This weird-looking parametrization is to match the implementation of Meta.Map. *)
      -> ('d, 'b * 's) t

let define : type d b s. (b, s) term -> (d, b * s) t -> (d, b * s) t =
 fun tm m ->
  match m with
  | Metadef { data = Undef_meta { status; _ }; termctx; ty } ->
      Metadef { data = Def_meta { tm; energy = energy status }; termctx; ty }
  | Metadef { data = Def_meta _; _ } ->
      fatal (Anomaly "trying to define already-defined metavariable")

type (_, _) wrapped = Wrap : ('d, 'b * 's) t -> ('b, 's) wrapped
