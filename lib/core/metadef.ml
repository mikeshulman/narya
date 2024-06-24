(* This module should not be opened, but used qualified. *)

open Util
open Syntax
open Term

type ('b, 's) value = [ `None | `Nonrec of ('b, 's) term ]

type (_, _) t =
  | Metadef : {
      vars : (string option, 'a) Bwv.t option;
      termctx : ('a, 'b) Termctx.t;
      ty : ('b, kinetic) term;
      tm : ('b, 's) value;
      energy : 's energy;
    }
      -> (* This weird-looking parametrization is to match the implementation of Meta.Map. *)
      (unit, 'b * 's) t
