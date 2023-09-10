(* This module should not be opened, but used qualified *)

open Util

(* A context (defined in ctx.ml) is a mapping from De Bruijn indices to types and values, represented as a Bwv with indices indexing into it.  Many of the values are De Bruijn level variables.  This also contains enough information to generate new De Bruijn levels, as there cannot be more of them than there are in the context.

   A CO-CONTEXT, defined in this file, is a mapping from De Bruijn LEVELS to De Bruijn INDICES.  However, we still represent it as a Bwv of levels, with looking up a level done by iterating backwards through it, so that when we extend it on the right with new levels, the indices associated to all the existing levels increment.  We also store separately the next new level to generate, which in this case may be greater than the length of the Bwv.  Failing to find a level when doing a backwards lookup happens during a failed occurs-check, for instance. *)

type 'a t = { vars : (int, 'a) Bwv.t; level : int }

let empty : N.zero t = { vars = Emp; level = 0 }
