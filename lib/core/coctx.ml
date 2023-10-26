(* This module should not be opened, but used qualified *)

open Util

(* A context (defined in ctx.ml) is a mapping from De Bruijn indices to types and values, represented as a Bwv with indices indexing into it.  Many of the values are De Bruijn level variables.  This also contains enough information to generate new De Bruijn levels, as there cannot be more of them than there are in the context.

   A CO-CONTEXT, defined in this file, is a mapping from De Bruijn LEVELS to De Bruijn INDICES.  However, we still represent it as a Bwv of levels, with looking up a level done by iterating backwards through it, so that when we extend it on the right with new levels, the indices associated to all the existing levels increment.

   We also store separately the next new level to generate, which in this case may be greater than the length of the Bwv, because there may be some levels that occur in values but don't appear in the co-context.  This means that looking up a level in a co-context can sometimes fail even for a valid level, which is intentional.  For instance, this happens during a failed occurs-check, where the levels appearing in the co-context are those that are allowed to occur.

   In addition, we allow some indices in the co-context to be associated with no level (a None in the Bwv rather than a Some).  Those indices can then NEVER occur in terms produced by reading back in such a co-context.  This happens naturally when a co-context is made from a context in which some of the index variables are let-bound to a nontrivial value, as those variables have no associated level and do not themselves appear in terms.  They could simply be omitted from the co-context, but it makes the scoping algebra simpler to keep them. *)

type 'a t = { vars : (int option, 'a) Bwv.t; level : int }

let empty : N.zero t = { vars = Emp; level = 0 }

(* The co-context corresponding to a context includes all the invisible variables. *)
let of_ctx : type a b. (a, b) Ctx.t -> b t =
 fun ctx ->
  let vars = Ctx.levels ctx in
  { vars; level = Ctx.level ctx }
