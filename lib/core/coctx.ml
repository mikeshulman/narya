(* This module should not be opened, but used qualified *)

open Util
open Dim
open Value

(* A context (defined in ctx.ml) is a mapping from De Bruijn indices to types and values, represented as a Bwv with indices indexing into it.  Many of the values are De Bruijn level variables.  This also contains enough information to generate new De Bruijn levels, as there cannot be more of them than there are in the context.

   A CO-CONTEXT, defined in this file, is a mapping from De Bruijn LEVELS to De Bruijn INDICES.  However, we still represent it as a Bwv of levels, with looking up a level done by iterating backwards through it, so that when we extend it on the right with new levels, the indices associated to all the existing levels increment.  We also store separately the next new level to generate, which in this case may be greater than the length of the Bwv.  Failing to find a level when doing a backwards lookup happens during a failed occurs-check, for instance. *)

type 'a t = { vars : (int, 'a) Bwv.t; level : int }

let empty : N.zero t = { vars = Emp; level = 0 }

(* Analogous to Ctx.dom_vars, but we return the levels in a Cube also so that they can be picked out with subcubes before being appended to co-contexts. *)
let dom_vars :
    type m a f af. a t -> (m, value) CubeOf.t -> (m, int) CubeOf.t * (m, value) CubeOf.t * int =
 fun ctx doms ->
  let argtbl = Hashtbl.create 10 in
  let level = ref ctx.level in
  let [ vars; args ] =
    CubeOf.pmap
      {
        map =
          (fun fa [ dom ] ->
            let ty =
              inst dom
                (TubeOf.build D.zero
                   (D.zero_plus (dom_sface fa))
                   {
                     build =
                       (fun fc ->
                         Hashtbl.find argtbl (SFace_of (comp_sface fa (sface_of_tface fc))));
                   }) in
            let lvl = !level in
            level := lvl + 1;
            let v = { tm = var lvl ty; ty } in
            Hashtbl.add argtbl (SFace_of fa) v;
            [ lvl; v.tm ]);
      }
      [ doms ] (Cons (Cons Nil)) in
  (vars, args, !level)
