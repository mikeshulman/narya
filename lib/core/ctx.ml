(* This module should not be opened, but used qualified *)

open Util
open Dim
open Term
open Value
open Norm

(* A context is a list of variables, each of which has a value that is a normal form.  Often the "value" of a variable will just be ITSELF, represented by a De Bruijn LEVEL, together of course with its type.  This can then appear in the types of later variables.  In particular, the LENGTH of this context, which is its type parameter as a type-level nat, is the current De Bruijn LEVEL for new variables to be added.  We can look up the INDEX of a TERM VARIABLE into this Bwv to get its type, but not of course the LEVEL of a VALUE VARIABLE. *)
type 'a t = (normal, 'a) Bwv.t

let level : 'a t -> int = fun ctx -> N.to_int (Bwv.length ctx)

(* The empty context *)
let empty : N.zero t = Emp

(* Every context has an underlying environment that substitutes each (level) variable for itself (index).  This environment ALWAYS HAS DIMENSION ZERO, and therefore in particular the variables don't need to come with their boundaries. *)
let rec env : type a. a t -> (D.zero, a) env = function
  | Emp -> Emp D.zero
  | Snoc (ctx, v) -> Ext (env ctx, CubeOf.build D.zero { build = (fun _ -> v.tm) })

(* Evaluate a term in (the environment of) a context.  Thus, replace its De Bruijn indices with De Bruijn levels, and substitute the values of variables with definitions. *)
let eval : type a. a t -> a term -> value = fun ctx tm -> eval (env ctx) tm

(* Extend a context by one new variable, without a value but with an assigned type. *)
let ext : type a. a t -> value -> a N.suc t =
 fun ctx ty -> Snoc (ctx, { tm = var (level ctx) ty; ty })

(* Extend a context by a finite number of new variables, whose types are specified in a hashtable. *)
let rec exts :
    type a b ab c. a t -> (a, b, ab) N.plus -> (c, b) Bwv.t -> (c, value) Hashtbl.t -> ab t =
 fun ctx ab keys vals ->
  match (ab, keys) with
  | Zero, Emp -> ctx
  | Suc ab, Snoc (keys, key) ->
      let newctx = exts ctx ab keys vals in
      let ty = Hashtbl.find vals key in
      Snoc (newctx, { tm = var (level newctx) ty; ty })

(* To typecheck a lambda, do an eta-expanding equality check, or check pi-types for equality, we must create one new variable for each argument in the boundary.  With De Bruijn levels, these variables are just sequential numbers after n.  But to make these variables into values, we need to annotate them with their types, which in general are instantiations of the domains at previous variables.  Thus, we assemble them in a hashtable as we create them for random access to the previous ones. *)
let dom_vars :
    type m a f af.
    a t ->
    (m, f) count_faces ->
    (a, f, af) N.plus ->
    (m, value) CubeOf.t ->
    af t * (m, value) CubeOf.t =
 fun ctx faces af doms ->
  let argtbl = Hashtbl.create 10 in
  let ctx, args =
    CubeOf.fold_left_append_map
      {
        fold =
          (fun ctx fa dom ->
            let ty =
              inst dom
                (TubeOf.build D.zero
                   (D.zero_plus (dom_sface fa))
                   {
                     build =
                       (fun fc ->
                         Hashtbl.find argtbl (SFace_of (comp_sface fa (sface_of_tface fc))));
                   }) in
            let v = { tm = var (level ctx) ty; ty } in
            Hashtbl.add argtbl (SFace_of fa) v;
            (v, v.tm));
      }
      ctx faces af doms in
  (ctx, args)
