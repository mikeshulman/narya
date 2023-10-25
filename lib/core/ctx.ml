(* This module should not be opened, but used qualified *)

open Util
open Dim
open Term
open Value
open Norm

(* A context is a list of variables, each of which has a value that is a normal form.  Often the "value" of a variable will just be ITSELF, represented by a De Bruijn LEVEL, together of course with its type.  This can then appear in the types of later variables.  In particular, the LENGTH of this context, which is its type parameter as a type-level nat, is the current De Bruijn LEVEL for new variables to be added.  We can look up the INDEX of a TERM VARIABLE into this Bwv to get its type, but not of course the LEVEL of a VALUE VARIABLE.

   The "int option" stores the level of the variable separately from its value.  If a term variable is bound to a value other than itself, then the "int option" will be None (and the value will be that value). *)
type 'a t = (int option * normal, 'a) Bwv.t

let level : 'a t -> int = fun ctx -> N.to_int (Bwv.length ctx)
let empty : N.zero t = Emp
let levels (ctx : 'a t) : (int option, 'a) Bwv.t = Bwv.map fst ctx
let lookup (ctx : 'a t) (ix : 'a N.index) : int option * normal = Bwv.nth ix ctx

(* Every context has an underlying environment that substitutes each (level) variable for itself (index).  This environment ALWAYS HAS DIMENSION ZERO, and therefore in particular the variables don't need to come with their boundaries. *)
let rec env : type a. a t -> (D.zero, a) env = function
  | Emp -> Emp D.zero
  | Snoc (ctx, (_, v)) -> Ext (env ctx, CubeOf.singleton v.tm)

(* Evaluate a term in (the environment of) a context.  Thus, replace its De Bruijn indices with De Bruijn levels, and substitute the values of variables with definitions. *)
let eval : type a. a t -> a term -> value = fun ctx tm -> eval (env ctx) tm

(* Extend a context by one new variable, without a value but with an assigned type. *)
let ext : type a. a t -> value -> a N.suc t =
 fun ctx ty ->
  let n = level ctx in
  Snoc (ctx, (Some n, { tm = var n ty; ty }))

(* Extend a context by one new variable with an assigned value. *)
let ext_let (ctx : 'a t) (v : normal) : 'a N.suc t = Snoc (ctx, (None, v))

(* Extend a context by a finite number of new variables, whose types and values are specified in a Bwv. *)
let rec exts : type a b ab c. a t -> (a, b, ab) N.plus -> (int option * normal, b) Bwv.t -> ab t =
 fun ctx ab keys ->
  match (ab, keys) with
  | Zero, Emp -> ctx
  | Suc ab, Snoc (keys, key) ->
      let newctx = exts ctx ab keys in
      Snoc (newctx, key)

(* Extend a context by a finite number of new variables, whose types are specified in a telescope (and hence may depend on the earlier ones).  Also return the new variables in a Bwd and the new environment extended by them. *)
let ext_tel :
    type a b c ac bc.
    a t ->
    (D.zero, b) env ->
    (b, c, bc) Telescope.t ->
    (a, c, ac) N.plus ->
    ac t * (D.zero, bc) env * (value, c) Bwv.t =
 fun ctx env tel ac ->
  let rec ext_tel :
      type a b c ac bc d dc.
      a t ->
      (D.zero, b) env ->
      (b, c, bc) Telescope.t ->
      (a, c, ac) N.plus ->
      (d, c, dc) N.plus ->
      (value, d) Bwv.t ->
      ac t * (D.zero, bc) env * (value, dc) Bwv.t =
   fun ctx env tel ac dc vars ->
    match (tel, ac, dc) with
    | Emp, Zero, Zero -> (ctx, env, vars)
    | Ext (rty, rest), Suc _, Suc _ ->
        let n = level ctx in
        let ty = Norm.eval env rty in
        let tm = var n ty in
        ext_tel
          (Snoc (ctx, (Some n, { tm; ty })))
          (Ext (env, CubeOf.singleton tm))
          rest (N.suc_plus'' ac) (N.suc_plus'' dc)
          (Snoc (vars, tm)) in
  ext_tel ctx env tel ac (N.zero_plus (N.plus_right ac)) Emp

(* Let-bind some of the variables in a context *)
let rec bind_some : type a. (int -> normal option) -> a t -> a t =
 fun binder ctx ->
  match ctx with
  | Emp -> Emp
  | Snoc (ctx, (None, x)) -> Snoc (bind_some binder ctx, (None, x))
  | Snoc (ctx, (Some i, x)) -> (
      match binder i with
      | None -> Snoc (bind_some binder ctx, (Some i, x))
      | Some t -> Snoc (bind_some binder ctx, (None, t)))
