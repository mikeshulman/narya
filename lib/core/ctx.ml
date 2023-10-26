(* This module should not be opened, but used qualified *)

open Util
open Dim
open Term
open Value

(* A context is a list of variables, each of which has a value that is a normal form.  Often the "value" of a variable will just be ITSELF, represented by a De Bruijn LEVEL, together of course with its type.  This can then appear in the types of later variables.  In particular, the LENGTH of this context, which is its type parameter as a type-level nat, is the current De Bruijn LEVEL for new variables to be added.  We can look up the INDEX of a TERM VARIABLE into this Bwv to get its type, but not of course the LEVEL of a VALUE VARIABLE.

   The "int option" stores the level of the variable separately from its value.  If a term variable is bound to a value other than itself, then the "int option" will be None (and the value will be that value).

   We also remember which of the variables in the context are "visible", i.e. have a name in scope for the user.  An element of (a, b) Ctx.t is a length-b context in which only a of the variables are visible.  We then use b for counting De Bruijn LEVELS, and for De Bruijn INDICES IN CHECKED TERMS, as well as for readback.  However, since the user can only refer to a of the variables, and the parser doesn't know about invisible variables (they are determined by semantic considerations, e.g. implicit arguments of constructors in match patterns), we use a for De Bruijn INDICES IN RAW TERMS.  Thus the index of a variable can change when it is typechecked.  But our intrinsically well-scoped indices manage this issue smoothly, ensuring that the correct kind of index is always used in the correct place. *)
type (_, _) t =
  | Emp : (N.zero, N.zero) t
  | Vis : ('a, 'b) t * int option * normal -> ('a N.suc, 'b N.suc) t
  | Invis : ('a, 'b) t * int option * normal -> ('a, 'b N.suc) t

let rec level : type a b. (a, b) t -> int =
 fun ctx ->
  match ctx with
  | Emp -> 0
  | Vis (ctx, _, _) -> level ctx + 1
  | Invis (ctx, _, _) -> level ctx + 1

let empty : (N.zero, N.zero) t = Emp

let rec levels : type a b. (a, b) t -> (int option, b) Bwv.t =
 fun ctx ->
  match ctx with
  | Emp -> Emp
  | Vis (ctx, i, _) ->
      let rest = levels ctx in
      Snoc (rest, i)
  | Invis (ctx, i, _) ->
      let rest = levels ctx in
      Snoc (rest, i)

(* When we look up an a-index variable in a context, we find the level (if any), the value, and the corresponding b-index variable. *)
let rec lookup : type a b. (a, b) t -> a N.index -> int option * normal * b N.index =
 fun ctx k ->
  match ctx with
  | Vis (ctx, j, x) -> (
      match k with
      | Top -> (j, x, Top)
      | Pop k ->
          let j, x, v = lookup ctx k in
          (j, x, Pop v))
  | Emp -> (
      match k with
      | _ -> .)
  | Invis (ctx, _, _) ->
      let j, x, v = lookup ctx k in
      (j, x, Pop v)

(* Every context has an underlying environment that substitutes each (level) variable for itself (index).  This environment ALWAYS HAS DIMENSION ZERO, and therefore in particular the variables don't need to come with their boundaries. *)
let rec env : type a b. (a, b) t -> (D.zero, b) env = function
  | Emp -> Emp D.zero
  | Vis (ctx, _, v) -> Ext (env ctx, CubeOf.singleton v.tm)
  | Invis (ctx, _, v) -> Ext (env ctx, CubeOf.singleton v.tm)

(* Evaluate a term in (the environment of) a context.  Thus, replace its De Bruijn indices with De Bruijn levels, and substitute the values of variables with definitions. *)
let eval : type a b. (a, b) t -> b term -> value = fun ctx tm -> Norm.eval (env ctx) tm

(* Extend a context by one new variable, without a value but with an assigned type. *)
let ext : type a b. (a, b) t -> value -> (a N.suc, b N.suc) t =
 fun ctx ty ->
  let n = level ctx in
  Vis (ctx, Some n, { tm = var n ty; ty })

(* Extend a context by one new variable with an assigned value. *)
let ext_let (ctx : ('a, 'b) t) (v : normal) : ('a N.suc, 'b N.suc) t = Vis (ctx, None, v)

(* Extend a context by a finite number of new variables, whose types and values are specified in a Bwv. *)
let rec exts :
    type a b ab c d db.
    (a, d) t ->
    (a, b, ab) N.plus ->
    (d, b, db) N.plus ->
    (int option * normal, b) Bwv.t ->
    (ab, db) t =
 fun ctx ab db keys ->
  match (ab, db, keys) with
  | Zero, Zero, Emp -> ctx
  | Suc ab, Suc db, Snoc (keys, key) ->
      let newctx = exts ctx ab db keys in
      Vis (newctx, fst key, snd key)

(* Extend a context by a finite number of new variables, whose types are specified in a telescope (and hence may depend on the earlier ones).  Also return the new variables in a Bwd and the new environment extended by them. *)
let ext_tel :
    type a b c ac bc e ec.
    (a, e) t ->
    (D.zero, b) env ->
    (b, c, bc) Telescope.t ->
    (a, c, ac) N.plus ->
    (e, c, ec) N.plus ->
    (ac, ec) t * (D.zero, bc) env * (value, c) Bwv.t =
 fun ctx env tel ac ec ->
  let rec ext_tel :
      type a b c ac bc d dc e ec.
      (a, e) t ->
      (D.zero, b) env ->
      (b, c, bc) Telescope.t ->
      (a, c, ac) N.plus ->
      (e, c, ec) N.plus ->
      (d, c, dc) N.plus ->
      (value, d) Bwv.t ->
      (ac, ec) t * (D.zero, bc) env * (value, dc) Bwv.t =
   fun ctx env tel ac ec dc vars ->
    match (tel, ac, ec, dc) with
    | Emp, Zero, Zero, Zero -> (ctx, env, vars)
    | Ext (rty, rest), Suc _, Suc _, Suc _ ->
        let n = level ctx in
        let ty = Norm.eval env rty in
        let tm = var n ty in
        ext_tel
          (Vis (ctx, Some n, { tm; ty }))
          (Ext (env, CubeOf.singleton tm))
          rest (N.suc_plus'' ac) (N.suc_plus'' ec) (N.suc_plus'' dc)
          (Snoc (vars, tm)) in
  ext_tel ctx env tel ac ec (N.zero_plus (N.plus_right ac)) Emp

(* Let-bind some of the variables in a context *)
let rec bind_some : type a e. (int -> normal option) -> (a, e) t -> (a, e) t =
 fun binder ctx ->
  match ctx with
  | Emp -> Emp
  | Vis (ctx, None, x) -> Vis (bind_some binder ctx, None, x)
  | Vis (ctx, Some i, x) -> (
      match binder i with
      | None -> Vis (bind_some binder ctx, Some i, x)
      | Some t -> Vis (bind_some binder ctx, None, t))
  | Invis (ctx, None, x) -> Invis (bind_some binder ctx, None, x)
  | Invis (ctx, Some i, x) -> (
      match binder i with
      | None -> Invis (bind_some binder ctx, Some i, x)
      | Some t -> Invis (bind_some binder ctx, None, t))
