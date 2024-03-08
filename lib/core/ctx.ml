(* This module should not be opened, but used qualified *)

open Bwd
open Util
open Tbwd
open Dim
open Reporter
open Syntax
open Term
open Value
open Inst

(* To first approximation, a context is a list of variables, each of which has a value that is a normal form.  Often the "value" of a variable will just be ITSELF, represented by a De Bruijn LEVEL, together of course with its type.  This can then appear in the types of later variables.  In particular, the LENGTH of this context, which is its type parameter as a type-level nat, is the current De Bruijn LEVEL for new variables to be added.

   We can look up the INDEX of a TERM VARIABLE into this Bwv to get its type.  This operation is statically guaranteed to succeed, since all De Bruijn indices are intrinsically well-scoped.

   We can also look up the LEVEL of a VALUE VARIABLE to find its corresponding term-variable index (and we do this during readback).  However, this operation is not statically guaranteed to succeed.  Indeed, in some cases it we intend for it to fail, e.g. during an occurs-check.  To enable this operation, we separately store for each index variable its corresponding level, if any, in addition to its value.  (If it is let-bound to a value, then it has no associated level variable.) *)

(* To second approximation, a "context" is actually a WEAKENING SUBSTITUTION from one De Bruijn INDEX context to another.  The index variables that arise from parsing are counted based on the number of textually in-scope variables, but internally there may be variables other than these, for instance if a pattern binds some arguments implicitly.  Thus, an element of (a, b) Ctx.t is actually a length-b context in which only a of the variables are "visible".  We then use b for counting the next De Bruijn LEVEL to create, and for De Bruijn INDICES IN CHECKED TERMS, as well as for readback.  However, since the user can only refer to a of the variables, and the parser doesn't know about invisible variables (they are determined by semantic considerations, e.g. implicit arguments of constructors in match patterns), we use a for De Bruijn INDICES IN RAW TERMS.  This means the index of a variable can change when it is typechecked, but our intrinsically well-scoped indices manage this issue smoothly, ensuring that the correct kind of index is always used in the correct place. *)

(* To third approximation, a context is not a flat list of variables, but a list of "cubes" of variables.  Frequently when introducing variables, we introduce a whole cube of them (e.g. when abstracting into a higher-dimensional pi-type, or pattern-matching against a higher-dimensional datatype), and we avoid "linearizing" these variables as much as possible.  Thus, index variables are not just a (well-scoped) natural number, but are paired with a dimension and a strict face of that dimension, and variables are stored in cubes.

   More precisely, the RAW parameter 'a is a simple type-level natural number, since the parser can't tell what dimensions things have, and a raw index variable is paired with a face of an arbitrary dimension corresponding to how the user used it.  However, the CHECKED parameter 'b is actually a type-level list of dimensions (an "hctx"), and a checked index variable is paired with a face *of the corresponding dimension*.  For level variables we use a pair of integers: one for the position in the context, and the other that counts through the variables in each cube.  (Since levels are only ever compared for equality, the ordering of the latter numbers doesn't matter.) *)

type (_, _) entry =
  (* Add a cube of internal variables that are visible to the parser as a cube of variables. *)
  | Vis : 'n variables * ('n, level option * normal) CubeOf.t -> (N.one, 'n) entry
  (* Add a cube of internal variables that are not visible to the parser. *)
  | Invis : ('n, level option * normal) CubeOf.t -> (N.zero, 'n) entry
  (* Add a cube of internal variables that are visible to the parser as a list of ordinary variables. *)
  | Split :
      ('n, 'f) count_faces * 'n variables * ('n, level option * normal) CubeOf.t
      -> ('f, 'n) entry

type (_, _) t =
  | Emp : (N.zero, emp) t
  | Snoc : ('a, 'b) t * ('x, 'n) entry * ('a, 'x, 'ax) N.plus -> ('ax, ('b, 'n) snoc) t

let vis :
    type a b n.
    (a, b) t -> n variables -> (n, level option * normal) CubeOf.t -> (a N.suc, (b, n) snoc) t =
 fun ctx xs vars -> Snoc (ctx, Vis (xs, vars), Suc Zero)

let invis : type a b n. (a, b) t -> (n, level option * normal) CubeOf.t -> (a, (b, n) snoc) t =
 fun ctx vars -> Snoc (ctx, Invis vars, Zero)

let split :
    type a b n f af.
    (a, b) t ->
    (n, f) count_faces ->
    (a, f, af) N.plus ->
    n variables ->
    (n, level option * normal) CubeOf.t ->
    (af, (b, n) snoc) t =
 fun ctx af pf name vars -> Snoc (ctx, Split (af, name, vars), pf)

let rec length : type a b. (a, b) t -> int = function
  | Emp -> 0
  | Snoc (ctx, _, _) -> length ctx + 1

let empty : (N.zero, emp) t = Emp

(* When we look up a visible variable in a context, we find the level (if any), the value, and the corresponding possibly-invisible variable. *)
let rec lookup : type a b n. (a, b) t -> a Raw.index -> level option * normal * b index =
 fun ctx k ->
  match ctx with
  | Emp -> (
      match k with
      | _ -> .)
  | Snoc (ctx, Vis (_, x), Suc Zero) -> (
      match k with
      | Top, None ->
          (* If the raw index variable doesn't have a specified face, it means the top face. *)
          let n = CubeOf.dim x in
          let j, x = CubeOf.find_top x in
          (j, x, Top (id_sface n))
      | Top, Some (Any_sface fa) -> (
          match compare (cod_sface fa) (CubeOf.dim x) with
          | Eq ->
              let j, x = CubeOf.find x fa in
              (j, x, Top fa)
          | Neq -> fatal (Invalid_variable_face (CubeOf.dim x, fa)))
      | Pop k, fa ->
          let j, x, v = lookup ctx (k, fa) in
          (j, x, Pop v))
  | Snoc (ctx, Invis _, Zero) ->
      let j, x, v = lookup ctx k in
      (j, x, Pop v)
  | Snoc (ctx, Split (af, _, xs), pf) -> lookup_face pf (sfaces af) ctx xs k

and lookup_face :
    type a f af b n.
    (a, f, af) N.plus ->
    (n sface_of, f) Bwv.t ->
    (a, b) t ->
    (n, level option * normal) CubeOf.t ->
    af Raw.index ->
    level option * normal * (b, n) snoc index =
 fun pf sf ctx xs k ->
  match (pf, sf) with
  | Zero, Emp ->
      let i, x, v = lookup ctx k in
      (i, x, Pop v)
  | Suc pf, Snoc (sf, SFace_of fb) -> (
      match k with
      | Pop k, fa -> lookup_face pf sf ctx xs (k, fa)
      | Top, None ->
          let i, x = CubeOf.find xs fb in
          (i, x, Top fb)
      | Top, Some (Any_sface fa) -> fatal (Invalid_variable_face (D.zero, fa)))

(* We can also look up a possibly-invisible variable in a context, in which case the only things to return are the possible-level and value. *)
let rec lookup_invis : type a b. (a, b) t -> b index -> level option * normal =
 fun ctx k ->
  match ctx with
  | Emp -> (
      match k with
      | _ -> .)
  | Snoc (ctx, Vis (_, x), Suc Zero) -> (
      match k with
      | Top fa -> CubeOf.find x fa
      | Pop k -> lookup_invis ctx k)
  | Snoc (ctx, Invis x, Zero) -> (
      match k with
      | Top fa -> CubeOf.find x fa
      | Pop k -> lookup_invis ctx k)
  | Snoc (ctx, Split (_, _, x), _) -> (
      match k with
      | Top fa -> CubeOf.find x fa
      | Pop k -> lookup_invis ctx k)

(* Look up a De Bruijn level in a context and find the corresponding possibly-invisible index, if one exists. *)
let rec find_level : type a b. (a, b) t -> level -> b index option =
 fun ctx i ->
  match ctx with
  | Emp -> None
  | Snoc (ctx, Vis (_, vars), Suc Zero) -> find_level_in_cube ctx vars i
  | Snoc (ctx, Invis vars, Zero) -> find_level_in_cube ctx vars i
  | Snoc (ctx, Split (_, _, vars), _) -> find_level_in_cube ctx vars i

and find_level_in_cube :
    type a b n. (a, b) t -> (n, level option * normal) CubeOf.t -> level -> (b, n) snoc index option
    =
 fun ctx vars i ->
  let open CubeOf.Monadic (Monad.State (struct
    type t = (b, n) snoc index option
  end)) in
  match
    miterM
      { it = (fun fa [ (j, _) ] s -> if j = Some i then ((), Some (Top fa)) else ((), s)) }
      [ vars ] None
  with
  | (), Some v -> Some v
  | (), None -> Option.map (fun v -> Pop v) (find_level ctx i)

(* Every context has an underlying environment that substitutes each (level) variable for itself (index).  This environment ALWAYS HAS DIMENSION ZERO, and therefore in particular the variables don't need to come with any boundaries. *)
let rec env : type a b. (a, b) t -> (D.zero, b) env = function
  | Emp -> Emp D.zero
  | Snoc (ctx, Vis (_, v), Suc Zero) ->
      Ext (env ctx, CubeOf.mmap { map = (fun _ [ x ] -> CubeOf.singleton (snd x).tm) } [ v ])
  | Snoc (ctx, Invis v, Zero) ->
      Ext (env ctx, CubeOf.mmap { map = (fun _ [ x ] -> CubeOf.singleton (snd x).tm) } [ v ])
  | Snoc (ctx, Split (_, _, v), _) ->
      Ext (env ctx, CubeOf.mmap { map = (fun _ [ x ] -> CubeOf.singleton (snd x).tm) } [ v ])

(* Evaluate a case tree or term in (the environment of) a context.  Thus, replace its De Bruijn indices with De Bruijn levels, and substitute the values of variables with definitions. *)
let eval : type a b s. (a, b) t -> (b, s) term -> s evaluation =
 fun ctx tm -> Norm.eval (env ctx) tm

let eval_term : type a b. (a, b) t -> (b, kinetic) term -> kinetic value =
 fun ctx tm -> Norm.eval_term (env ctx) tm

(* Extend a context by one new variable, without a value but with an assigned type. *)
let ext : type a b. (a, b) t -> string option -> kinetic value -> (a N.suc, (b, D.zero) snoc) t =
 fun ctx x ty ->
  let n = length ctx in
  vis ctx (singleton_variables D.zero x)
    (CubeOf.singleton (Some (n, 0), { tm = var (n, 0) ty; ty }))

(* Extend a context by one new variable with an assigned value. *)
let ext_let : type a b. (a, b) t -> string option -> normal -> (a N.suc, (b, D.zero) snoc) t =
 fun ctx x v -> vis ctx (singleton_variables D.zero x) (CubeOf.singleton (None, v))

(* Extend a context by a finite number of cubes of new visible variables at some dimension, with boundaries, whose types are specified by the evaluation of some telescope in some (possibly higher-dimensional) environment (and hence may depend on the earlier ones).  Also return the new variables in a Bwd of Cubes, and the new environment extended by the *top-dimensional variables only*. *)
let ext_tel :
    type a b c ac bc e ec n.
    (a, e) t ->
    (n, b) env ->
    (* Note that c is a Fwn, since it is the length of a telescope. *)
    (string option, c) Vec.t ->
    (b, c, bc) Telescope.t ->
    (a, c, ac) Fwn.bplus ->
    (e, c, n, ec) Tbwd.snocs ->
    (ac, ec) t * (n, bc) env * (n, kinetic value) CubeOf.t Bwd.t =
 fun ctx env xs tel ac ec ->
  let rec ext_tel :
      type a b c ac bc d e ec.
      (a, e) t ->
      (n, b) env ->
      (string option, c) Vec.t ->
      (b, c, bc) Telescope.t ->
      (a, c, ac) Fwn.bplus ->
      (e, c, n, ec) Tbwd.snocs ->
      (n, kinetic value) CubeOf.t Bwd.t ->
      (ac, ec) t * (n, bc) env * (n, kinetic value) CubeOf.t Bwd.t =
   fun ctx env xs tel ac ec vars ->
    match (xs, tel, ac) with
    | [], Emp, Zero ->
        let Zero, Zero = (ac, ec) in
        (ctx, env, vars)
    | x :: xs, Ext (x', rty, rest), Suc ac ->
        let newvars, newnfs =
          dom_vars (length ctx)
            (CubeOf.build (dim_env env)
               { build = (fun fa -> Norm.eval_term (Act (env, op_of_sface fa)) rty) }) in
        let x =
          match x with
          | Some x -> Some x
          | None -> x' in
        let newctx = vis ctx (`Cube x) newnfs in
        ext_tel newctx
          (Ext (env, CubeOf.singleton newvars))
          xs rest ac (Tbwd.snocs_suc ec)
          (Snoc (vars, newvars)) in
  ext_tel ctx env xs tel ac ec Emp

(* Let-bind some of the variables in a context *)

let bind_some_cube :
    type n.
    (level -> normal option) ->
    (n, level option * normal) CubeOf.t ->
    (n, level option * normal) CubeOf.t =
 fun binder xs ->
  CubeOf.mmap
    {
      map =
        (fun _ [ (i, x) ] ->
          match i with
          | None -> (i, x)
          | Some i -> (
              match binder i with
              | None -> (Some i, x)
              | Some t -> (None, t)));
    }
    [ xs ]

let rec bind_some : type a e n. (level -> normal option) -> (a, e) t -> (a, e) t =
 fun binder ctx ->
  match ctx with
  | Emp -> Emp
  | Snoc (ctx, Vis (name, xs), Suc Zero) ->
      vis (bind_some binder ctx) name (bind_some_cube binder xs)
  | Snoc (ctx, Invis xs, Zero) -> invis (bind_some binder ctx) (bind_some_cube binder xs)
  | Snoc (ctx, Split (af, name, xs), pf) ->
      split (bind_some binder ctx) af pf name (bind_some_cube binder xs)

(* Following Cockx's thesis, in this file we call forwards contexts "telescopes", since they generally are going to get appended to a "real", backwards, context.  They are indexed by a raw length that is a *forwards* natural number, and a checked length that is a *forwards* hctx. *)
(* type (_, _) tel =
     | Nil : (Fwn.zero, nil) tel
     | Snoc : ('x, 'n) entry * ('a, 'b) tel * ('x, 'a, 'xa) Fwn.fplus -> ('xa, ('n, 'b) cons) tel *)

(* Apply a function to all the types and terms in a context. *)
let rec map : type a b. (normal -> normal) -> (a, b) t -> (a, b) t =
 fun f ctx ->
  match ctx with
  | Emp -> Emp
  | Snoc (ctx, Vis (name, xs), Suc Zero) ->
      vis (map f ctx) name (CubeOf.mmap { map = (fun _ [ (i, x) ] -> (i, f x)) } [ xs ])
  | Snoc (ctx, Invis xs, Zero) ->
      invis (map f ctx) (CubeOf.mmap { map = (fun _ [ (i, x) ] -> (i, f x)) } [ xs ])
  | Snoc (ctx, Split (af, name, xs), pf) ->
      split (map f ctx) af pf name (CubeOf.mmap { map = (fun _ [ (i, x) ] -> (i, f x)) } [ xs ])

let rec names : type a b. (a, b) t -> b Names.t = function
  | Emp -> Names.empty
  | Snoc (ctx, Vis (name, _), _) -> snd (Names.add (names ctx) name)
  | Snoc (ctx, Invis _, _) -> snd (Names.add_cube (names ctx) None)
  | Snoc (ctx, Split (_, name, _), _) -> snd (Names.add (names ctx) name)

let lookup_name : type a b. (a, b) t -> b index -> string list =
 fun ctx x -> Names.lookup (names ctx) x

(* Generate a case tree consisting of a sequence of abstractions corresponding to the (checked) variables in a context. *)
let rec lam : type a b. (a, b) t -> (b, potential) term -> (emp, potential) term =
 fun ctx tree ->
  match ctx with
  | Emp -> tree
  | Snoc (ctx, Vis (xs, vars), _) -> lam ctx (Lam (CubeOf.dim vars, xs, tree))
  | Snoc (ctx, Invis vars, _) -> lam ctx (Lam (CubeOf.dim vars, `Cube None, tree))
  | Snoc (ctx, Split (_, xs, vars), _) -> lam ctx (Lam (CubeOf.dim vars, xs, tree))

open Format

let pp_lvlopt ppf = function
  | Some (i, j) -> fprintf ppf "(%d,%d)" i j
  | None -> fprintf ppf "-"

let pp_variables :
    type n. Format.formatter -> n variables * (n, level option * normal) CubeOf.t -> unit =
 fun ppf (x, lvls) ->
  match x with
  | `Cube x ->
      fprintf ppf "%s = @[<hv 2>%s" (Option.value x ~default:"_")
        (match compare (CubeOf.dim lvls) D.zero with
        | Eq -> ""
        | Neq -> "(");
      CubeOf.miter
        {
          it =
            (fun fa [ i ] ->
              if Option.is_some (is_id_sface fa) then pp_lvlopt ppf (fst i)
              else fprintf ppf "%a,@ " pp_lvlopt (fst i));
        }
        [ lvls ];
      (match compare (CubeOf.dim lvls) D.zero with
      | Eq -> ()
      | Neq -> pp_print_string ppf ")");
      fprintf ppf "@]"
  | `Normal x ->
      fprintf ppf "@[<hv 2>(";
      CubeOf.miter
        {
          it =
            (fun fa [ x; i ] ->
              if Option.is_some (is_id_sface fa) then
                fprintf ppf "%s = %a" (Option.value x ~default:"_") pp_lvlopt (fst i)
              else fprintf ppf "%s = %a,@ " (Option.value x ~default:"_") pp_lvlopt (fst i));
        }
        [ x; lvls ];
      fprintf ppf ")@]"

let pp_ctx : type a b. Format.formatter -> (a, b) t -> unit =
 fun ppf ctx ->
  let rec pp : type a b. bool -> formatter -> (a, b) t -> unit =
   fun comma ppf ctx ->
    match ctx with
    | Emp -> ()
    | Snoc (ctx, Vis (x, lvls), _) ->
        fprintf ppf "%a%a" (pp true) ctx pp_variables (x, lvls);
        if comma then fprintf ppf ",@ "
    | Snoc (ctx, Invis lvls, _) ->
        fprintf ppf "%a%a" (pp true) ctx pp_variables (`Cube (Some "-"), lvls);
        if comma then fprintf ppf ",@ "
    | Snoc (ctx, Split (_, x, lvls), _) ->
        fprintf ppf "%a%a" (pp true) ctx pp_variables (x, lvls);
        if comma then fprintf ppf ",@ " in
  fprintf ppf "@[<hv 2>(%a)@]" (pp false) ctx
