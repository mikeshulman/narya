(* This module should not be opened, but used qualified *)

open Bwd
open Util
open Tbwd
open Dim
open Dimbwd
open Reporter
open Term
open Value

(* To first approximation, a context is a list of variables, each of which has a value that is a normal form.  Often the "value" of a variable will just be ITSELF, represented by a De Bruijn LEVEL, together of course with its type.  This can then appear in the types of later variables.  In particular, the LENGTH of this context, which is its type parameter as a type-level nat, is the current De Bruijn LEVEL for new variables to be added.

   We can look up the INDEX of a TERM VARIABLE into this Bwv to get its type.  This operation is statically guaranteed to succeed, since all De Bruijn indices are intrinsically well-scoped.

   We can also look up the LEVEL of a VALUE VARIABLE to find its corresponding term-variable index (and we do this during readback).  However, this operation is not statically guaranteed to succeed.  Indeed, in some cases it we intend for it to fail, e.g. during an occurs-check.  To enable this operation, we separately store for each index variable its corresponding level, if any, in addition to its value.  (If it is let-bound to a value, then it has no associated level variable.) *)

(* To second approximation, a "context" is actually a WEAKENING SUBSTITUTION from one De Bruijn INDEX context to another.  The index variables that arise from parsing are counted based on the number of textually in-scope variables, but internally there may be variables other than these, for instance if a pattern binds some arguments implicitly.  Thus, an element of (a, b) Ctx.t is actually a length-b context in which only a of the variables are "visible".  We then use b for counting the next De Bruijn LEVEL to create, and for De Bruijn INDICES IN CHECKED TERMS, as well as for readback.  However, since the user can only refer to a of the variables, and the parser doesn't know about invisible variables (they are determined by semantic considerations, e.g. implicit arguments of constructors in match patterns), we use a for De Bruijn INDICES IN RAW TERMS.  This means the index of a variable can change when it is typechecked, but our intrinsically well-scoped indices manage this issue smoothly, ensuring that the correct kind of index is always used in the correct place. *)

(* To third approximation, a context is not a flat list of variables, but a list of "cubes" of variables.  Frequently when introducing variables, we introduce a whole cube of them (e.g. when abstracting into a higher-dimensional pi-type, or pattern-matching against a higher-dimensional datatype), and we avoid "linearizing" these variables as much as possible.  Thus, index variables are not just a (well-scoped) natural number, but are paired with a dimension and a strict face of that dimension, and variables are stored in cubes.

   More precisely, the RAW parameter 'a is a simple type-level natural number, since the parser can't tell what dimensions things have, and a raw index variable is paired with a face of an arbitrary dimension corresponding to how the user used it.  However, the CHECKED parameter 'b is actually a type-level list of dimensions (an "hctx"), and a checked index variable is paired with a face *of the corresponding dimension*.  For level variables we use a pair of integers: one for the position in the context, and the other that counts through the variables in each cube.  (Since levels are only ever compared for equality, the ordering of the latter numbers doesn't matter.) *)

(* To fourth approximation, a context (qua substitution) can also incorporate a permutation of the raw indices.  This is because the raw indices occur in the order that they are bound *textually*, whereas we require that the checked indices occur in a "logical" order so that the type and possible value of each variable involves only those appearing prior to it.  These can disconnect during a match, where the new variables bound as arguments of the matched constructor are last textually, but must be inserted earlier in the context to retain logical order.  We postpone this modification until later, first defining "Ordered" contexts and then adding the permutations. *)

(* The binding of each variable in a context is a "level option * normal".  But instead of exposing this literally as a product type, we use an abstract type with a constructor "Binding.make" and accessors "Binding.level" and "Binding.value".  The reason is that in the "bind_some" machinery below, we work with contexts where the binding of a variable is "known but not yet available" or "not yet computed".  So the internal implementation of Binding is actually a reference cell that usually stores a "Known" "level option * normal", but sometimes is Unknown or other times a Delayed "level option * normal". *)
module Binding : sig
  type t

  val make : level option -> normal -> t
  val level : t -> level option
  val value : t -> normal

  (* An unknown binding can be specified when we have its value. *)
  val unknown : unit -> t
  val specify : t -> level option -> normal -> unit

  (* A known but not-yet-available value is created by delaying it, and can be made available by forcing it. *)
  val delay : t -> t
  val force : t -> unit

  (* An error value raises an exception when accessed. *)
  val error : Reporter.Code.t -> t
end = struct
  type state =
    | Known of level option * normal
    | Unknown
    | Delayed of level option * normal
    | Error of Reporter.Code.t

  type t = state ref

  let make i x = ref (Known (i, x))

  let level b =
    match !b with
    | Known (i, _) -> i
    | Unknown | Delayed _ -> None
    | Error e -> fatal e

  let value b =
    match !b with
    | Known (_, x) -> x
    | Unknown | Delayed _ -> fatal (Anomaly "Undetermined context variable")
    | Error e -> fatal e

  let unknown () = ref Unknown
  let specify b i x = b := Known (i, x)
  let delay b = ref (Delayed (level b, value b))
  let error e = ref (Error e)

  let force b =
    match !b with
    | Known _ | Unknown -> ()
    | Delayed (i, x) -> b := Known (i, x)
    | Error e -> fatal e
end

(* Test whether all the variables in a cube of bindings are free (none are let-bound). *)
let all_free : type n. (n, Binding.t) CubeOf.t -> bool =
 fun b ->
  let open CubeOf.Monadic (Monad.Maybe) in
  Option.is_some (mmapM { map = (fun _ [ x ] -> Option.map (fun _ -> ()) (Binding.level x)) } [ b ])

(* A context is a list of "entries", which can be either visible or invisible in the raw world.  An (f,n) entry contains f raw variables and an n-dimensional cube of checked variables. *)
type (_, _) entry =
  (* Add a cube of internal variables that are visible to the parser as a list of cubes of variables, the list-of-cubes being obtained by decomposing the dimension as a sum.  Note that the division into a cube and non-cube part, and the sum of dimensions, are only relevant for looking up *raw* indices: they are invisible to the checked world, whose indices store the total face of mn. *)
  | Vis : {
      dim : 'm D.t;
      plusdim : ('m, 'n, 'mn) D.plus;
      (* We use an indexed cube to automatically count how many raw variables appear, by starting with zero and incrementing it for each entry in the cube.  It's tempting to want to start instead from the previous raw length of the context, thereby eliminating the "plus" parameter of Snoc, below; but this causes problems with telescopes (forwards contexts), below, whose raw indices are forwards natural numbers instead. *)
      vars : (N.zero, 'n, string option, 'f1) NICubeOf.t;
      bindings : ('mn, Binding.t) CubeOf.t;
      (* While typechecking a record, we expose the "self" variable as a list of "illusory" variables, visible only to raw terms, that are substituted at typechecking time with the fields of self. *)
      hasfields : ('m, 'f2) has_fields;
      fields : (D.zero Field.t * string, 'f2) Bwv.t;
      fplus : ('f1, 'f2, 'f) N.plus;
    }
      -> ('f, 'mn) entry
  (* Add a cube of internal variables that are not visible to the parser.  We also allow a vector of "field view" variables that look to the user like ordinary variables but actually expand *at typechecking time* to field projections of the top invisible variable. *)
  | Invis : ('n, Binding.t) CubeOf.t -> (N.zero, 'n) entry

let raw_entry : type f n. (f, n) entry -> f N.t = function
  | Vis { vars; fplus; _ } -> N.plus_out (NICubeOf.out N.zero vars) fplus
  | Invis _ -> N.zero

let dim_entry : type f n. (f, n) entry -> n D.t = function
  | Vis { bindings; _ } | Invis bindings -> CubeOf.dim bindings

(* Given an entry containing no let-bound variables, produce an "app" that says how to apply a function to its cube of (free) variables. *)
let app_entry : type f n. (f, n) entry -> app = function
  | Vis { bindings; _ } | Invis bindings ->
      if all_free bindings then
        let n = CubeOf.dim bindings in
        App (Arg (CubeOf.mmap { map = (fun _ [ x ] -> Binding.value x) } [ bindings ]), ins_zero n)
      else fatal (Anomaly "let-bound variable in Ctx.apps")

module Ordered = struct
  type (_, _) t =
    | Emp : (N.zero, emp) t
    | Snoc : ('a, 'b) t * ('x, 'n) entry * ('a, 'x, 'ax) N.plus -> ('ax, ('b, 'n) snoc) t
    (* A locked context permits no access to the variables behind it. *)
    | Lock : ('a, 'b) t -> ('a, 'b) t

  let vis : type a b f af m n mn.
      (a, b) t ->
      m D.t ->
      (m, n, mn) D.plus ->
      (N.zero, n, string option, f) NICubeOf.t ->
      (mn, Binding.t) CubeOf.t ->
      (a, f, af) N.plus ->
      (af, (b, mn) snoc) t =
   fun ctx dim plusdim vars bindings af ->
    Snoc
      ( ctx,
        Vis { dim; plusdim; vars; bindings; hasfields = No_fields; fields = Emp; fplus = Zero },
        af )

  let cube_vis : type a b n.
      (a, b) t -> string option -> (n, Binding.t) CubeOf.t -> (a N.suc, (b, n) snoc) t =
   fun ctx x vars ->
    let m = CubeOf.dim vars in
    vis ctx m (D.plus_zero m) (NICubeOf.singleton x) vars (Suc Zero)

  let vis_fields : type a b f1 f2 f af n.
      (a, b) t ->
      (N.zero, n, string option, f1) NICubeOf.t ->
      (n, Binding.t) CubeOf.t ->
      (D.zero Field.t * string, f2) Bwv.t ->
      (f1, f2, f) N.plus ->
      (a, f, af) N.plus ->
      (af, (b, n) snoc) t =
   fun ctx vars bindings fields fplus af ->
    let plusdim = D.zero_plus (CubeOf.dim bindings) in
    Snoc
      (ctx, Vis { dim = D.zero; plusdim; vars; bindings; hasfields = Has_fields; fields; fplus }, af)

  let invis : type a b n. (a, b) t -> (n, Binding.t) CubeOf.t -> (a, (b, n) snoc) t =
   fun ctx bindings -> Snoc (ctx, Invis bindings, Zero)

  let lock : type a b. (a, b) t -> (a, b) t = fun ctx -> Lock ctx

  let rec locked : type a b. (a, b) t -> bool = function
    | Emp -> false
    | Snoc (ctx, _, _) -> locked ctx
    | Lock _ -> true

  let rec checked_length : type a b. (a, b) t -> b Tbwd.t = function
    | Emp -> Emp
    | Snoc (ctx, _, _) -> Snoc (checked_length ctx)
    | Lock ctx -> checked_length ctx

  let rec raw_length : type a b. (a, b) t -> a N.t = function
    | Emp -> N.zero
    | Snoc (ctx, _, ax) -> N.plus_out (raw_length ctx) ax
    | Lock ctx -> raw_length ctx

  let rec length : type a b. (a, b) t -> int = function
    | Emp -> 0
    | Snoc (ctx, _, _) -> length ctx + 1
    | Lock ctx -> length ctx

  let empty : (N.zero, emp) t = Emp

  let rec dbwd : type a b. (a, b) t -> b Dbwd.t = function
    | Emp -> Word Zero
    | Snoc (ctx, e, _) ->
        let (Word b) = dbwd ctx in
        Word (Suc (b, dim_entry e))
    | Lock ctx -> dbwd ctx

  let rec apps : type a b. (a, b) t -> app Bwd.t = function
    | Emp -> Emp
    | Snoc (ctx, e, _) -> Snoc (apps ctx, app_entry e)
    | Lock ctx -> apps ctx

  (* When we look up a visible variable in a context, we find the level (if any), the value, and the corresponding possibly-invisible variable.  To do this we have to iterate through each cube of variables from right-to-left as we decrement the raw index looking for the corresponding face.  So we need an auxiliary type family to keep track of where we are in that iteration and what result type we're expecting. *)

  type (_, _, _, _) lookup =
    | Unfound : ('a, 'right, 'rest) N.plus * 'rest Raw.index -> ('a, 'right, 'b, 'n) lookup
    | Found : level option * normal * ('b, 'n) snoc index -> ('a, 'right, 'b, 'n) lookup

  (* This function is called on every step of that iteration through a cube.  It appears that we have to define it with an explicit type signature in order for it to end up sufficiently polymorphic. *)
  let lookup_folder : type left right l m n mn a b.
      m D.t ->
      (m, n, mn) D.plus ->
      (mn, Binding.t) CubeOf.t ->
      (l, n) sface ->
      (left, l, string option, right) NFamOf.t ->
      (a, right, b, mn) lookup ->
      (a, left, b, mn) lookup * (left, l, unit, right) NFamOf.t =
   fun m mn xs fb (NFamOf _) acc ->
    let found_it fa =
      let (Plus kl) = D.plus (dom_sface fb) in
      let fab = sface_plus_sface fa mn kl fb in
      let x = CubeOf.find xs fab in
      (Found (Binding.level x, Binding.value x, Index (Now, fab)), NFamOf.NFamOf ()) in
    match acc with
    | Found (i, x, v) -> (Found (i, x, v), NFamOf ())
    | Unfound (Suc p, (Pop k, fa)) -> (Unfound (p, (k, fa)), NFamOf ())
    | Unfound (_, (Top, None)) -> found_it (id_sface m)
    | Unfound (_, (Top, Some (Any_sface fa))) -> (
        match D.compare (cod_sface fa) m with
        | Eq -> found_it fa
        | Neq -> fatal (Invalid_variable_face (D.zero, fa)))

  (* The lookup function iterates through entries. *)
  let rec lookup : type a b.
      (a, b) t ->
      a Raw.index ->
      (* We return either an ordinary variable or an illusory field-access variable. *)
      [ `Var of level option * normal * b index | `Field of level * normal * D.zero Field.t ] =
   fun ctx k ->
    match (ctx, k) with
    | Emp, _ -> .
    | Snoc (ctx, e, pf), _ -> lookup_entry ctx e pf k
    | Lock _, _ -> fatal Locked_variable

  (* For each entry, we iterate through the list of fields or the cube of names, as appropriate. *)
  and lookup_entry : type a b f af n.
      (a, b) t ->
      (f, n) entry ->
      (a, f, af) N.plus ->
      af Raw.index ->
      [ `Var of level option * normal * (b, n) snoc index
      | `Field of level * normal * D.zero Field.t ] =
   fun ctx e pf k ->
    let pop = function
      | `Var (i, x, Index (v, fa)) -> `Var (i, x, Index (Later v, fa))
      | `Field f -> `Field f in
    match e with
    | Vis { dim; plusdim; vars; bindings; hasfields = _; fields; fplus } -> (
        let (Plus pf1) = N.plus (NICubeOf.out N.zero vars) in
        let pf12 = N.plus_assocl pf1 fplus pf in
        match N.index_in_plus pf12 (fst k) with
        | Right i -> (
            let b = CubeOf.find_top bindings in
            match Binding.level b with
            | Some lvl -> `Field (lvl, Binding.value b, fst (Bwv.nth i fields))
            | None -> fatal (Anomaly "missing level in field view"))
        | Left i -> (
            let module Fold = NICubeOf.Traverse (struct
              type 'right t = (a, 'right, b, n) lookup
            end) in
            match
              Fold.fold_map_right
                { foldmap = (fun fb -> lookup_folder dim plusdim bindings fb) }
                vars
                (Unfound (pf1, (i, snd k)))
            with
            | Unfound (Zero, k), _ -> pop (lookup ctx k)
            | Found (j, x, v), _ -> `Var (j, x, v)))
    | Invis _ ->
        let Zero = pf in
        pop (lookup ctx k)

  (* Look up a De Bruijn level in a context and find the corresponding possibly-invisible index, if one exists. *)
  let rec find_level : type a b. (a, b) t -> level -> b index option =
   fun ctx i ->
    match ctx with
    | Emp -> None
    | Snoc (ctx, Vis { bindings; _ }, _) -> find_level_in_cube ctx bindings i
    | Snoc (ctx, Invis bindings, _) -> find_level_in_cube ctx bindings i
    | Lock ctx -> find_level ctx i

  and find_level_in_cube : type a b n.
      (a, b) t -> (n, Binding.t) CubeOf.t -> level -> (b, n) snoc index option =
   fun ctx vars i ->
    let open CubeOf.Monadic (Monad.State (struct
      type t = (b, n) snoc index option
    end)) in
    match
      miterM
        {
          it =
            (fun fa [ x ] s ->
              if Binding.level x = Some i then ((), Some (Index (Now, fa))) else ((), s));
        }
        [ vars ] None
    with
    | (), Some v -> Some v
    | (), None -> Option.map (fun (Index (v, fa)) -> Index (Later v, fa)) (find_level ctx i)

  (* Every context has an underlying environment that substitutes each (level) variable for itself (index).  This environment ALWAYS HAS DIMENSION ZERO, and therefore in particular the variables don't need to come with any boundaries. *)

  let env_entry : type n. (n, Binding.t) CubeOf.t -> (n, kinetic lazy_eval) CubeOf.t =
   fun v ->
    CubeOf.mmap
      (* We defer the value because it might be Unknown or Delayed, but we don't want an error reported unless such a value is actually *used*. *)
      { map = (fun _ [ x ] -> defer (fun () -> Val (Binding.value x).tm)) }
      [ v ]

  (* This function traverses the entire context and computes the corresponding environment.  However, when we add permutations to environments below, we will also store a precomputed environment, so this function only needs to be called when the context has been globally modified. *)
  let rec env : type a b. (a, b) t -> (D.zero, b) env = function
    | Emp -> Emp D.zero
    | Snoc (ctx, Vis { bindings; _ }, _) ->
        LazyExt (env ctx, D.zero_plus (CubeOf.dim bindings), env_entry bindings)
    | Snoc (ctx, Invis bindings, _) ->
        LazyExt (env ctx, D.zero_plus (CubeOf.dim bindings), env_entry bindings)
    | Lock ctx -> env ctx

  (* Extend a context by one new variable, without a value but with an assigned type. *)
  let ext : type a b.
      (a, b) t -> string option -> kinetic value -> (a N.suc, (b, D.zero) snoc) t * Binding.t =
   fun ctx x ty ->
    let n = length ctx in
    let b = Binding.make (Some (n, 0)) { tm = var (n, 0) ty; ty } in
    (cube_vis ctx x (CubeOf.singleton b), b)

  (* Extend a context by one new variable with an assigned value. *)
  let ext_let : type a b.
      (a, b) t -> string option -> normal -> (a N.suc, (b, D.zero) snoc) t * Binding.t =
   fun ctx x v ->
    let b = Binding.make None v in
    (cube_vis ctx x (CubeOf.singleton b), b)

  (* Generate a case tree consisting of a sequence of abstractions corresponding to the (checked) variables in a context.  The context must contain NO LET-BOUND VARIABLES, including field-access variables, since abstracting over them would not be well-defined.  (In general, we couldn't just omit them, because some of the variables in a cube could be bound but not others, and cubes in the context yield cube abstractions.  However, at least when this comment was written, this function was only used for contexts consisting entirely of 0-dimensional cubes without let-bound variables.) *)
  let rec lam : type a b. (a, b) t -> (b, potential) term -> (emp, potential) term =
   fun ctx tree ->
    match ctx with
    | Emp -> tree
    | Lock ctx -> lam ctx tree
    | Snoc (ctx, Vis { dim; plusdim; vars; bindings; fplus = Zero; _ }, _) when all_free bindings ->
        lam ctx (Lam (Variables (dim, plusdim, vars), tree))
    | Snoc (ctx, Invis bindings, _) when all_free bindings ->
        lam ctx (Lam (singleton_variables (CubeOf.dim bindings) None, tree))
    | _ -> fatal (Anomaly "let-bound variable in Ctx.lam")

  (* Delete some level variables from a context by making their bindings into "unknown".  This will cause readback to raise No_such_level if it encounters one of those variables, which can then be trapped as an occurs-check. *)
  let rec forget_levels : type a b. (a, b) t -> (level -> bool) -> (a, b) t =
   fun ctx forget ->
    let forget_bindings : type n. (n, Binding.t) CubeOf.t -> (n, Binding.t) CubeOf.t =
     fun bindings ->
      CubeOf.mmap
        {
          map =
            (fun _ [ b ] ->
              match Binding.level b with
              | Some x when forget x -> Binding.unknown ()
              | _ -> b);
        }
        [ bindings ] in
    match ctx with
    | Emp -> Emp
    | Lock ctx -> Lock (forget_levels ctx forget)
    | Snoc (ctx, Vis ({ bindings; _ } as e), af) ->
        Snoc (ctx, Vis { e with bindings = forget_bindings bindings }, af)
    | Snoc (ctx, Invis bindings, af) -> Snoc (ctx, Invis (forget_bindings bindings), af)
end

(* Now we define contexts that add a permutation of the raw indices.  For efficiency reasons we also precompute its environment as the context is built and store it. *)

type ('a, 'b) t = Permute : ('a, 'i) N.perm * (D.zero, 'b) env * ('i, 'b) Ordered.t -> ('a, 'b) t

(* Nearly all the operations on ordered contexts are lifted to either ignore the permutations or add identities on the right. *)

let vis (Permute (p, env, ctx)) m mn xs vars af =
  let (Plus bf) = N.plus (N.plus_right af) in
  Permute
    ( N.perm_plus p af bf,
      LazyExt (env, D.zero_plus (CubeOf.dim vars), Ordered.env_entry vars),
      Ordered.vis ctx m mn xs vars bf )

let cube_vis ctx x vars =
  let m = CubeOf.dim vars in
  vis ctx m (D.plus_zero m) (NICubeOf.singleton x) vars (Suc Zero)

let vis_fields (Permute (p, env, ctx)) xs vars fields fplus af =
  let (Plus bf) = N.plus (N.plus_right af) in
  Permute
    ( N.perm_plus p af bf,
      LazyExt (env, D.zero_plus (CubeOf.dim vars), Ordered.env_entry vars),
      Ordered.vis_fields ctx xs vars fields fplus bf )

let invis (Permute (p, env, ctx)) vars =
  Permute
    (p, LazyExt (env, D.zero_plus (CubeOf.dim vars), Ordered.env_entry vars), Ordered.invis ctx vars)

let lock (Permute (p, env, ctx)) = Permute (p, env, Ordered.lock ctx)
let locked (Permute (_, _, ctx)) = Ordered.locked ctx
let raw_length (Permute (p, _, ctx)) = N.perm_dom (Ordered.raw_length ctx) p
let length (Permute (_, _, ctx)) = Ordered.length ctx
let empty = Permute (N.id_perm N.zero, Emp D.zero, Ordered.empty)
let dbwd (Permute (_, _, ctx)) = Ordered.dbwd ctx
let apps (Permute (_, _, ctx)) = Ordered.apps ctx

(* Lookup is the only place where the permutations are used nontrivially: we apply the permutation to the raw index before looking it up. *)
let lookup (Permute (p, _, ctx)) i = Ordered.lookup ctx (N.perm_apply p (fst i), snd i)
let find_level (Permute (_, _, ctx)) x = Ordered.find_level ctx x

(* To get the environment, we can now just return the precomputed one. *)
let env (Permute (_, env, _)) = env

let ext (Permute (p, env, ctx)) xs ty =
  let ctx, b = Ordered.ext ctx xs ty in
  Permute
    (Insert (p, Top), LazyExt (env, D.zero_plus D.zero, Ordered.env_entry (CubeOf.singleton b)), ctx)

let ext_let (Permute (p, env, ctx)) xs tm =
  let ctx, b = Ordered.ext_let ctx xs tm in
  Permute
    (Insert (p, Top), LazyExt (env, D.zero_plus D.zero, Ordered.env_entry (CubeOf.singleton b)), ctx)

let lam (Permute (_, _, ctx)) tm = Ordered.lam ctx tm

let forget_levels (Permute (p, _, ctx)) forget =
  let ctx = Ordered.forget_levels ctx forget in
  Permute (p, Ordered.env ctx, ctx)

(* Augment an ordered context by the identity permutation *)
let of_ordered ctx = Permute (N.id_perm (Ordered.raw_length ctx), Ordered.env ctx, ctx)
