(* This module should not be opened, but used qualified *)

open Bwd
open Util
open Tlist
open Tbwd
open Dim
open Reporter
open Syntax
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

  (* The constructor and accessors are all that's exported outside this file in ctx.mli. *)
  val make : level option -> normal -> t
  val level : t -> level option
  val value : t -> normal

  (* An unknown binding can be specified when we have its value. *)
  val unknown : unit -> t
  val specify : t -> level option -> normal -> unit

  (* A known but not-yet-available value is created by delaying it, and can be made available by forcing it. *)
  val delay : t -> t
  val force : t -> unit
end = struct
  type state = Known of level option * normal | Unknown | Delayed of level option * normal
  type t = state ref

  let make i x = ref (Known (i, x))

  let level b =
    match !b with
    | Known (i, _) -> i
    | Unknown | Delayed _ -> None

  let value b =
    match !b with
    | Known (_, x) -> x
    | Unknown | Delayed _ -> fatal (Anomaly "Undetermined context variable")

  let unknown () = ref Unknown
  let specify b i x = b := Known (i, x)
  let delay b = ref (Delayed (level b, value b))

  let force b =
    match !b with
    | Known _ | Unknown -> ()
    | Delayed (i, x) -> b := Known (i, x)
end

(* A context is a list of "entries", which have various possibilities depending on the raw visibility. *)
type (_, _) entry =
  (* Add a cube of internal variables that are visible to the parser as a list of cubes of variables, the list-of-cubes being obtained by decomposing the dimension not just as a sum but by an insertion that permutes things.  Note that the division into a cube and non-cube part, and the insertion, are only relevant for looking up *raw* indices: they are invisible to the checked world, whose indices store the total face of mn. *)
  | Vis :
      'm D.t
      * ('m, 'n, 'mn) D.plus
      * ('l, 'n, 'f) count_faces
      * ('n, string option) CubeOf.t
      * ('mn, Binding.t) CubeOf.t
      -> ('f, 'mn) entry
  (* Add a cube of internal variables that are not visible to the parser. *)
  | Invis : ('n, Binding.t) CubeOf.t -> (N.zero, 'n) entry

let raw_entry : type f n. (f, n) entry -> f N.t = function
  | Vis (_, _, f, _, _) -> faces_out f
  | Invis _ -> N.zero

let _dim_entry : type f n. (f, n) entry -> n D.t = function
  | Vis (_, _, _, _, x) | Invis x -> CubeOf.dim x

let app_entry : type f n. (f, n) entry -> app = function
  | Vis (_, _, _, _, b) | Invis b ->
      let n = CubeOf.dim b in
      App (Arg (CubeOf.mmap { map = (fun _ [ x ] -> Binding.value x) } [ b ]), ins_zero n)

module Ordered = struct
  type (_, _) t =
    | Emp : (N.zero, emp) t
    | Snoc : ('a, 'b) t * ('x, 'n) entry * ('a, 'x, 'ax) N.plus -> ('ax, ('b, 'n) snoc) t
    (* A locked context permits no access to the variables behind it. *)
    | Lock : ('a, 'b) t -> ('a, 'b) t

  let vis :
      type a b f af m n mn l.
      (a, b) t ->
      m D.t ->
      (m, n, mn) D.plus ->
      (l, n, f) count_faces ->
      (a, f, af) N.plus ->
      (n, string option) CubeOf.t ->
      (mn, Binding.t) CubeOf.t ->
      (af, (b, mn) snoc) t =
   fun ctx m mn f af xs vars -> Snoc (ctx, Vis (m, mn, f, xs, vars), af)

  let cube_vis :
      type a b n. (a, b) t -> string option -> (n, Binding.t) CubeOf.t -> (a N.suc, (b, n) snoc) t =
   fun ctx x vars ->
    let m = CubeOf.dim vars in
    let (Wrap l) = Endpoints.wrapped () in
    vis ctx m (D.plus_zero m) (faces_zero l) (Suc Zero) (CubeOf.singleton x) vars

  let invis : type a b n. (a, b) t -> (n, Binding.t) CubeOf.t -> (a, (b, n) snoc) t =
   fun ctx vars -> Snoc (ctx, Invis vars, Zero)

  let lock : type a b. (a, b) t -> (a, b) t = fun ctx -> Lock ctx

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

  let rec apps : type a b. (a, b) t -> app Bwd.t = function
    | Emp -> Emp
    | Snoc (ctx, e, _) -> Snoc (apps ctx, app_entry e)
    | Lock ctx -> apps ctx

  (* When we look up a visible variable in a context, we find the level (if any), the value, and the corresponding possibly-invisible variable. *)
  let rec lookup : type a b n. (a, b) t -> a Raw.index -> level option * normal * b index =
   fun ctx k ->
    match ctx with
    | Emp -> (
        match k with
        | _ -> .)
    | Snoc (ctx, Vis (m, mn, af, _, xs), pf) -> lookup_face pf (sfaces af) ctx m mn xs k
    | Snoc (ctx, Invis _, Zero) ->
        let j, x, v = lookup ctx k in
        (j, x, Pop v)
    | Lock _ -> fatal Locked_variable

  and lookup_face :
      type a f af b m n mn.
      (a, f, af) N.plus ->
      (n sface_of, f) Bwv.t ->
      (a, b) t ->
      m D.t ->
      (m, n, mn) D.plus ->
      (mn, Binding.t) CubeOf.t ->
      af Raw.index ->
      level option * normal * (b, mn) snoc index =
   fun pf sf ctx m mn xs k ->
    match (pf, sf) with
    | Zero, Emp ->
        let i, x, v = lookup ctx k in
        (i, x, Pop v)
    | Suc pf, Snoc (sf, SFace_of fb) -> (
        match k with
        | Pop k, fa -> lookup_face pf sf ctx m mn xs (k, fa)
        | Top, None ->
            let fa = id_sface m in
            let (Plus kl) = D.plus (dom_sface fb) in
            let fab = sface_plus_sface fa mn kl fb in
            let x = CubeOf.find xs fab in
            (Binding.level x, Binding.value x, Top fab)
        | Top, Some (Any_sface fa) -> (
            match compare (cod_sface fa) m with
            | Eq ->
                let (Plus kl) = D.plus (dom_sface fb) in
                let fab = sface_plus_sface fa mn kl fb in
                let x = CubeOf.find xs fab in
                (Binding.level x, Binding.value x, Top fab)
            | Neq -> fatal (Invalid_variable_face (D.zero, fa))))

  (* Look up a De Bruijn level in a context and find the corresponding possibly-invisible index, if one exists. *)
  let rec find_level : type a b. (a, b) t -> level -> b index option =
   fun ctx i ->
    match ctx with
    | Emp -> None
    | Snoc (ctx, Vis (_, _, _, _, vars), _) -> find_level_in_cube ctx vars i
    | Snoc (ctx, Invis vars, Zero) -> find_level_in_cube ctx vars i
    | Lock ctx -> find_level ctx i

  and find_level_in_cube :
      type a b n. (a, b) t -> (n, Binding.t) CubeOf.t -> level -> (b, n) snoc index option =
   fun ctx vars i ->
    let open CubeOf.Monadic (Monad.State (struct
      type t = (b, n) snoc index option
    end)) in
    match
      miterM
        {
          it = (fun fa [ x ] s -> if Binding.level x = Some i then ((), Some (Top fa)) else ((), s));
        }
        [ vars ] None
    with
    | (), Some v -> Some v
    | (), None -> Option.map (fun v -> Pop v) (find_level ctx i)

  (* Every context has an underlying environment that substitutes each (level) variable for itself (index).  This environment ALWAYS HAS DIMENSION ZERO, and therefore in particular the variables don't need to come with any boundaries. *)
  let rec env : type a b. (a, b) t -> (D.zero, b) env = function
    | Emp -> Emp D.zero
    | Snoc (ctx, Vis (_, _, _, _, v), _) -> env_entry ctx v
    | Snoc (ctx, Invis v, Zero) -> env_entry ctx v
    | Lock ctx -> env ctx

  and env_entry : type a b n. (a, b) t -> (n, Binding.t) CubeOf.t -> (D.zero, (b, n) snoc) env =
   fun ctx v ->
    Ext
      ( env ctx,
        CubeOf.mmap
          (* We wrap the value in a Lazy because it might be Unknown or Delayed, but we don't want an error reported unless such a value is actually *used*. *)
          { map = (fun _ [ x ] -> CubeOf.singleton (Lazy (lazy (Binding.value x).tm))) }
          [ v ] )

  (* Evaluate a case tree or term in (the environment of) a context.  Thus, replace its De Bruijn indices with De Bruijn levels, and substitute the values of variables with definitions. *)
  let eval : type a b s. (a, b) t -> (b, s) term -> s evaluation =
   fun ctx tm -> Norm.eval (env ctx) tm

  let eval_term : type a b. (a, b) t -> (b, kinetic) term -> kinetic value =
   fun ctx tm -> Norm.eval_term (env ctx) tm

  (* Extend a context by one new variable, without a value but with an assigned type. *)
  let ext : type a b. (a, b) t -> string option -> kinetic value -> (a N.suc, (b, D.zero) snoc) t =
   fun ctx x ty ->
    let n = length ctx in
    cube_vis ctx x (CubeOf.singleton (Binding.make (Some (n, 0)) { tm = var (n, 0) ty; ty }))

  (* Extend a context by one new variable with an assigned value. *)
  let ext_let : type a b. (a, b) t -> string option -> normal -> (a N.suc, (b, D.zero) snoc) t =
   fun ctx x v -> cube_vis ctx x (CubeOf.singleton (Binding.make None v))

  (* Extract all the names in a context. *)
  let rec names : type a b. (a, b) t -> b Names.t = function
    | Emp -> Names.empty
    | Snoc (ctx, Vis (m, mn, _, name, _), _) ->
        snd (Names.add (names ctx) (Variables (m, mn, name)))
    | Snoc (ctx, Invis xs, Zero) -> snd (Names.add_cube (CubeOf.dim xs) (names ctx) None)
    | Lock ctx -> names ctx

  let lookup_name : type a b. (a, b) t -> b index -> string list =
   fun ctx x -> Names.lookup (names ctx) x

  (* Generate a case tree consisting of a sequence of abstractions corresponding to the (checked) variables in a context. *)
  let rec lam : type a b. (a, b) t -> (b, potential) term -> (emp, potential) term =
   fun ctx tree ->
    match ctx with
    | Emp -> tree
    | Snoc (ctx, Vis (m, mn, _, xs, _), _) -> lam ctx (Lam (Variables (m, mn, xs), tree))
    | Snoc (ctx, Invis vars, _) ->
        let n = CubeOf.dim vars in
        lam ctx (Lam (singleton_variables n None, tree))
    | Lock ctx -> lam ctx tree

  (* Ordinary contexts are "backwards" lists.  Following Cockx's thesis, in this file we call the forwards version "telescopes", since they generally are going to get appended to a "real", backwards, context.  A telescope has *three* indices:

     1. A raw length that is a forwards natural number, like the backwards natural numbers that are the raw indices of contexts.
     3. A checked length that is a forwards Tlist of dimensions, like the backwards Tbwd of dimensions that are the checked indices of contexts.
     2. A forwards Tlist of backwards natural numbers that flattens to the raw length.  We could index contexts by an analogous backwards Tbwd of nats, but we don't have any need for that so far.  But retaining this index for telescopes is crucial to constructing the correct permutations in bind_some, below, in an intrinsically well-typed way. *)
  type (_, _, _) tel =
    | Nil : (Fwn.zero, nil, nil) tel
    | Cons :
        ('x, 'n) entry * ('a, 'f, 'b) tel * ('x, 'a, 'xa) Fwn.fplus
        -> ('xa, ('x, 'f) cons, ('n, 'b) cons) tel
    | Lock : ('i, 'f, 'a) tel -> ('i, 'f, 'a) tel

  (* The second index does in fact flatten to the first. *)
  let rec tel_flatten : type i f a. (i, f, a) tel -> (f, i) Tlist.flatten = function
    | Nil -> Flat_nil
    | Cons (_, tel, xa) -> Flat_cons (xa, tel_flatten tel)
    | Lock tel -> tel_flatten tel

  (* Split a (backwards) context into a (backwards) context prefix and a (forwards) telescope suffix, given a way to split the checked indices.  Outputs a corresponding way to split the raw indices.  The opposite way wouldn't make as much sense, since if there were invisible variables at the split point it wouldn't specify which side to put them on. *)
  type (_, _, _) split_tel =
    | Split_tel :
        ('i, 'j, 'ij) Fwn.bplus * ('i, 'b) t * ('j, 'ff, 'c) tel
        -> ('ij, 'b, 'c) split_tel

  let rec split_tel_step :
      type i j ij i b j ff c x.
      (i, j, ij) Fwn.bplus -> (i, (b, x) snoc) t -> (j, ff, c) tel -> (ij, b, (x, c) cons) split_tel
      =
   fun ij_k newctx newtel ->
    match newctx with
    | Snoc (newctx, x, ij) ->
        let (Fplus jk) = Fwn.fplus (N.plus_right ij) in
        let i_jk = Fwn.assocr ij jk ij_k in
        Split_tel (i_jk, newctx, Cons (x, newtel, jk))
    | Lock newctx -> split_tel_step ij_k newctx (Lock newtel)

  let rec split_tel : type ij b c bc. (ij, bc) t -> (b, c, bc) Tbwd.append -> (ij, b, c) split_tel =
   fun ctx b ->
    match b with
    | Append_nil -> Split_tel (Zero, ctx, Nil)
    | Append_cons b ->
        let (Split_tel (ij_k, newctx, newtel)) = split_tel ctx b in
        split_tel_step ij_k newctx newtel

  (* In particular, we can convert an entire context to a telescope.  (This is what we really care about, but to do it we had to strengthen the inductive hypothesis and define all of split_tel.) *)
  type (_, _) to_tel =
    | To_tel :
        (N.zero, 'j, 'i) Fwn.bplus * (emp, 'c, 'b) Tbwd.append * ('j, 'ff, 'c) tel
        -> ('i, 'b) to_tel

  let rec bplus_emp :
      type i j ij ff c. (i, j, ij) Fwn.bplus -> (i, emp) t -> (N.zero, j, ij) Fwn.bplus =
   fun ij ctx ->
    match ctx with
    | Emp -> ij
    | Lock ctx -> bplus_emp ij ctx

  let to_tel : type i b. (i, b) t -> (i, b) to_tel =
   fun ctx ->
    let (To_tlist (_, bc)) = Tbwd.to_tlist (checked_length ctx) in
    let (Split_tel (ij, newctx, tel)) = split_tel ctx bc in
    To_tel (bplus_emp ij newctx, bc, tel)

  (* Now we begin the suite of helper functions for bind_some.  This is an operation that happens during typechecking a pattern match, when the match variable along with all its indices have to be replaced by values determined by the constructor of each branch.  This requires the context to be re-sorted at the same time to maintain a consistent dependency structure, with each type and value depending only on the variables to its left.

     It also requires "substitution into values", which we do by reading back values into the old context and then evaluating them in the new context.  However, readback and evaluation are defined in other files, and readback depends on this file since readback happens *in* a context.  So we define these operations to take a "readback-then-eval" callback function as an argument.  It has to be wrapped up in a record so as to be polymorphic, and we include two different versions of it acting on normals and values.  In addition, these callbacks return an option indicating whether readback succeeded, where failure means that not all the level variables in the input value appear in the readback context.  For normal readback such a failure is a fatal error, but in this case it just means we need to permute some other variables past the present one, so we require the caller to capture that error and return None instead.  Here's the record. *)

  type eval_readback = {
    nf : 'a 'b. oldctx:('a, 'b) t -> newctx:('a, 'b) t -> normal -> normal option;
    ty : 'a 'b. oldctx:('a, 'b) t -> newctx:('a, 'b) t -> kinetic value -> kinetic value option;
  }

  (* We define bind_some and its helper functions in reverse order from the order in which they're called, so that each one can call the already-defined next one in line.  We could put them in the other order by making them mutual, but I prefer to avoid mutuality when it's unnecessary, and also this way each one can be next to the definition of its GADT return type.  But it is probably better to read them in reverse order, starting with bind_some lower down.  The call process goes as follows:

     1. Typechecking during a match calls bind_some, passing it the context and a callback function that picks out the level variables to be re-bound and their associated values (which are in that context).

     2. bind_some shuffles the context entirely to the right into a telescope, and computes the corresponding Tlist of nats and flattened forwards nat (representing the same raw length).  Then it calls go_bind_some with these data and two empty contexts "oldctx" and "newctx".

     3. go_bind_some is passed (in addition to the rebinding callback and flattening data) two contexts of the same (raw and checked) lengths, oldctx and newctx, as well as a telescope.  It and its callees maintain the invariant that oldctx appended by the telescope is a permutation of the old context, containing the *old* level variables and their types, unsubstituted by the rebinding callbar (now no longer in order); while newctx contains the same variables as oldctx, in the same order (which is the new correct order), but now with new level variables and the rebinding substitutions made.  It returns a completed permuted context, along with data recording the resulting permutation and flattening.

     4. go_go_bind_some is passed mostly the same data as go_bind_some, but its job is only to find the *next* variable from the unprocessed telescope to add to oldctx and newctx.  Thus, it recurses through that telescope, trying for each cube of variables to readback all the types and values in oldctx and then evaluate them in newctx.  As soon as it finds one that succeeds, it excises that entry from the telescope and returns both the old entry, the readback-evaluated version, and the telescope with that entry removed (plus information about where it was removed from, which is used to construct the permutations).

     5. Thus, go_bind_some proceeds by calling go_go_bind_some, adding the returned entries to oldctx and newctx, and then calling itself recursively on the remaining telescope.  If the telescope is emptied, we have succeeded and we return.  But if go_go_bind_some fails on all entries of a nonempty telescope, the whole process fails.  (I think this should never happen and indicates a bug; anything the user might do that would cause that should be caught earlier.)

     6. go_go_bind_some acts on each entry with bind_some_entry, whose real work is done by bind_some_normal_cube that acts on a cube of variables with the binder callback and the readback-eval callback.  Since that function is the one we define first, we now proceed to comment its definition directly. *)

  let bind_some_normal_cube :
      type i a n.
      int ->
      (level -> normal option) ->
      eval_readback ->
      oldctx:(i, a) t ->
      newctx:(i, a) t ->
      (n, Binding.t) CubeOf.t ->
      (n, Binding.t) CubeOf.t option =
   fun i binder f ~oldctx ~newctx in_entry ->
    let open Monad.Ops (Monad.Maybe) in
    let open CubeOf.Monadic (Monad.Maybe) in
    (* The tricky thing we have to deal with is that in a *cube* of variables, when doing readback-eval on each variable, we should be allowed to use the *preceeding* variables in the dependency order of the cube, but not the *subsequent* ones.  Unfortunately we don't have a direct way for a context to contain only "some" of a cube of variables.  Thus, we use the ability of Binder.t to be Unknown or Delayed.  *)
    (* We start by creating two variable cubes from the given one.  In "oldentry" all the variables have the same values, but they are delayed so that we can't use them until we've gotten past them in iterating through the cube.  In "newentry" the variables all have unknown values, which we will specify later after eval-readback succeeds step by step. *)
    let [ oldentry; newentry ] =
      CubeOf.pmap
        { map = (fun _ [ b ] -> [ Binding.delay b; Binding.unknown () ]) }
        [ in_entry ] (Cons (Cons Nil)) in
    (* Now we temporarily add both of those entries to the given contexts.  Since we are not using these contexts for typechecking, they might as well be invisible. *)
    let oldctx = Snoc (oldctx, Invis oldentry, Zero) in
    let newctx = Snoc (newctx, Invis newentry, Zero) in
    (* The integer k counts the second component of the new level variables we are creating. *)
    let k = ref 0 in
    let* () =
      miterM
        {
          it =
            (fun _ [ b; oldb; newb ] ->
              let new_level = (i, !k) in
              k := !k + 1;
              match Binding.level b with
              | None ->
                  (* If the variable was let-bound in the original context, we readback-eval its (normal) value, which includes its type. *)
                  let oldnf = Binding.value b in
                  let* newnf = f.nf ~oldctx ~newctx oldnf in
                  (* Now we allow this variable to be used when reading back other variables, and specify the newly evaluated version to be used in the new context. *)
                  Binding.force oldb;
                  Binding.specify newb None newnf;
                  return ()
              | Some old_level -> (
                  (* For variables that were not let-bound in the old context, we first check whether we're newly binding them. *)
                  match binder old_level with
                  | Some oldnf ->
                      (* If so, then the value returned by the binder callback is in the old context, so we readback-eval it and proceed as before. *)
                      let* newnf = f.nf ~oldctx ~newctx oldnf in
                      Binding.force oldb;
                      Binding.specify newb None newnf;
                      return ()
                  | None ->
                      (* Otherwise, we readback-eval only its type, and create a new De Bruijn level for the new context. *)
                      let oldnf = Binding.value b in
                      let oldty = oldnf.ty in
                      let* newty = f.ty ~oldctx ~newctx oldty in
                      let newnf = { tm = var new_level newty; ty = newty } in
                      Binding.force oldb;
                      Binding.specify newb (Some new_level) newnf;
                      return ()));
        }
        [ in_entry; oldentry; newentry ] in
    return newentry

  let bind_some_entry :
      type f i a n.
      int ->
      (level -> normal option) ->
      eval_readback ->
      oldctx:(i, a) t ->
      newctx:(i, a) t ->
      (f, n) entry ->
      (f, n) entry option =
   fun i binder f ~oldctx ~newctx e ->
    let open Monad.Ops (Monad.Maybe) in
    match e with
    | Vis (m, mn, faces, vars, x) ->
        let* x = bind_some_normal_cube i binder f ~oldctx ~newctx x in
        return (Vis (m, mn, faces, vars, x))
    | Invis x ->
        let* x = bind_some_normal_cube i binder f ~oldctx ~newctx x in
        return (Invis x)

  (* This seems an appropriate place to comment about the "insert" and "append_permute" data being returned from (go_)go_bind_some.  The issue is that in addition to a permuted context, we need to compute the permutation relating it to the original context.  In fact we need *two* permutations, one for the raw indices and one for the checked indices.

     The one for the checked indices is more straightforward to compute, because the checked indices are a list of dimensions and we construct the permutation directly working with that list.  Our definition of permutations in terms of iterated insertions closely matches how we construct the permutation, picking out one entry at a time from the remaining ones.  The data structure Tbwd.append_permute is designed to capture the construction of a permutation in this way.

     The one for the raw indices is trickier because it acts as a "block" permutation, with all the raw variables in each Split entry being permuted as a group.  It seems that this permutation should be determined by the permutation of checked indices, but confusingly, that isn't quite true, because the number of raw indices corresponding to a single cube of variables (which is one entry in the checked-index dimension list) depends on what kind of entry it is -- visible, invisible, or split -- which is not recorded in the index *type*.  Our solution is to construct, as we go along, a parallel type list of *natural numbers*, which flattens to the raw index type, and a permutation of it.  Thus go_go_bind some returns *two* 'Tlist.insert's, and go_bind_some returns *two* 'Tbwd.append_permute's, while bind_some flattens and dices them to make a single N.perm and Tbwd.permute. *)

  type (_, _) go_go_bind_some =
    | Found : {
        oldentry : ('f, 'n) entry;
        newentry : ('f, 'n) entry;
        ins : ('b, 'n, 'c) Tlist.insert;
        fins : ('bf, 'f, 'cf) Tlist.insert;
        rest : ('i, 'bf, 'b) tel;
      }
        -> ('c, 'cf) go_go_bind_some
    | Nil : (nil, nil) go_go_bind_some
    | None : ('c, 'cf) go_go_bind_some

  let rec go_go_bind_some :
      type i j a c cf.
      (level -> normal option) ->
      eval_readback ->
      oldctx:(i, a) t ->
      newctx:(i, a) t ->
      (j, cf, c) tel ->
      (c, cf) go_go_bind_some =
   fun binder f ~oldctx ~newctx tel ->
    match tel with
    | Nil -> Nil
    | Cons (entry, rest, _) -> (
        match bind_some_entry (length newctx) binder f ~oldctx ~newctx entry with
        | Some newentry -> Found { ins = Now; fins = Now; oldentry = entry; newentry; rest }
        | None -> (
            match go_go_bind_some binder f ~oldctx ~newctx rest with
            | Found { ins; oldentry; newentry; rest; fins } ->
                let (Fplus newfaces) = Fwn.fplus (raw_entry entry) in
                Found
                  {
                    ins = Later ins;
                    oldentry;
                    newentry;
                    rest = Cons (entry, rest, newfaces);
                    fins = Later fins;
                  }
            | Nil | None -> None))
    | Lock tel -> go_go_bind_some binder f ~oldctx ~newctx tel

  type (_, _, _, _, _, _) go_bind_some =
    | Go_bind_some : {
        raw_flat : ('cf, 'k) Tbwd.flatten;
        raw_perm : ('af, 'bf, 'cf) Tbwd.append_permute;
        checked_perm : ('a, 'b, 'c) Tbwd.append_permute;
        newctx : ('k, 'c) t;
        oldctx : ('k, 'c) t;
      }
        -> ('i, 'j, 'a, 'af, 'b, 'bf) go_bind_some
    | None : ('i, 'j, 'a, 'af, 'b, 'bf) go_bind_some

  let rec go_bind_some :
      type i j a af b bf.
      (level -> normal option) ->
      eval_readback ->
      oldctx:(i, a) t ->
      newctx:(i, a) t ->
      (af, i) Tbwd.flatten ->
      (j, bf, b) tel ->
      (i, j, a, af, b, bf) go_bind_some =
   fun binder f ~oldctx ~newctx af tel ->
    match go_go_bind_some binder f ~oldctx ~newctx tel with
    | Found { ins; fins; oldentry; newentry; rest } -> (
        let (Plus faces) = N.plus (raw_entry oldentry) in
        let oldctx = Snoc (oldctx, oldentry, faces) in
        let newctx = Snoc (newctx, newentry, faces) in
        match go_bind_some binder f ~oldctx ~newctx (Flat_snoc (af, faces)) rest with
        | Go_bind_some { raw_flat; raw_perm; checked_perm; oldctx; newctx } ->
            Go_bind_some
              {
                raw_flat;
                raw_perm = Ap_insert (fins, raw_perm);
                checked_perm = Ap_insert (ins, checked_perm);
                oldctx;
                newctx;
              }
        | None -> None)
    | Nil ->
        Go_bind_some { raw_flat = af; raw_perm = Ap_nil; checked_perm = Ap_nil; oldctx; newctx }
    | None -> None

  type (_, _) bind_some =
    | Bind_some : {
        raw_perm : ('a, 'i) N.perm;
        checked_perm : ('c, 'b) Tbwd.permute;
        oldctx : ('i, 'c) t;
        newctx : ('i, 'c) t;
      }
        -> ('a, 'b) bind_some
    | None : ('a, 'b) bind_some

  let bind_some :
      type a b. (level -> normal option) -> eval_readback -> (a, b) t -> (a, b) bind_some =
   fun binder f ctx ->
    let (To_tel (bplus_raw, checked_append, tel)) = to_tel ctx in
    let telf = tel_flatten tel in
    match go_bind_some binder f ~oldctx:empty ~newctx:empty Flat_emp tel with
    | Go_bind_some { raw_flat; raw_perm; checked_perm; oldctx; newctx } ->
        let (Append raw_append) = Tbwd.append (Tlist.flatten_in telf) in
        let (Bplus_flatten_append (new_flat, bplus_raw')) =
          Tbwd.bplus_flatten_append Flat_emp telf raw_append in
        let Eq = Fwn.bplus_uniq bplus_raw bplus_raw' in
        (* The N.perm_inv here is absolutely essential.  Our choice to index N.perm by a separate domain and codomain, even though in concrete cases the two are always equal, means that if we leave it off, the typechecker complains.  (We could convince the typechecker to let us leave it off by destructing "perm_eq", but that would be stupid.) *)
        let raw_perm =
          N.perm_inv
            (Tbwd.permute_flatten raw_flat new_flat
               (Tbwd.append_append_permute raw_perm raw_append)) in
        let checked_perm = Tbwd.append_append_permute checked_perm checked_append in
        Bind_some { raw_perm; checked_perm; oldctx; newctx }
    | None -> None
end

(* Now we define contexts that add a permutation of the raw indices. *)
type ('a, 'b) t = Permute : ('a, 'i) N.perm * ('i, 'b) Ordered.t -> ('a, 'b) t

(* Nearly all the operations on ordered contexts are lifted to either ignore the permutations or add identities on the right. *)

let vis (Permute (p, ctx)) m mn faces af xs vars =
  let (Plus bf) = N.plus (N.plus_right af) in
  Permute (N.perm_plus p af bf, Ordered.vis ctx m mn faces bf xs vars)

let cube_vis ctx x vars =
  let m = CubeOf.dim vars in
  let (Wrap l) = Endpoints.wrapped () in
  vis ctx m (D.plus_zero m) (faces_zero l) (Suc Zero) (CubeOf.singleton x) vars

let invis (Permute (p, ctx)) vars = Permute (p, Ordered.invis ctx vars)
let lock (Permute (p, ctx)) = Permute (p, Ordered.lock ctx)
let raw_length (Permute (p, ctx)) = N.perm_dom (Ordered.raw_length ctx) p
let length (Permute (_, ctx)) = Ordered.length ctx
let empty = Permute (N.id_perm N.zero, Ordered.empty)
let apps (Permute (_, ctx)) = Ordered.apps ctx

(* Lookup is the only place where the permutations are used nontrivially: we apply the permutation to the raw index before looking it up. *)
let lookup (Permute (p, ctx)) i = Ordered.lookup ctx (N.perm_apply p (fst i), snd i)
let find_level (Permute (_, ctx)) x = Ordered.find_level ctx x
let env (Permute (_, ctx)) = Ordered.env ctx
let eval (Permute (_, ctx)) tm = Ordered.eval ctx tm
let eval_term (Permute (_, ctx)) tm = Ordered.eval_term ctx tm
let ext (Permute (p, ctx)) xs ty = Permute (Insert (p, Top), Ordered.ext ctx xs ty)
let ext_let (Permute (p, ctx)) xs tm = Permute (Insert (p, Top), Ordered.ext_let ctx xs tm)

type eval_readback = {
  nf : 'a 'b. oldctx:('a, 'b) t -> newctx:('a, 'b) t -> normal -> normal option;
  ty : 'a 'b. oldctx:('a, 'b) t -> newctx:('a, 'b) t -> kinetic value -> kinetic value option;
}

(* Note the different return type of this bind_some and of Ordered.bind_some.  The latter returns a new ordered context and two permutations, one for the raw indices and one for the checked indices.  This one incorporates the raw permutation into the permutation stored in the context and returns only the checked permutation to the caller. *)
type (_, _) bind_some =
  | Bind_some : {
      checked_perm : ('c, 'b) Tbwd.permute;
      oldctx : ('a, 'c) t;
      newctx : ('a, 'c) t;
    }
      -> ('a, 'b) bind_some
  | None : ('a, 'b) bind_some

let bind_some (f : eval_readback) g (Permute (p, ctx)) =
  (* Here we have to do some annoying repackaging.  The "eval_readback" provided by the *caller* refers to contexts-with-permutations, whereas the one that Ordered.bind_some wants to receive refers to contexts *without* permutations.  But because those contexts are an *input* of the callback, here we are in the position of promoting an ordered context to one with permutations.  However, since the raw part of a context doesn't matter for readback and eval, we can just make the permutation an identity. *)
  match
    Ordered.bind_some g
      {
        nf =
          (fun ~oldctx ~newctx tm ->
            let p = N.id_perm (Ordered.raw_length oldctx) in
            f.nf ~oldctx:(Permute (p, oldctx)) ~newctx:(Permute (p, newctx)) tm);
        ty =
          (fun ~oldctx ~newctx tm ->
            let p = N.id_perm (Ordered.raw_length oldctx) in
            f.ty ~oldctx:(Permute (p, oldctx)) ~newctx:(Permute (p, newctx)) tm);
      }
      ctx
  with
  | Bind_some { raw_perm; checked_perm; oldctx; newctx } ->
      Bind_some
        {
          checked_perm;
          oldctx = Permute (N.comp_perm p raw_perm, oldctx);
          newctx = Permute (N.comp_perm p raw_perm, newctx);
        }
  | None -> None

let names (Permute (_, ctx)) = Ordered.names ctx
let lookup_name (Permute (_, ctx)) i = Ordered.lookup_name ctx i
let lam (Permute (_, ctx)) tm = Ordered.lam ctx tm
