open Util
open Tbwd
open Tlist
open Dim
open Reporter
open Value
open Norm
open Readback
module Binding = Ctx.Binding

module Ordered = struct
  open Ctx.Ordered

  (* Ordinary contexts are "backwards" lists.  Following Cockx's thesis, in this file we call the forwards version "telescopes", since they generally are going to get appended to a "real", backwards, context.  A telescope has *three* indices:

     1. A raw length that is a forwards natural number, like the backwards natural numbers that are the raw indices of contexts.
     3. A checked length that is a forwards Tlist of dimensions, like the backwards Tbwd of dimensions that are the checked indices of contexts.
     2. A forwards Tlist of backwards natural numbers that flattens to the raw length.  We could index contexts by an analogous backwards Tbwd of nats, but we don't have any need for that so far.  But retaining this index for telescopes is crucial to constructing the correct permutations in bind_some, below, in an intrinsically well-typed way. *)
  type (_, _, _) tel =
    | Nil : (Fwn.zero, nil, nil) tel
    | Cons :
        ('x, 'n) Ctx.entry * ('a, 'f, 'b) tel * ('x, 'a, 'xa) Fwn.fplus
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
        ('i, 'j, 'ij) Fwn.bplus * ('i, 'b) Ctx.Ordered.t * ('j, 'ff, 'c) tel
        -> ('ij, 'b, 'c) split_tel

  let rec split_tel_step : type i j ij b ff c x.
      (i, j, ij) Fwn.bplus ->
      (i, (b, x) snoc) Ctx.Ordered.t ->
      (j, ff, c) tel ->
      (ij, b, (x, c) cons) split_tel =
   fun ij_k newctx newtel ->
    match newctx with
    | Snoc (newctx, x, ij) ->
        let (Fplus jk) = Fwn.fplus (N.plus_right ij) in
        let i_jk = Fwn.bfplus_assocr ij jk ij_k in
        Split_tel (i_jk, newctx, Cons (x, newtel, jk))
    | Lock newctx -> split_tel_step ij_k newctx (Lock newtel)

  let rec split_tel : type ij b c bc.
      (ij, bc) Ctx.Ordered.t -> (b, c, bc) Tbwd.append -> (ij, b, c) split_tel =
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

  let rec bplus_emp : type i j ij.
      (i, j, ij) Fwn.bplus -> (i, emp) Ctx.Ordered.t -> (N.zero, j, ij) Fwn.bplus =
   fun ij ctx ->
    match ctx with
    | Emp -> ij
    | Lock ctx -> bplus_emp ij ctx

  let to_tel : type i b. (i, b) Ctx.Ordered.t -> (i, b) to_tel =
   fun ctx ->
    let (To_tlist (_, bc)) = Tbwd.to_tlist (checked_length ctx) in
    let (Split_tel (ij, newctx, tel)) = split_tel ctx bc in
    To_tel (bplus_emp ij newctx, bc, tel)

  (* Now we begin the suite of helper functions for bind_some.  This is an operation that happens during typechecking a pattern match, when the match variable along with all its indices have to be replaced by values determined by the constructor of each branch.  This requires the context to be re-sorted at the same time to maintain a consistent dependency structure, with each type and value depending only on the variables to its left.  It also requires "substitution into values", which we do by reading back values into the old context and then evaluating them in the new context. *)

  let eval_readback_nf : type a b.
      oldctx:(a, b) Ctx.Ordered.t -> newctx:(a, b) Ctx.Ordered.t -> normal -> normal option =
   fun ~oldctx ~newctx nf ->
    Reporter.try_with ~fatal:(fun d ->
        match d.message with
        | No_such_level _ -> None
        | _ -> fatal_diagnostic d)
    @@ fun () ->
    Some
      {
        tm = eval_term (Ctx.Ordered.env newctx) (readback_nf (Ctx.of_ordered oldctx) nf);
        ty = eval_term (Ctx.Ordered.env newctx) (readback_val (Ctx.of_ordered oldctx) nf.ty);
      }

  let eval_readback_val : type a b.
      oldctx:(a, b) Ctx.Ordered.t ->
      newctx:(a, b) Ctx.Ordered.t ->
      kinetic value ->
      kinetic value option =
   fun ~oldctx ~newctx ty ->
    Reporter.try_with ~fatal:(fun d ->
        match d.message with
        | No_such_level _ -> None
        | _ -> fatal_diagnostic d)
    @@ fun () -> Some (eval_term (Ctx.Ordered.env newctx) (readback_val (Ctx.of_ordered oldctx) ty))

  (* We define bind_some and its helper functions in reverse order from the order in which they're called, so that each one can call the already-defined next one in line.  We could put them in the other order by making them mutual, but I prefer to avoid mutuality when it's unnecessary, and also this way each one can be next to the definition of its GADT return type.  But it is probably better to read them in reverse order, starting with bind_some lower down.  The call process goes as follows:

     1. Typechecking during a match calls bind_some, passing it the context and a callback function that picks out the level variables to be re-bound and their associated values (which are in that context).

     2. bind_some shuffles the context entirely to the right into a telescope, and computes the corresponding Tlist of nats and flattened forwards nat (representing the same raw length).  Then it calls go_bind_some with these data and two empty contexts "oldctx" and "newctx".

     3. go_bind_some is passed (in addition to the rebinding callback and flattening data) two contexts of the same (raw and checked) lengths, oldctx and newctx, as well as a telescope.  It and its callees maintain the invariant that oldctx appended by the telescope is a permutation of the old context, containing the *old* level variables and their types, unsubstituted by the rebinding callbar (now no longer in order); while newctx contains the same variables as oldctx, in the same order (which is the new correct order), but now with new level variables and the rebinding substitutions made.  It returns a completed permuted context, along with data recording the resulting permutation and flattening.

     4. go_go_bind_some is passed mostly the same data as go_bind_some, but its job is only to find the *next* variable from the unprocessed telescope to add to oldctx and newctx.  Thus, it recurses through that telescope, trying for each cube of variables to readback all the types and values in oldctx and then evaluate them in newctx.  As soon as it finds one that succeeds, it excises that entry from the telescope and returns both the old entry, the readback-evaluated version, and the telescope with that entry removed (plus information about where it was removed from, which is used to construct the permutations).

     5. Thus, go_bind_some proceeds by calling go_go_bind_some, adding the returned entries to oldctx and newctx, and then calling itself recursively on the remaining telescope.  If the telescope is emptied, we have succeeded and we return.  But if go_go_bind_some fails on all entries of a nonempty telescope, the whole process fails.  (I think this should never happen and indicates a bug; anything the user might do that would cause that should be caught earlier.)

     6. go_go_bind_some acts on each entry with bind_some_entry, whose real work is done by bind_some_normal_cube that acts on a cube of variables with the binder callback and readback-eval.  Since that function is the one we define first, we now proceed to comment its definition directly. *)

  let bind_some_normal_cube : type i a n.
      int ->
      (level -> normal option) ->
      [ `Bindable | `Nonbindable ] ->
      oldctx:(i, a) Ctx.Ordered.t ->
      newctx:(i, a) Ctx.Ordered.t ->
      (n, Binding.t) CubeOf.t ->
      (n, Binding.t) CubeOf.t option =
   fun i binder bindable ~oldctx ~newctx in_entry ->
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
            (fun fa [ b; oldb; newb ] ->
              let new_level = (i, !k) in
              k := !k + 1;
              match Binding.level b with
              | None ->
                  (* If the variable was let-bound in the original context, we readback-eval its (normal) value, which includes its type. *)
                  let oldnf = Binding.value b in
                  let* newnf = eval_readback_nf ~oldctx ~newctx oldnf in
                  (* Now we allow this variable to be used when reading back other variables, and specify the newly evaluated version to be used in the new context. *)
                  Binding.force oldb;
                  Binding.specify newb None newnf;
                  return ()
              | Some old_level -> (
                  (* For variables that were not let-bound in the old context, we first check whether we're newly binding them. *)
                  match binder old_level with
                  (* `Nonbindable means only that the *top* variable is nonbindable. *)
                  | Some oldnf when bindable = `Bindable || Option.is_none (is_id_sface fa) ->
                      (* If so, then the value returned by the binder callback is in the old context, so we readback-eval it and proceed as before. *)
                      let* newnf = eval_readback_nf ~oldctx ~newctx oldnf in
                      Binding.force oldb;
                      Binding.specify newb None newnf;
                      return ()
                  | None ->
                      (* Otherwise, we readback-eval only its type, and create a new De Bruijn level for the new context. *)
                      let oldnf = Binding.value b in
                      let oldty = oldnf.ty in
                      let* newty = eval_readback_val ~oldctx ~newctx oldty in
                      let newnf = { tm = var new_level newty; ty = newty } in
                      Binding.force oldb;
                      Binding.specify newb (Some new_level) newnf;
                      return ()
                  | _ -> fatal (Anomaly "attempt to bind variable with field views")));
        }
        [ in_entry; oldentry; newentry ] in
    return newentry

  let bind_some_entry : type f i a n.
      int ->
      (level -> normal option) ->
      oldctx:(i, a) Ctx.Ordered.t ->
      newctx:(i, a) Ctx.Ordered.t ->
      (f, n) Ctx.entry ->
      (f, n) Ctx.entry option =
   fun i binder ~oldctx ~newctx e ->
    let open Monad.Ops (Monad.Maybe) in
    match e with
    | Vis ({ bindings; fplus = Zero; _ } as v) ->
        let* bindings = bind_some_normal_cube i binder `Bindable ~oldctx ~newctx bindings in
        return (Ctx.Vis { v with bindings })
    | Invis bindings ->
        let* bindings = bind_some_normal_cube i binder `Bindable ~oldctx ~newctx bindings in
        return (Ctx.Invis bindings)
    | Vis ({ bindings; _ } as v) ->
        (* A variable that has views of its fields can't be bound. *)
        let* bindings = bind_some_normal_cube i binder `Nonbindable ~oldctx ~newctx bindings in
        return (Ctx.Vis { v with bindings })

  (* This seems an appropriate place to comment about the "insert" and "append_permute" data being returned from (go_)go_bind_some.  The issue is that in addition to a permuted context, we need to compute the permutation relating it to the original context.  In fact we need *two* permutations, one for the raw indices and one for the checked indices.

     The one for the checked indices is more straightforward to compute, because the checked indices are a list of dimensions and we construct the permutation directly working with that list.  Our definition of permutations in terms of iterated insertions closely matches how we construct the permutation, picking out one entry at a time from the remaining ones.  The data structure Tbwd.append_permute is designed to capture the construction of a permutation in this way.

     The one for the raw indices is trickier because it acts as a "block" permutation, with all the raw variables in each Split entry being permuted as a group.  It seems that this permutation should be determined by the permutation of checked indices, but confusingly, that isn't quite true, because the number of raw indices corresponding to a single cube of variables (which is one entry in the checked-index dimension list) depends on what kind of entry it is -- visible, invisible, or split -- which is not recorded in the index *type*.  Our solution is to construct, as we go along, a parallel type list of *natural numbers*, which flattens to the raw index type, and a permutation of it.  Thus go_go_bind some returns *two* 'Tlist.insert's, and go_bind_some returns *two* 'Tbwd.append_permute's, while bind_some flattens and dices them to make a single N.perm and Tbwd.permute. *)

  type (_, _) go_go_bind_some =
    | Found : {
        oldentry : ('f, 'n) Ctx.entry;
        newentry : ('f, 'n) Ctx.entry;
        ins : ('b, 'n, 'c) Tlist.insert;
        fins : ('bf, 'f, 'cf) Tlist.insert;
        rest : ('i, 'bf, 'b) tel;
      }
        -> ('c, 'cf) go_go_bind_some
    | Nil : (nil, nil) go_go_bind_some
    | None : ('c, 'cf) go_go_bind_some

  let rec go_go_bind_some : type i j a c cf.
      (level -> normal option) ->
      oldctx:(i, a) Ctx.Ordered.t ->
      newctx:(i, a) Ctx.Ordered.t ->
      (j, cf, c) tel ->
      (c, cf) go_go_bind_some =
   fun binder ~oldctx ~newctx tel ->
    match tel with
    | Nil -> Nil
    | Cons (entry, rest, _) -> (
        match bind_some_entry (length newctx) binder ~oldctx ~newctx entry with
        | Some newentry -> Found { ins = Now; fins = Now; oldentry = entry; newentry; rest }
        | None -> (
            match go_go_bind_some binder ~oldctx ~newctx rest with
            | Found { ins; oldentry; newentry; rest; fins } ->
                let (Fplus newfaces) = Fwn.fplus (Ctx.raw_entry entry) in
                Found
                  {
                    ins = Later ins;
                    oldentry;
                    newentry;
                    rest = Cons (entry, rest, newfaces);
                    fins = Later fins;
                  }
            | Nil | None -> None))
    | Lock tel -> go_go_bind_some binder ~oldctx ~newctx tel

  type (_, _, _, _, _, _) go_bind_some =
    | Go_bind_some : {
        raw_flat : ('cf, 'k) Tbwd.flatten;
        raw_perm : ('af, 'bf, 'cf) Tbwd.append_permute;
        checked_perm : ('a, 'b, 'c) Tbwd.append_permute;
        newctx : ('k, 'c) Ctx.Ordered.t;
        oldctx : ('k, 'c) Ctx.Ordered.t;
      }
        -> ('i, 'j, 'a, 'af, 'b, 'bf) go_bind_some
    | None : ('i, 'j, 'a, 'af, 'b, 'bf) go_bind_some

  let rec go_bind_some : type i j a af b bf.
      (level -> normal option) ->
      oldctx:(i, a) Ctx.Ordered.t ->
      newctx:(i, a) Ctx.Ordered.t ->
      (af, i) Tbwd.flatten ->
      (j, bf, b) tel ->
      (i, j, a, af, b, bf) go_bind_some =
   fun binder ~oldctx ~newctx af tel ->
    match go_go_bind_some binder ~oldctx ~newctx tel with
    | Found { ins; fins; oldentry; newentry; rest } -> (
        let (Plus faces) = N.plus (Ctx.raw_entry oldentry) in
        let oldctx = Snoc (oldctx, oldentry, faces) in
        let newctx = Snoc (newctx, newentry, faces) in
        match go_bind_some binder ~oldctx ~newctx (Flat_snoc (af, faces)) rest with
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
        oldctx : ('i, 'c) Ctx.Ordered.t;
        newctx : ('i, 'c) Ctx.Ordered.t;
      }
        -> ('a, 'b) bind_some
    | None : ('a, 'b) bind_some

  let bind_some : type a b. (level -> normal option) -> (a, b) Ctx.Ordered.t -> (a, b) bind_some =
   fun binder ctx ->
    let (To_tel (bplus_raw, checked_append, tel)) = to_tel ctx in
    let telf = tel_flatten tel in
    match go_bind_some binder ~oldctx:empty ~newctx:empty Flat_emp tel with
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

(* Note the different return type of this bind_some and of Ordered.bind_some.  The latter returns a new ordered context and two permutations, one for the raw indices and one for the checked indices.  This one incorporates the raw permutation into the permutation stored in the context and returns only the checked permutation to the caller. *)
type (_, _) bind_some =
  | Bind_some : {
      checked_perm : ('c, 'b) Tbwd.permute;
      oldctx : ('a, 'c) Ctx.t;
      newctx : ('a, 'c) Ctx.t;
    }
      -> ('a, 'b) bind_some
  | None : ('a, 'b) bind_some

let bind_some g (Ctx.Permute (p, _, ctx)) =
  match Ordered.bind_some g ctx with
  | Bind_some { raw_perm; checked_perm; oldctx; newctx } ->
      Bind_some
        {
          checked_perm;
          oldctx = Permute (N.comp_perm p raw_perm, Ctx.Ordered.env oldctx, oldctx);
          newctx = Permute (N.comp_perm p raw_perm, Ctx.Ordered.env newctx, newctx);
        }
  | None -> None
