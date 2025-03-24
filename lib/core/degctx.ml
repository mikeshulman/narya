open Util
open Tbwd
open Dim
open Reporter
open Value
open Readback
open Norm

(* Degenerating contexts (for higher inductive and coinductive types).  The degeneracy of a context by a dimension k is a context in which all the n-cubes of variables have been replaced by (k+n)-cubes, whose types are degenerate versions of those in the original context.  Thus, while its raw length is the same, its checked length has k added to all the dimensions.  There is a canonical k-dimensional substitution (environment) from the degenerated context to the original one, which is the universal such substitution exhibiting the degenerated context as a power/cotensor in the dimension-enriched category of contexts.  (The universal property of this power/cotensor is implemented by the Shift operation on environments/substitutions.)

   You might naively think that we could build the degenerated context by iterating through the original one and applying "act" to all the types.  However, the degenerated context has *more level variables* than the original context does, and we need to create these variables and ensure that they appear in all the later types as needed.  Thus, it seems that we really do have to do an eval-readback cycle. *)

module Ordered = struct
  open Ctx.Ordered

  let degenerate_binding : type k n kn ax b.
      int ->
      k D.t ->
      (k, n, kn) D.plus ->
      (n, Binding.t) CubeOf.t ->
      (* Because the values and types of variables in one cube can refer to other variables in the same cube, we need to be given the extended context with this binding included at the end in order to readback. *)
      (ax, (b, n) snoc) t ->
      (* But we are building the degenerating environment as we go, so we don't have the extended version of that yet. *)
      (k, b) env ->
      (kn, Binding.t) CubeOf.t * (kn, kinetic value) CubeOf.t =
   fun i k k_n xs ctx env ->
    let kn = D.plus_out k k_n in
    let ctx = Ctx.of_ordered ctx in
    let readbacks =
      CubeOf.mmap
        {
          map =
            (fun _ [ x ] ->
              let nf = Binding.value x in
              match Binding.level x with
              | None -> (Some (readback_nf ctx nf), readback_val ctx nf.ty)
              | Some _ -> (None, readback_val ctx nf.ty));
        }
        [ xs ] in
    let j = ref 0 in
    let xstbl = Hashtbl.create 20 in
    let newxs =
      CubeOf.build kn
        {
          build =
            (fun fab ->
              (* At each step we need to re-build a partially extended environment containing the values for smaller faces that we have already evaluated, in order to evaluate the term for this face. *)
              let prev_vals =
                CubeOf.build kn
                  {
                    build =
                      (fun fab' ->
                        match Hashtbl.find_opt xstbl (SFace_of fab') with
                        | Some x -> ready (Val x.tm)
                        | None ->
                            defer (fun () ->
                                fatal (Anomaly "variable out of scope in degenerate_binding")));
                  } in
              let env = LazyExt (env, k_n, prev_vals) in
              let (SFace_of_plus (_, fa, fb)) = sface_of_plus k_n fab in
              let m = dom_sface fb in
              match CubeOf.find readbacks fb with
              | None, ty ->
                  let level = (i, !j) in
                  j := !j + 1;
                  let ty = Norm.eval_term (Act (env, op_of_sface fa)) ty in
                  let ty =
                    inst ty
                      (TubeOf.build D.zero
                         (D.zero_plus (dom_sface fa))
                         {
                           build =
                             (fun fc ->
                               let (Plus l_m) = D.plus m in
                               Hashtbl.find xstbl
                                 (SFace_of
                                    (sface_plus_sface
                                       (comp_sface fa (sface_of_tface fc))
                                       k_n l_m fb)));
                         }) in
                  let v = { tm = var level ty; ty } in
                  Hashtbl.add xstbl (SFace_of fab) v;
                  Binding.make (Some level) v
              | Some tm, ty ->
                  (* Incrementing the level isn't really necessary since we aren't going to use it in this case, but we do it anyway for consistency. *)
                  j := !j + 1;
                  let tm = Norm.eval_term (Act (env, op_of_sface fa)) tm in
                  let ty = Norm.eval_term (Act (env, op_of_sface fa)) ty in
                  let ty =
                    inst ty
                      (TubeOf.build D.zero
                         (D.zero_plus (dom_sface fa))
                         {
                           build =
                             (fun fc ->
                               let (Plus l_m) = D.plus m in
                               Hashtbl.find xstbl
                                 (SFace_of
                                    (sface_plus_sface
                                       (comp_sface fa (sface_of_tface fc))
                                       k_n l_m fb)));
                         }) in
                  let v = { tm; ty } in
                  Hashtbl.add xstbl (SFace_of fab) v;
                  Binding.make None v);
        } in
    let newvals = CubeOf.mmap { map = (fun _ [ v ] -> (Binding.value v).tm) } [ newxs ] in
    (newxs, newvals)

  type (_, _, _) degctx =
    | Degctx : ('k, 'b, 'kb) Plusmap.t * ('a, 'kb) t * ('k, 'b) env -> ('a, 'b, 'k) degctx

  (* TODO: Short-circuit if k=0. *)
  let rec degenerate : type a b k. (a, b) t -> k D.t -> (a, b, k) degctx =
   fun ctx k ->
    match ctx with
    | Emp -> Degctx (Map_emp, Emp, Emp k)
    | Snoc (ctx', entry, ax) ->
        let (Degctx (kb, newctx', env)) = degenerate ctx' k in
        let mn = Ctx.dim_entry entry in
        let (Plus k_mn) = D.plus mn in
        let newentry, newenv =
          match entry with
          | Vis { hasfields = Has_fields; _ } ->
              fatal (Anomaly "attempt to degenerate a context containing illusory variables")
          | Vis { dim; plusdim; vars; bindings; hasfields = No_fields; fields; fplus } ->
              let (Plus km) = D.plus dim in
              let plusdim = D.plus_assocl km plusdim k_mn in
              let bindings, newval = degenerate_binding (length newctx') k k_mn bindings ctx env in
              let hasfields = Term.No_fields in
              ( Ctx.Vis { dim = D.plus_out k km; plusdim; vars; bindings; hasfields; fields; fplus },
                Ext (env, k_mn, Ok newval) )
          | Invis xs ->
              let newxs, newval = degenerate_binding (length newctx') k k_mn xs ctx env in
              (Invis newxs, Ext (env, k_mn, Ok newval)) in
        Degctx (Map_snoc (kb, k_mn), Snoc (newctx', newentry, ax), newenv)
    | Lock ctx ->
        let (Degctx (kb, newctx, env)) = degenerate ctx k in
        Degctx (kb, Lock newctx, env)
end

type (_, _, _) degctx =
  | Degctx : ('k, 'b, 'kb) Plusmap.t * ('a, 'kb) Ctx.t * ('k, 'b) env -> ('a, 'b, 'k) degctx

let degctx : type a b k. (a, b) Ctx.t -> k D.t -> (a, b, k) degctx =
 fun (Permute (p, _, ctx)) k ->
  let (Degctx (kb, newctx, env)) = Ordered.degenerate ctx k in
  Degctx (kb, Permute (p, Ctx.Ordered.env newctx, newctx), env)
