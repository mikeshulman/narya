open Bwd
open Util
open Tbwd
open Reporter
open Dim
open Syntax
open Term
open Value
open Inst
open Domvars
open Norm
open Printable
module Binding = Ctx.Binding

(* Readback of values to terms.  Closely follows equality-testing in equal.ml, so most comments are omitted.  However, unlike equality-testing and the "readback" in theoretical NbE, this readback does *not* eta-expand functions and tuples.  It is used for (1) displaying terms to the user, who will usually prefer not to see things eta-expanded, and (2) turning values into terms so that we can re-evaluate them in a new environment, for which purpose eta-expansion is irrelevant. *)

let rec readback_nf : type a z. (z, a) Ctx.t -> normal -> (a, kinetic) term =
 fun n x -> readback_at n x.tm x.ty

and readback_at : type a z. (z, a) Ctx.t -> kinetic value -> kinetic value -> (a, kinetic) term =
 fun ctx tm ty ->
  let (Fullinst (uty, tyargs)) = full_inst ty "equal_at" in
  match (uty, tm) with
  | Pi (_, doms, cods), Lam ((Variables (m, mn, xs) as x), body) -> (
      let k = CubeOf.dim doms in
      let l = dim_binder body in
      match (D.compare (TubeOf.inst tyargs) k, D.compare k l) with
      | Neq, _ | _, Neq -> fatal (Dimension_mismatch ("reading back at pi", TubeOf.inst tyargs, k))
      | Eq, Eq ->
          let args, newnfs = dom_vars (Ctx.length ctx) doms in
          let (Plus af) = N.plus (NICubeOf.out N.zero xs) in
          let newctx = Ctx.vis ctx m mn xs newnfs af in
          let output = tyof_app cods tyargs args in
          let body = readback_at newctx (apply_term tm args) output in
          Term.Lam (x, body))
  | Neu { alignment = Lawful (Codata { eta = Eta; fields = _; _ }); _ }, Struct (tmflds, tmins) ->
      let fields =
        Abwd.mapi
          (fun fld (fldtm, l) ->
            match Lazy.force fldtm with
            | Val x -> (readback_at ctx x (tyof_field tm ty fld), l))
          tmflds in
      Act (Struct (Eta, cod_left_ins tmins, fields), perm_of_ins tmins)
  | ( Neu { alignment = Lawful (Data { dim = _; indices = _; missing = Zero; constrs }); _ },
      Constr (xconstr, xn, xargs) ) -> (
      let (Dataconstr { env; args = argtys; indices = _ }) =
        Constr.Map.find_opt xconstr constrs <|> Anomaly "constr not found in readback" in
      match (D.compare xn (TubeOf.inst tyargs), D.compare (TubeOf.inst tyargs) (dim_env env)) with
      | Neq, _ -> fatal (Dimension_mismatch ("reading back constrs", xn, TubeOf.inst tyargs))
      | _, Neq ->
          fatal (Dimension_mismatch ("reading back constrs", TubeOf.inst tyargs, dim_env env))
      | Eq, Eq ->
          let tyarg_args =
            TubeOf.mmap
              {
                map =
                  (fun _ [ tm ] ->
                    match tm.tm with
                    | Constr (tmname, _, tmargs) ->
                        if tmname = xconstr then List.map (fun a -> CubeOf.find_top a) tmargs
                        else fatal (Anomaly "inst arg wrong constr in readback at datatype")
                    | _ -> fatal (Anomaly "inst arg not constr in readback at datatype"));
              }
              [ tyargs ] in
          Constr
            ( xconstr,
              dim_env env,
              readback_at_tel ctx env
                (List.fold_right (fun a args -> CubeOf.find_top a :: args) xargs [])
                argtys
                (TubeOf.mmap { map = (fun _ [ args ] -> args) } [ tyarg_args ]) ))
  | _ -> readback_val ctx tm

and readback_val : type a z. (z, a) Ctx.t -> kinetic value -> (a, kinetic) term =
 fun n x ->
  match x with
  | Lazy (lazy x) -> readback_val n x
  | Uninst (u, _) -> readback_uninst n u
  | Inst { tm; dim = _; args; tys = _ } ->
      let tm = readback_uninst n tm in
      let args = TubeOf.mmap { map = (fun _ [ x ] -> readback_nf n x) } [ args ] in
      Inst (tm, args)
  | Lam _ -> fatal (Anomaly "unexpected lambda in synthesizing readback")
  | Struct _ -> fatal (Anomaly "unexpected struct in synthesizing readback")
  | Constr _ -> fatal (Anomaly "unexpected constr in synthesizing readback")

and readback_uninst : type a z. (z, a) Ctx.t -> uninst -> (a, kinetic) term =
 fun ctx x ->
  match x with
  | UU m -> UU m
  | Pi (x, doms, cods) ->
      let k = CubeOf.dim doms in
      let args, newnfs = dom_vars (Ctx.length ctx) doms in
      Pi
        ( x,
          CubeOf.mmap { map = (fun _ [ dom ] -> readback_val ctx dom) } [ doms ],
          CodCube.build k
            {
              build =
                (fun fa ->
                  let sctx = Ctx.cube_vis ctx x (CubeOf.subcube fa newnfs) in
                  let sargs = CubeOf.subcube fa args in
                  readback_val sctx (apply_binder_term (BindCube.find cods fa) sargs));
            } )
  | Neu { head; args; alignment = _ } ->
      Bwd.fold_left
        (fun fn (Value.App (arg, ins)) ->
          Term.Act
            ( (match arg with
              | Arg args ->
                  App (fn, CubeOf.mmap { map = (fun _ [ tm ] -> readback_nf ctx tm) } [ args ])
              | Field fld -> Field (fn, fld)),
              perm_of_ins ins ))
        (readback_head ctx head) args

and readback_head : type a k z h. (z, a) Ctx.t -> h head -> (a, kinetic) term =
 fun ctx h ->
  match h with
  | Var { level; deg } ->
      let x = Ctx.find_level ctx level <|> No_such_level (PLevel level) in
      Act (Var x, deg)
  | Const { name; ins } ->
      let dim = cod_left_ins ins in
      let perm = deg_of_ins ins (plus_of_ins ins) in
      let (DegExt (_, _, deg)) = comp_deg_extending (deg_zero dim) perm in
      Act (Const name, deg)
  | Meta { meta; env; ins } ->
      let perm = deg_of_ins ins (plus_of_ins ins) in
      let (Data { termctx; _ }) = Galaxy.find_opt meta <|> Undefined_metavariable (PMeta meta) in
      Act (MetaEnv (meta, readback_env ctx env termctx), perm)

and readback_at_tel :
    type n c a b ab z.
    (z, c) Ctx.t ->
    (n, a) env ->
    kinetic value list ->
    (a, b, ab) Telescope.t ->
    (D.zero, n, n, kinetic value list) TubeOf.t ->
    (n, (c, kinetic) term) CubeOf.t list =
 fun ctx env xs tys tyargs ->
  match (xs, tys) with
  | [], Emp -> []
  | x :: xs, Ext (_, ty, tys) ->
      let ety = eval_term env ty in
      (* Copied from check_at_tel; TODO: Factor it out *)
      let tyargtbl = Hashtbl.create 10 in
      let [ tyarg; tms; tyargs ] =
        TubeOf.pmap
          {
            map =
              (fun fa [ tyargs ] ->
                match tyargs with
                | [] -> fatal (Anomaly "missing arguments in readback_at_tel")
                | argtm :: argrest ->
                    let fa = sface_of_tface fa in
                    let argty =
                      inst
                        (eval_term (Act (env, op_of_sface fa)) ty)
                        (TubeOf.build D.zero
                           (D.zero_plus (dom_sface fa))
                           {
                             build =
                               (fun fb ->
                                 Hashtbl.find tyargtbl
                                   (SFace_of (comp_sface fa (sface_of_tface fb))));
                           }) in
                    let argnorm = { tm = argtm; ty = argty } in
                    let argtm = readback_at ctx argtm argty in
                    Hashtbl.add tyargtbl (SFace_of fa) argnorm;
                    [ argnorm; argtm; argrest ]);
          }
          [ tyargs ] (Cons (Cons (Cons Nil))) in
      let ity = inst ety tyarg in
      TubeOf.plus_cube tms (CubeOf.singleton (readback_at ctx x ity))
      :: readback_at_tel ctx
           (Ext
              ( env,
                CubeOf.singleton (TubeOf.plus_cube (val_of_norm_tube tyarg) (CubeOf.singleton x)) ))
           xs tys tyargs
  | _ -> fatal (Anomaly "length mismatch in equal_at_tel")

and readback_env :
    type n a b c d. (a, b) Ctx.t -> (n, d) Value.env -> (c, d) Termctx.t -> (b, n, d) Term.env =
 fun ctx env (Permute (_, envctx)) -> readback_ordered_env ctx env envctx

and readback_ordered_env :
    type n a b c d.
    (a, b) Ctx.t -> (n, d) Value.env -> (c, d) Termctx.Ordered.t -> (b, n, d) Term.env =
 fun ctx env envctx ->
  match envctx with
  | Emp ->
      let (Emp n) = Permute.env_top env in
      Emp n
  | Lock envctx -> readback_ordered_env ctx env envctx
  | Snoc (envctx, entry, _) -> (
      let (Ext (env', xss)) = Permute.env_top env in
      let tmenv = readback_ordered_env ctx env' envctx in
      match entry with
      | Vis { bindings; _ } | Invis bindings ->
          let tmxss =
            CubeOf.mmap
              {
                map =
                  (fun fa [ xs ] ->
                    let ty = (CubeOf.find bindings fa).ty in
                    let xtytbl = Hashtbl.create 10 in
                    CubeOf.mmap
                      {
                        map =
                          (fun fb [ tm ] ->
                            let k = dom_sface fb in
                            let ty =
                              inst
                                (eval_term (Act (env, op_of_sface fb)) ty)
                                (TubeOf.build k (D.plus_zero k)
                                   {
                                     build =
                                       (fun fc ->
                                         Hashtbl.find xtytbl
                                           (SFace_of (comp_sface fb (sface_of_tface fc))));
                                   }) in
                            Hashtbl.add xtytbl (SFace_of fb) { tm; ty };
                            readback_at ctx tm ty);
                      }
                      [ xs ]);
              }
              [ xss ] in
          Ext (tmenv, tmxss))

let readback_bindings :
    type a b n.
    (a, (b, n) snoc) Ctx.t -> (n, Binding.t) CubeOf.t -> (n, (b, n) snoc Termctx.binding) CubeOf.t =
 fun ctx vbs ->
  CubeOf.mmap
    {
      map =
        (fun _ [ b ] ->
          match Binding.level b with
          | Some _ ->
              ({ tm = None; ty = readback_val ctx (Binding.value b).ty }
                : (b, n) snoc Termctx.binding)
          | None ->
              {
                tm = Some (readback_nf ctx (Binding.value b));
                ty = readback_val ctx (Binding.value b).ty;
              });
    }
    [ vbs ]

let readback_entry :
    type a b f n. (a, (b, n) snoc) Ctx.t -> (f, n) Ctx.entry -> (b, f, n) Termctx.entry =
 fun ctx e ->
  match e with
  | Vis { dim; plusdim; vars; bindings; hasfields; fields; fplus } ->
      let top = Binding.value (CubeOf.find_top bindings) in
      let fields =
        Bwv.map
          (fun (f, x) ->
            let fldty = readback_val ctx (tyof_field top.tm top.ty f) in
            (f, x, fldty))
          fields in
      let bindings = readback_bindings ctx bindings in
      Vis { dim; plusdim; vars; bindings; hasfields; fields; fplus }
  | Invis bindings -> Invis (readback_bindings ctx bindings)

let rec readback_ordered_ctx : type a b. (a, b) Ctx.Ordered.t -> (a, b) Termctx.Ordered.t = function
  | Emp -> Emp
  | Snoc (rest, e, af) as ctx ->
      Snoc (readback_ordered_ctx rest, readback_entry (Ctx.of_ordered ctx) e, af)
  | Lock ctx -> Lock (readback_ordered_ctx ctx)

let readback_ctx : type a b. (a, b) Ctx.t -> (a, b) Termctx.t = function
  | Permute (p, ctx) -> Permute (p, readback_ordered_ctx ctx)
