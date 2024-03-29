open Bwd
open Util
open Reporter
open Dim
open Syntax
open Term
open Value
open Inst
open Domvars
open Norm
open Printable

(* Readback of values to terms.  Closely follows equality-testing in equal.ml, so most comments are omitted.  However, unlike equality-testing and the "readback" in theoretical NbE, this readback does *not* eta-expand functions and tuples.  It is used for (1) displaying terms to the user, who will usually prefer not to see things eta-expanded, and (2) turning values into terms so that we can re-evaluate them in a new environment, for which purpose eta-expansion is irrelevant. *)

let rec readback_nf : type a z. (z, a) Ctx.t -> normal -> (a, kinetic) term =
 fun n x -> readback_at n x.tm x.ty

and readback_at : type a z. (z, a) Ctx.t -> kinetic value -> kinetic value -> (a, kinetic) term =
 fun ctx tm ty ->
  let (Fullinst (uty, tyargs)) = full_inst ty "equal_at" in
  match (uty, tm) with
  | Pi (_, doms, cods), Lam (x, body) -> (
      let k = CubeOf.dim doms in
      let l = dim_binder body in
      match (compare (TubeOf.inst tyargs) k, compare k l) with
      | Neq, _ | _, Neq -> fatal (Dimension_mismatch ("reading back at pi", TubeOf.inst tyargs, k))
      | Eq, Eq -> (
          let args, newnfs = dom_vars (Ctx.length ctx) doms in
          match x with
          | `Cube x ->
              let newctx = Ctx.vis ctx x newnfs in
              let output = tyof_app cods tyargs args in
              let body = readback_at newctx (apply_term tm args) output in
              Term.Lam (k, `Cube x, body)
          | `Normal x ->
              let (Faces dom_faces) = count_faces k in
              let f = faces_out dom_faces in
              let (Plus af) = N.plus f in
              let newctx = Ctx.split ctx dom_faces af x newnfs in
              let output = tyof_app cods tyargs args in
              let body = readback_at newctx (apply_term tm args) output in
              Term.Lam (k, `Normal x, body)))
  | Neu { alignment = Lawful (Codata { eta = Eta; fields = _; _ }); _ }, Struct (tmflds, tmins) ->
      let fields =
        Abwd.mapi
          (fun fld (fldtm, l) ->
            match Lazy.force fldtm with
            | Val x -> (readback_at ctx x (tyof_field tm ty fld), l))
          tmflds in
      Act (Struct (Eta, fields), perm_of_ins tmins)
  | ( Neu { alignment = Lawful (Data { dim = _; indices = _; missing = Zero; constrs }); _ },
      Constr (xconstr, xn, xargs) ) -> (
      let (Dataconstr { env; args = argtys; indices = _ }) =
        match Constr.Map.find_opt xconstr constrs with
        | Some x -> x
        | None -> fatal (Anomaly "constr not found in readback") in
      match (compare xn (TubeOf.inst tyargs), compare (TubeOf.inst tyargs) (dim_env env)) with
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
                        if tmname = xconstr then Bwd.map (fun a -> CubeOf.find_top a) tmargs
                        else fatal (Anomaly "inst arg wrong constr in readback at datatype")
                    | _ -> fatal (Anomaly "inst arg not constr in readback at datatype"));
              }
              [ tyargs ] in
          Constr
            ( xconstr,
              dim_env env,
              Bwd.of_list
                (readback_at_tel ctx env
                   (Bwd.fold_right (fun a args -> CubeOf.find_top a :: args) xargs [])
                   argtys
                   (TubeOf.mmap { map = (fun _ [ args ] -> Bwd.to_list args) } [ tyarg_args ])) ))
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
                  let sctx = Ctx.vis ctx x (CubeOf.subcube fa newnfs) in
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
  | Var { level; deg } -> (
      match Ctx.find_level ctx level with
      | Some x -> Act (Var x, deg)
      | None -> fatal (No_such_level (PLevel level)))
  | Const { name; ins } ->
      let dim = cod_left_ins ins in
      let perm = deg_of_ins ins (plus_of_ins ins) in
      let (DegExt (_, _, deg)) = comp_deg_extending (deg_zero dim) perm in
      Act (Const name, deg)

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
      (* Copied from check_tel; TODO: Factor it out *)
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
