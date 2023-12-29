open Bwd
open Util
open Reporter
open Dim
open Term
open Value
open Inst
open Norm

(* Eta-expanding readback of values to terms.  Closely follows eta-expanding equality-testing in equal.ml, so most comments are omitted. *)

let rec readback_nf : type a z. (z, a) Ctx.t -> normal -> a term =
 fun n x -> readback_at n x.tm x.ty

and readback_at : type a z. (z, a) Ctx.t -> value -> value -> a term =
 fun ctx tm ty ->
  let (Fullinst (uty, tyargs)) = full_inst ty "equal_at" in
  match uty with
  | Pi (x, doms, cods) -> (
      let k = CubeOf.dim doms in
      match compare (TubeOf.inst tyargs) k with
      | Neq -> fatal (Dimension_mismatch ("reading back pi", TubeOf.inst tyargs, k))
      | Eq -> (
          let args, newnfs = dom_vars (Ctx.length ctx) doms in
          let newctx = Ctx.vis ctx (`Cube x) newnfs in
          let output = tyof_app cods tyargs args in
          let body = readback_at newctx (apply tm args) output in
          (* If the term is already an abstraction, we pick up its variable(s). *)
          match tm with
          | Lam (`Cube x, _) -> Lam (k, `Cube x, body)
          | Lam (`Normal x, _) -> (
              match compare (CubeOf.dim x) k with
              | Eq -> Lam (k, `Normal x, body)
              | Neq -> fatal (Dimension_mismatch ("variables reading back pi", CubeOf.dim x, k)))
          (* Also if it's a partial application of a constant that's defined as a case tree, we pick up variables from the case tree. *)
          | Uninst (Neu (Const { name; _ }, args), _) -> (
              match Hashtbl.find_opt Global.constants name with
              | Some (Defined tree) -> (
                  match Case.nth_var !tree args with
                  | Some (Any (`Cube x)) -> Lam (k, `Cube x, body)
                  | Some (Any (`Normal x)) -> (
                      match compare (CubeOf.dim x) k with
                      | Eq -> Lam (k, `Normal x, body)
                      | Neq ->
                          fatal (Dimension_mismatch ("variables reading back pi", CubeOf.dim x, k)))
                  (* Otherwise, we use the variable(s) from the type.  However, in this case we insist that the variable has a name, since we are (probably?) doing an eta-expansion and so the variable *will* appear in the body even if the pi-type is non-dependent. *)
                  | None -> Lam (k, singleton_named_variables k x, body))
              | _ -> Lam (k, singleton_named_variables k x, body))
          | _ -> Lam (k, singleton_named_variables k x, body)))
  | Canonical (name, canonical_args, ins) -> (
      let k = cod_left_ins ins in
      match Hashtbl.find Global.constants name with
      | Record { eta; fields; _ } -> (
          let module M = Monad.State (struct
            type t = a term Field.Map.t
          end) in
          let open Monad.Ops (M) in
          let open Mlist.Monadic (M) in
          if eta then
            let _, fields =
              miterM
                (fun [ (fld, _) ] ->
                  let* fields = M.get in
                  M.put
                    (fields
                    |> Field.Map.add fld (readback_at ctx (field tm fld) (tyof_field tm ty fld))))
                [ fields ] Field.Map.empty in
            Struct fields
          else
            match tm with
            | Struct (tmflds, tmins) ->
                let _, fields =
                  miterM
                    (fun [ (fld, _) ] ->
                      let* fields = M.get in
                      M.put
                        (fields
                        |> Field.Map.add fld
                             (readback_at ctx (Field.Map.find fld tmflds) (tyof_field tm ty fld))))
                    [ fields ] Field.Map.empty in
                Act (Struct fields, perm_of_ins tmins)
            | _ -> readback_val ctx tm)
      | Data { constrs; params; indices } -> (
          match compare (TubeOf.inst tyargs) k with
          | Neq -> fatal (Dimension_mismatch ("reading back canonical", TubeOf.inst tyargs, k))
          | Eq -> (
              match tm with
              | Constr (xconstr, xn, xargs) -> (
                  match compare xn (TubeOf.inst tyargs) with
                  | Neq ->
                      fatal (Dimension_mismatch ("reading back constrs", xn, TubeOf.inst tyargs))
                  | Eq ->
                      let (Constr { args = argtys; indices = _ }) =
                        Constr.Map.find xconstr constrs in
                      let env, _ =
                        take_canonical_args (Emp k) canonical_args params (N.plus_right indices)
                      in
                      let tyarg_args =
                        TubeOf.mmap
                          {
                            map =
                              (fun _ [ tm ] ->
                                match tm.tm with
                                | Constr (tmname, _, tmargs) ->
                                    if tmname = xconstr then
                                      Bwd.map (fun a -> CubeOf.find_top a) tmargs
                                    else
                                      fatal
                                        (Anomaly "inst arg wrong constr in readback at datatype")
                                | _ -> fatal (Anomaly "inst arg not constr in readback at datatype"));
                          }
                          [ tyargs ] in
                      Constr
                        ( xconstr,
                          k,
                          Bwd.of_list
                            (readback_at_tel ctx env
                               (Bwd.fold_right (fun a args -> CubeOf.find_top a :: args) xargs [])
                               argtys
                               (TubeOf.mmap
                                  { map = (fun _ [ args ] -> Bwd.to_list args) }
                                  [ tyarg_args ])) ))
              | _ -> readback_val ctx tm))
      | _ -> readback_val ctx tm)
  | _ -> readback_val ctx tm

and readback_val : type a z. (z, a) Ctx.t -> value -> a term =
 fun n x ->
  match x with
  | Uninst (u, _) -> readback_uninst n u
  | Inst { tm; dim = _; args; tys = _ } ->
      let tm = readback_uninst n tm in
      let args = TubeOf.mmap { map = (fun _ [ x ] -> readback_nf n x) } [ args ] in
      Inst (tm, args)
  | Lam _ -> fatal (Anomaly "unexpected lambda in synthesizing readback")
  | Struct _ -> fatal (Anomaly "unexpected struct in synthesizing readback")
  | Constr _ -> fatal (Anomaly "unexpected constr in synthesizing readback")

and readback_uninst : type a z. (z, a) Ctx.t -> uninst -> a term =
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
                  let sctx = Ctx.vis ctx (`Cube x) (CubeOf.subcube fa newnfs) in
                  let sargs = CubeOf.subcube fa args in
                  readback_val sctx (apply_binder (BindCube.find cods fa) sargs));
            } )
  | Neu (fn, args) ->
      Bwd.fold_left
        (fun fn (Value.App (arg, ins)) ->
          Term.Act
            ( (match arg with
              | Arg args ->
                  App (fn, CubeOf.mmap { map = (fun _ [ tm ] -> readback_nf ctx tm) } [ args ])
              | Field fld -> Field (fn, fld)),
              perm_of_ins ins ))
        (readback_head ctx fn) args
  | Canonical (name, args, ins) ->
      Act
        ( Bwd.fold_left
            (fun fn arg ->
              Term.App (fn, CubeOf.mmap { map = (fun _ [ tm ] -> readback_nf ctx tm) } [ arg ]))
            (* TODO: When constants can be higher-dimensional, this needs adjusting. *)
            (Act (Const name, deg_zero (cod_left_ins ins)))
            args,
          perm_of_ins ins )

and readback_head : type a k z. (z, a) Ctx.t -> head -> a term =
 fun ctx h ->
  match h with
  | Var { level; deg } -> (
      match Ctx.find_level ctx level with
      | Some x -> Act (Var x, deg)
      | None -> fatal (No_such_level level))
  (* TODO: When constants can be higher-dimensional, this needs adjusting. *)
  | Const { name; dim } -> Act (Const name, deg_zero dim)

and readback_at_tel :
    type n c a b ab z.
    (z, c) Ctx.t ->
    (n, a) env ->
    value list ->
    (a, b, ab) Telescope.t ->
    (D.zero, n, n, value list) TubeOf.t ->
    (n, c term) CubeOf.t list =
 fun ctx env xs tys tyargs ->
  match (xs, tys) with
  | [], Emp -> []
  | x :: xs, Ext (_, ty, tys) ->
      let ety = eval env ty in
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
                        (eval (Act (env, op_of_sface fa)) ty)
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
