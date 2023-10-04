open Bwd
open Util
open Dim
open Value
open Term
open Norm

exception Missing_variable

(* Eta-expanding readback of values to terms.  Closely follows eta-expanding equality-testing in equal.ml, so most comments are omitted. *)

let rec readback_nf : type a. a Coctx.t -> normal -> a term = fun n x -> readback_at n x.tm x.ty

and readback_at : type a. a Coctx.t -> value -> value -> a term =
 fun n tm ty ->
  let (Fullinst (uty, tyargs)) = full_inst ty "equal_at" in
  match uty with
  | Pi (doms, cods) -> (
      let k = CubeOf.dim doms in
      match compare (TubeOf.inst tyargs) k with
      | Neq -> raise (Failure "Instantiation mismatch in equality-checking")
      | Eq ->
          let (Faces df) = count_faces k in
          let (Plus af) = N.plus (faces_out df) in
          let vars, args, _, level = dom_vars n.level doms in
          let ctx = { Coctx.vars = CubeOf.flatten_append n.vars vars df af; level } in
          let output = tyof_app cods tyargs args in
          Lam (Bind (df, af, readback_at ctx (apply tm args) output)))
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
                    |> Field.Map.add fld (readback_at n (field tm fld) (tyof_field tm ty fld))))
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
                             (readback_at n (Field.Map.find fld tmflds) (tyof_field tm ty fld))))
                    [ fields ] Field.Map.empty in
                Act (Struct fields, perm_of_ins tmins)
            | _ -> readback_val n tm)
      | Data { constrs; params; indices } -> (
          match compare (TubeOf.inst tyargs) k with
          | Neq -> raise (Failure "Instantiation mismatch in readback at canonical")
          | Eq -> (
              match tm with
              | Constr (xconstr, xn, xargs) -> (
                  match compare xn (TubeOf.inst tyargs) with
                  | Neq -> raise (Failure "Unequal dimensions of constrs in readback")
                  | Eq ->
                      let (Constr { args = argtys; indices = _ }) =
                        Constr.Map.find xconstr constrs in
                      let env, _ =
                        take_canonical_args (Emp k) canonical_args (N.zero_plus params) indices
                      in
                      let tyarg_args =
                        TubeOf.mmap
                          {
                            map =
                              (fun _ [ tm ] ->
                                match tm.tm with
                                | Constr (tmname, l, tmargs) ->
                                    if tmname = xconstr then
                                      Bwd.map (fun a -> CubeOf.find a (id_sface l)) tmargs
                                    else
                                      raise
                                        (Failure "Inst arg wrong constr in readback at datatype")
                                | _ -> raise (Failure "Inst arg not constr in readback at datatype"));
                          }
                          [ tyargs ] in
                      Constr
                        ( xconstr,
                          k,
                          Bwd.of_list
                            (readback_at_tel n env
                               (Bwd.fold_right
                                  (fun a args -> CubeOf.find a (id_sface xn) :: args)
                                  xargs [])
                               argtys
                               (TubeOf.mmap
                                  { map = (fun _ [ args ] -> Bwd.to_list args) }
                                  [ tyarg_args ])) ))
              | _ -> readback_val n tm))
      | _ -> readback_val n tm)
  | _ -> readback_val n tm

and readback_val : type a. a Coctx.t -> value -> a term =
 fun n x ->
  match x with
  | Uninst (u, _) -> readback_uninst n u
  | Inst { tm; dim = _; args; tys = _ } ->
      let tm = readback_uninst n tm in
      let args = TubeOf.mmap { map = (fun _ [ x ] -> readback_nf n x) } [ args ] in
      Inst (tm, args)
  | Lam _ -> raise (Failure "Unexpected lambda in synthesizing readback")
  | Struct _ -> raise (Failure "Unexpected struct in synthesizing readback")
  | Constr _ -> raise (Failure "Unexpected constr in synthesizing readback")

and readback_uninst : type a. a Coctx.t -> uninst -> a term =
 fun ctx x ->
  match x with
  | UU m -> UU m
  | Pi (doms, cods) ->
      let k = CubeOf.dim doms in
      let vars, args, _, level = dom_vars ctx.level doms in
      Pi
        ( CubeOf.mmap { map = (fun _ [ dom ] -> readback_val ctx dom) } [ doms ],
          CodCube.build k
            {
              build =
                (fun fa ->
                  let (Faces sf) = count_faces (dom_sface fa) in
                  let (Plus asf) = N.plus (faces_out sf) in
                  let svars = CubeOf.subcube fa vars in
                  let sctx = { Coctx.vars = CubeOf.flatten_append ctx.vars svars sf asf; level } in
                  let sargs = CubeOf.subcube fa args in
                  Bind (sf, asf, readback_val sctx (apply_binder (BindCube.find cods fa) sargs)));
            } )
  | Neu (fn, args) ->
      Bwd.fold_left
        (fun fn (Value.App (arg, ins)) ->
          Act
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
              App (fn, CubeOf.mmap { map = (fun _ [ tm ] -> readback_nf ctx tm) } [ arg ]))
            (Const name) args,
          perm_of_ins ins )

and readback_head : type a k. a Coctx.t -> head -> a term =
 fun ctx h ->
  match h with
  | Var { level; deg } -> (
      match Bwv.index (Some level) ctx.vars with
      | Some x -> Act (Var x, deg)
      | None -> raise Missing_variable)
  | Const { name; dim } -> Act (Const name, deg_zero dim)

and readback_at_tel :
    type n c a b ab.
    c Coctx.t ->
    (n, a) env ->
    value list ->
    (a, b, ab) Telescope.t ->
    (D.zero, n, n, value list) TubeOf.t ->
    (n, c term) CubeOf.t list =
 fun ctx env xs tys tyargs ->
  match (xs, tys) with
  | [], Emp -> []
  | x :: xs, Ext (ty, tys) ->
      let ety = eval env ty in
      (* Copied from check_tel; TODO: Factor it out *)
      let tyargtbl = Hashtbl.create 10 in
      let [ tyarg; tms; tyargs ] =
        TubeOf.pmap
          {
            map =
              (fun fa [ tyargs ] ->
                match tyargs with
                | [] -> raise (Failure "Missing arguments in readback_at_tel")
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
           (Ext (env, TubeOf.plus_cube (val_of_norm_tube tyarg) (CubeOf.singleton x)))
           xs tys tyargs
  | _ -> raise (Failure "Length mismatch in equal_at_tel")
