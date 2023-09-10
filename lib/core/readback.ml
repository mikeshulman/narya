open Bwd
open Util
open Dim
open Value
open Term
open Norm

exception Missing_variable

(* Eta-expanding readback of values to terms.  Closely follows eta-expanding equality-testing. *)

let rec readback_nf : type a. a Coctx.t -> normal -> a term = fun n x -> readback_at n x.tm x.ty

and readback_at : type a. a Coctx.t -> value -> value -> a term =
 fun n tm ty ->
  (* The type must be fully instantiated. *)
  let (Fullinst (uty, tyargs)) = full_inst ty "equal_at" in
  match uty with
  (* The only interesting thing here happens when the type is one with an eta-rule, such as a pi-type. *)
  | Pi (doms, cods) -> (
      let k = CubeOf.dim doms in
      (* The pi-type must be instantiated at the correct dimension. *)
      match compare (TubeOf.inst tyargs) k with
      | Neq -> raise (Failure "Instantiation mismatch in equality-checking")
      | Eq ->
          (* Create variables for all the boundary domains. *)
          let (Faces df) = count_faces k in
          let (Plus af) = N.plus (faces_out df) in
          let vars, args, _, level = dom_vars n.level doms in
          let ctx =
            {
              Coctx.vars =
                fst
                  (CubeOf.fold_left_append_map { fold = (fun _ _ l -> (l, ())) } n.vars df af vars);
              level;
            } in
          (* Calculate the output type of the application to those variables *)
          let output = tyof_app cods tyargs args in
          Lam (Bind (df, af, readback_at ctx (apply tm args) output)))
  | Neu (Const { name; _ }, _) -> (
      match Hashtbl.find_opt Global.records name with
      | Some (Record { eta; fields; _ }) -> (
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
                  let sctx =
                    {
                      Coctx.vars =
                        fst
                          (CubeOf.fold_left_append_map
                             { fold = (fun _ _ l -> (l, ())) }
                             ctx.vars sf asf svars);
                      level;
                    } in
                  let sargs = CubeOf.subcube fa args in
                  Bind (sf, asf, readback_val sctx (apply_binder (BindCube.find cods fa) sargs)));
            } )
  | Neu (fn, args) ->
      Bwd.fold_left
        (fun fn (Value.App (arg, ins)) ->
          Act
            ( (match arg with
              | Arg args ->
                  App (fn, CubeOf.mmap { map = (fun _ [ tm ] -> readback_val ctx tm.tm) } [ args ])
              | Field fld -> Field (fn, fld)),
              perm_of_ins ins ))
        (readback_head ctx fn) args

and readback_head : type a k. a Coctx.t -> head -> a term =
 fun ctx h ->
  match h with
  | Var { level; deg } -> (
      match Bwv.index level ctx.vars with
      | Some x -> Act (Var x, deg)
      | None -> raise Missing_variable)
  | Const { name; dim } -> Act (Const name, deg_zero dim)
