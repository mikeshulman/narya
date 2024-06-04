open Util
open Reporter
open Dim
open Syntax
open Value
open Inst
open Domvars
open Norm
open Monad.ZeroOps (Monad.Maybe)
open Bwd
module ListM = Mlist.Monadic (Monad.Maybe)
module BwdM = Mbwd.Monadic (Monad.Maybe)

(* Eta-expanding equality checks.  In all functions, the integer is the current De Bruijn level, i.e. the length of the current context (we don't need any other information about the context). *)

(* Compare two normal forms that are *assumed* to have the same type. *)
let rec equal_nf : int -> normal -> normal -> unit option =
 fun n x y ->
  (* Thus, we can do an eta-expanding check at either one of their stored types, since they are assumed equal.  *)
  equal_at n x.tm y.tm x.ty

(* Compare two values at a type, which they are both assumed to belong to.  We do eta-expansion here if the type is one with an eta-rule, like a pi-type or a record type.  We also deal with the case of terms that don't synthesize, such as structs even in codatatypes without eta, and constructors in datatypes. *)
and equal_at : int -> kinetic value -> kinetic value -> kinetic value -> unit option =
 fun ctx x y ty ->
  (* The type must be fully instantiated. *)
  let (Fullinst (uty, tyargs)) = full_inst ty "equal_at" in
  match uty with
  (* The only interesting thing here happens when the type is one with an eta-rule, such as a pi-type. *)
  | Pi (_, doms, cods) -> (
      let k = CubeOf.dim doms in
      (* The pi-type must be instantiated at the correct dimension. *)
      match D.compare (TubeOf.inst tyargs) k with
      | Neq -> fatal (Dimension_mismatch ("equality at pi", TubeOf.inst tyargs, k))
      | Eq ->
          (* Create variables for all the boundary domains. *)
          let newargs, _ = dom_vars ctx doms in
          (* Calculate the output type of the application to those variables *)
          let output = tyof_app cods tyargs newargs in
          (* If both terms have the given pi-type, then when applied to variables of the domains, they will both have the computed output-type, so we can recurse back to eta-expanding equality at that type. *)
          equal_at (ctx + 1) (apply_term x newargs) (apply_term y newargs) output)
  (* In the case of a codatatype/record, the insertion ought to match whatever there is on the structs, in the case when it's possible, so we don't bother giving it a name or checking it.  And its dimension gets checked by tyof_field.  In fact because we pass off to 'field' and 'tyof_field', we don't need to make explicit use of any of the data here except whether it has eta and what the list of field names is. *)
  | Neu { alignment = Lawful (Codata { eta = Eta; fields; _ }); _ } ->
      (* In the eta case, we take the projections and compare them at appropriate types.  It suffices to use the fields of x when computing the types of the fields, since we proceed to check the fields for equality *in order* and thus by the time we are checking equality of any particulary field of x and y, the previous fields of x and y are already known to be equal, and the type of the current field can only depend on these.  (This is a semantic constraint on the kinds of generalized records that can sensibly admit eta-conversion.) *)
      BwdM.miterM
        (fun [ (fld, _) ] -> equal_at ctx (field x fld) (field y fld) (tyof_field x ty fld))
        [ fields ]
  | Neu { alignment = Lawful (Codata { eta = Noeta; fields; _ }); _ } -> (
      (* At a record-type without eta, two structs are equal if their insertions and corresponding fields are equal, and a struct is not equal to any other term.  We have to handle these cases here, though, because once we get to equal_val we don't have the type information, which is not stored in a struct. *)
      match (x, y) with
      | Struct (xfld, xins), Struct (yfld, yins) ->
          let* () = deg_equiv (perm_of_ins xins) (perm_of_ins yins) in
          BwdM.miterM
            (fun [ (fld, _) ] ->
              let xv =
                match Abwd.find_opt fld xfld with
                | Some xv -> xv
                | None -> fatal (Anomaly "missing field in equality-check") in
              let (Val xtm) = Lazy.force (fst xv) in
              let yv =
                match Abwd.find_opt fld yfld with
                | Some yv -> yv
                | None -> fatal (Anomaly "missing field in equality-check") in
              let (Val ytm) = Lazy.force (fst yv) in
              equal_at ctx xtm ytm (tyof_field x ty fld))
            [ fields ]
      | Struct _, _ | _, Struct _ -> fail
      | _ -> equal_val ctx x y)
  (* At a datatype, two constructors are equal if they are instances of the same constructor, with the same dimension and arguments.  Again, we handle these cases here because we can use the datatype information to give types to the arguments of the constructor.  We require the datatype to be applied to all its indices, and we check the dimension. *)
  | Neu { alignment = Lawful (Data { constrs; _ }); _ } -> (
      match (x, y) with
      | Constr (xconstr, xn, xargs), Constr (yconstr, yn, yargs) -> (
          let (Dataconstr { env; args = argtys; indices = _ }) =
            match Abwd.find_opt xconstr constrs with
            | Some x -> x
            | None -> fatal (Anomaly "constr not found in equality-check") in
          let* () = guard (xconstr = yconstr) in
          match
            ( D.compare xn yn,
              D.compare xn (TubeOf.inst tyargs),
              D.compare (TubeOf.inst tyargs) (dim_env env) )
          with
          | Neq, _, _ -> fatal (Dimension_mismatch ("equality of constrs", xn, yn))
          | _, Neq, _ -> fatal (Dimension_mismatch ("equality of constrs", xn, TubeOf.inst tyargs))
          | _, _, Neq ->
              fatal (Dimension_mismatch ("equality at canonical", TubeOf.inst tyargs, dim_env env))
          | Eq, Eq, Eq ->
              (* The instantiation must be at other instances of the same constructor; we take its arguments as in 'check'. *)
              let tyarg_args =
                TubeOf.mmap
                  {
                    map =
                      (fun _ [ tm ] ->
                        match tm.tm with
                        | Constr (tmname, _, tmargs) ->
                            if tmname = xconstr then List.map (fun a -> CubeOf.find_top a) tmargs
                            else fatal (Anomaly "inst arg wrong constr in equality at datatype")
                        | _ -> fatal (Anomaly "inst arg not constr in equality at datatype"));
                  }
                  [ tyargs ] in
              (* It suffices to compare the top-dimensional faces of the cubes; the others are only there for evaluating case trees.  It would be nice to do this recursion directly on the Bwds, but equal_at_tel is expressed much more cleanly as an operation on lists. *)
              equal_at_tel ctx env
                (List.fold_right (fun a args -> CubeOf.find_top a :: args) xargs [])
                (List.fold_right (fun a args -> CubeOf.find_top a :: args) yargs [])
                argtys
                (TubeOf.mmap { map = (fun _ [ args ] -> args) } [ tyarg_args ]))
      | Constr _, _ | _, Constr _ -> fail
      | _ -> equal_val ctx x y)
  (* If the type is not one that has an eta-rule, then we pass off to a synthesizing equality-check, forgetting about our assumption that the two terms had the same type.  This is the equality-checking analogue of the conversion rule for checking a synthesizing term, but since equality requires no evidence we don't have to actually synthesize a type at which they are equal or verify that it equals the type we assumed them to have. *)
  | _ -> equal_val ctx x y

(* "Synthesizing" equality check of two values, now *not* assumed a priori to have the same type.  If this function concludes that they are equal, then the equality of their types is part of that conclusion. *)
and equal_val : int -> kinetic value -> kinetic value -> unit option =
 fun n x y ->
  match (x, y) with
  (* Since an Inst has a positive amount of instantiation, it can never equal an Uninst.  We don't need to check that the types agree, since equal_uninst concludes equality of types rather than assumes it. *)
  | Uninst (u, _), Uninst (v, _) -> equal_uninst n u v
  | Inst { tm = tm1; dim = _; args = a1; tys = _ }, Inst { tm = tm2; dim = _; args = a2; tys = _ }
    -> (
      let* () = equal_uninst n tm1 tm2 in
      (* If tm1 and tm2 are equal and have the same type, that type must be an instantiation of a universe of the same dimension, itself instantiated at the same arguments.  So for the instantiations to be equal (including their types), it suffices for the instantiation dimensions and arguments to be equal. *)
      match
        ( D.compare (TubeOf.inst a1) (TubeOf.inst a2),
          D.compare (TubeOf.uninst a1) (TubeOf.uninst a2) )
      with
      | Eq, Eq ->
          let Eq = D.plus_uniq (TubeOf.plus a1) (TubeOf.plus a2) in
          let open TubeOf.Monadic (Monad.Maybe) in
          (* Because instantiation arguments are stored as normals, we use type-sensitive equality to compare them. *)
          miterM { it = (fun _ [ x; y ] -> equal_nf n x y) } [ a1; a2 ]
      | _ -> fail)
  | Lam _, _ | _, Lam _ -> fatal (Anomaly "unexpected lambda in synthesizing equality-check")
  | Struct _, _ | _, Struct _ -> fatal (Anomaly "unexpected struct in synthesizing equality-check")
  | _, _ -> fail

(* Subroutine of equal_val.  Like it, equality of the types is part of the conclusion, not a hypothesis.  *)
and equal_uninst : int -> uninst -> uninst -> unit option =
 fun lvl x y ->
  match (x, y) with
  | UU m, UU n -> (
      (* Two universes are equal precisely when they have the same dimension, in which case they also automatically have the same type (a standard instantiation of a (higher) universe of that same dimension). *)
      match D.compare m n with
      | Eq -> return ()
      | _ -> fail)
  | ( Neu { head = head1; args = args1; alignment = _ },
      Neu { head = head2; args = args2; alignment = _ } ) ->
      (* To check two neutral applications are equal, with their types, we first check if the functions are equal, including their types and hence also their domains and codomains (and also they have the same insertion applied outside).  An alignment doesn't affect definitional equality. *)
      let* () = equal_head lvl head1 head2 in
      (* Then we recursively check that all their arguments are equal. *)
      equal_args lvl args1 args2
  | Pi (_, dom1s, cod1s), Pi (_, dom2s, cod2s) -> (
      (* If two pi-types have the same dimension, equal domains, and equal codomains, they are equal and have the same type (an instantiation of the universe of that dimension at pi-types formed from the lower-dimensional domains and codomains). *)
      let k = CubeOf.dim dom1s in
      match D.compare (CubeOf.dim dom2s) k with
      | Eq ->
          let open CubeOf.Monadic (Monad.Maybe) in
          let* () = miterM { it = (fun _ [ x; y ] -> equal_val lvl x y) } [ dom1s; dom2s ] in
          (* We create variables for all the domains, in order to equality-check all the codomains.  The codomain boundary types only use some of those variables, but it doesn't hurt to have the others around. *)
          let newargs, _ = dom_vars lvl dom1s in
          let open BindCube.Monadic (Monad.Maybe) in
          miterM
            {
              it =
                (fun s [ cod1; cod2 ] ->
                  let sargs = CubeOf.subcube s newargs in
                  equal_val (lvl + 1) (apply_binder_term cod1 sargs) (apply_binder_term cod2 sargs));
            }
            [ cod1s; cod2s ]
      | Neq -> fail)
  | _ -> fail

(* Synthesizing equality check for heads.  Again equality of types is part of the conclusion, not a hypothesis. *)
and equal_head : int -> head -> head -> unit option =
 fun lvl x y ->
  match (x, y) with
  | Var { level = l1; deg = d1 }, Var { level = l2; deg = d2 } ->
      (* Two equal variables with the same degeneracy applied are equal, including their types because that variable has only one type. *)
      let* () = guard (l1 = l2) in
      deg_equiv d1 d2
  | Const { name = c1; ins = i1 }, Const { name = c2; ins = i2 } -> (
      let* () = guard (c1 = c2) in
      match D.compare (cod_left_ins i1) (cod_left_ins i2) with
      | Eq ->
          let d1 = deg_of_ins i1 (plus_of_ins i1) in
          let d2 = deg_of_ins i2 (plus_of_ins i2) in
          deg_equiv d1 d2
      | Neq -> fail)
  | Meta { meta = meta1; env = env1; ins = i1 }, Meta { meta = meta2; env = env2; ins = i2 } -> (
      match (Meta.compare meta1 meta2, D.compare (cod_left_ins i1) (cod_left_ins i2)) with
      | Eq, Eq ->
          let (Metadef { termctx; _ }) =
            Global.find_meta_opt meta1 <|> Undefined_metavariable (PMeta meta1) in
          equal_env lvl env1 env2 termctx
      | _ -> fail)
  | _, _ -> fail

(* Check that the arguments of two entire application spines of equal functions are equal.  This is basically a left fold, but we make sure to iterate from left to right, and fail rather than raising an exception if the lists have different lengths.  *)
and equal_args : int -> app Bwd.t -> app Bwd.t -> unit option =
 fun lvl args1 args2 ->
  match (args1, args2) with
  | Emp, Emp -> return ()
  | Snoc (rest1, arg1), Snoc (rest2, arg2) ->
      (* Iterating from left to right is important because it ensures that at the point of checking equality for any pair of arguments, we know that they have the same type, since they are valid arguments of equal functions with all previous arguments equal.  *)
      let* () = equal_args lvl rest1 rest2 in
      equal_arg lvl arg1 arg2
  | Emp, Snoc _ | Snoc _, Emp -> fail

(* Check that two application arguments are equal, including their outer insertions as well as their values.  As noted above, here we can go back to *assuming* that they have equal types, and thus passing off to the eta-expanding equality check. *)
and equal_arg : int -> app -> app -> unit option =
 fun n (App (a1, i1)) (App (a2, i2)) ->
  let* () = deg_equiv (perm_of_ins i1) (perm_of_ins i2) in
  match (a1, a2) with
  | Arg a1, Arg a2 -> (
      match D.compare (CubeOf.dim a1) (CubeOf.dim a2) with
      | Eq ->
          let open CubeOf.Monadic (Monad.Maybe) in
          miterM { it = (fun _ [ x; y ] -> (equal_nf n) x y) } [ a1; a2 ]
      (* If the dimensions don't match, it is a bug rather than a user error, since they are supposed to both be valid arguments of the same function, and any function has a unique dimension. *)
      | Neq ->
          fatal (Dimension_mismatch ("application in equality-check", CubeOf.dim a1, CubeOf.dim a2))
      )
  | Field f1, Field f2 -> guard (f1 = f2)
  | _, _ -> fail

and equal_at_tel :
    type n a b ab.
    int ->
    (n, a) env ->
    kinetic value list ->
    kinetic value list ->
    (a, b, ab) Telescope.t ->
    (D.zero, n, n, kinetic value list) TubeOf.t ->
    unit option =
 fun ctx env xs ys tys tyargs ->
  match (xs, ys, tys) with
  | [], [], Emp -> Some ()
  | x :: xs, y :: ys, Ext (_, ty, tys) ->
      let ety = eval_term env ty in
      (* Copied from check_tel; TODO: Factor it out *)
      let tyargtbl = Hashtbl.create 10 in
      let [ tyarg; tyargs ] =
        TubeOf.pmap
          {
            map =
              (fun fa [ tyargs ] ->
                match tyargs with
                | [] -> fatal (Anomaly "missing arguments in equal_at_tel")
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
                    Hashtbl.add tyargtbl (SFace_of fa) argnorm;
                    [ argnorm; argrest ]);
          }
          [ tyargs ] (Cons (Cons Nil)) in
      let ity = inst ety tyarg in
      let* () = equal_at ctx x y ity in
      equal_at_tel ctx
        (Ext (env, CubeOf.singleton (TubeOf.plus_cube (val_of_norm_tube tyarg) (CubeOf.singleton x))))
        xs ys tys tyargs
  | _ -> fatal (Anomaly "length mismatch in equal_at_tel")

and equal_env : type a b n. int -> (n, b) env -> (n, b) env -> (a, b) Termctx.t -> unit option =
 fun lvl env1 env2 (Permute (_, envctx)) -> equal_ordered_env lvl env1 env2 envctx

and equal_ordered_env :
    type a b n. int -> (n, b) env -> (n, b) env -> (a, b) Termctx.ordered -> unit option =
 fun lvl env1 env2 envctx ->
  (* Copied from readback_ordered_env *)
  match envctx with
  | Emp -> Some ()
  | Lock envctx -> equal_ordered_env lvl env1 env2 envctx
  | Snoc (envctx, entry, _) -> (
      let open Monad.Ops (Monad.Maybe) in
      let open CubeOf.Monadic (Monad.Maybe) in
      let (Ext (env1', xss1)) = Permute.env_top env1 in
      let (Ext (env2', xss2)) = Permute.env_top env2 in
      let* () = equal_ordered_env lvl env1' env2' envctx in
      match entry with
      | Vis { bindings; _ } | Invis bindings ->
          let* _ =
            mmapM
              {
                map =
                  (fun fa [ xs1; xs2 ] ->
                    let ty = (CubeOf.find bindings fa).ty in
                    let xtytbl = Hashtbl.create 10 in
                    mmapM
                      {
                        map =
                          (fun fb [ tm1; tm2 ] ->
                            let k = dom_sface fb in
                            let ty =
                              inst
                                (eval_term (Act (env1, op_of_sface fb)) ty)
                                (TubeOf.build k (D.plus_zero k)
                                   {
                                     build =
                                       (fun fc ->
                                         Hashtbl.find xtytbl
                                           (SFace_of (comp_sface fb (sface_of_tface fc))));
                                   }) in
                            Hashtbl.add xtytbl (SFace_of fb) { tm = tm1; ty };
                            equal_at lvl tm1 tm2 ty);
                      }
                      [ xs1; xs2 ]);
              }
              [ xss1; xss2 ] in
          return ())
