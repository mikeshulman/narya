open Bwd
open Util
open Reporter
open Syntax
open Term
open Value
open Inst
open Raw
open Dim
open Act
open Norm
open Equal
open Readback
open Hctx
open Printable
open Asai.Range

let ( <|> ) : type a b. a option -> Code.t -> a =
 fun x e ->
  match x with
  | Some x -> x
  | None -> fatal e

(* Look through a specified number of lambdas to find an inner body. *)
let rec lambdas :
    type a b ab. (a, b, ab) N.plus -> a check located -> string option list * ab check located =
 fun ab tm ->
  match (ab, tm.value) with
  | Zero, _ -> ([], tm)
  | Suc _, Lam (x, `Normal, body) ->
      let names, body = lambdas (N.suc_plus ab) body in
      (x :: names, body)
  | _ -> fatal (Not_enough_lambdas (N.to_int (N.plus_right ab)))

let vars_of_list m names =
  let module S = Monad.State (struct
    type t = string option list
  end) in
  let open CubeOf.Monadic (S) in
  let names, _ =
    buildM m
      {
        build =
          (fun _ ->
            let open Monad.Ops (S) in
            let* names = S.get in
            match names with
            | [] -> fatal (Anomaly "missing name")
            | x :: xs ->
                let* () = S.put xs in
                return x);
      }
      names in
  `Normal names

(* Slurp up an entire application spine.  Returns the function, the locations of all the applications (e.g. in "f x y" returns the locations of "f x" and "f x y") and all the arguments. *)
let spine :
    type a. a synth located -> a synth located * Asai.Range.t option list * a check located list =
 fun tm ->
  let rec spine tm locs args =
    match tm.value with
    | Raw.App (fn, arg) -> spine fn (tm.loc :: locs) (arg :: args)
    | _ -> (tm, locs, args) in
  spine tm [] []

(* Check a term or case tree.  The default is to check a term; the optional argument switches modes to checking a case tree. *)
let rec check :
    type a b s. s energy -> (a, b) Ctx.t -> a check located -> kinetic value -> (b, s) term =
 fun energy ctx tm ty ->
  with_loc tm.loc @@ fun () ->
  (* If the "type" is not a type here, or not fully instantiated, that's a user error, not a bug. *)
  let (Fullinst (uty, tyargs)) = full_inst ~severity:Asai.Diagnostic.Error ty "typechecking" in
  match (tm.value, energy) with
  | Synth stm, _ -> (
      let sval, sty = synth ctx { value = stm; loc = tm.loc } in
      let () =
        equal_val (Ctx.length ctx) sty ty
        <|> Unequal_synthesized_type (PVal (ctx, sty), PVal (ctx, ty)) in
      match energy with
      | Potential -> (Term.Realize sval : (b, s) term)
      | Kinetic -> sval)
  | Lam (x, cube, body), _ -> (
      match uty with
      | Pi (_, doms, cods) -> (
          let m = CubeOf.dim doms in
          match compare (TubeOf.inst tyargs) m with
          | Neq -> fatal (Dimension_mismatch ("checking lambda", TubeOf.inst tyargs, m))
          | Eq ->
              let Eq = D.plus_uniq (TubeOf.plus tyargs) (D.zero_plus m) in
              (* Extend the context by one variable for each type in doms, instantiated at the appropriate previous ones. *)
              let newargs, newnfs = dom_vars (Ctx.length ctx) doms in
              (* Apply and instantiate the codomain to those arguments to get a type to check the body at. *)
              let output = tyof_app cods tyargs newargs in
              let xs, cbody =
                match cube with
                | `Normal ->
                    (* Slurp up the right number of lambdas for the dimension of the pi-type, and pick up the body inside them. *)
                    let (Faces dom_faces) = count_faces m in
                    let f = faces_out dom_faces in
                    let (Plus af) = N.plus f in
                    let names, body = lambdas af tm in
                    let names = vars_of_list m names in
                    (names, check energy (Ctx.split ctx dom_faces af names newnfs) body output)
                | `Cube ->
                    (* Here we don't need to slurp up lots of lambdas, but can make do with one. *)
                    (`Cube x, check energy (Ctx.vis ctx (`Cube x) newnfs) body output) in
              Term.Lam (m, xs, cbody))
      | _ -> fatal (Checking_lambda_at_nonfunction (PUninst (ctx, uty))))
  | Struct (Noeta, _), Kinetic ->
      fatal (Unimplemented "Comatching in terms (rather than case trees)")
  | Struct (tmeta, tms), _ -> (
      match uty with
      | Neu { head = Const { name; _ }; alignment = Lawful (Codata { eta; ins; fields; _ }); _ }
      (* We don't need to name the arguments here because tyof_field, called below, uses them. *)
        when match (eta, tmeta) with
             | Eta, Eta | Noeta, Noeta -> true
             | _ -> false ->
          let () =
            is_id_perm (perm_of_ins ins) <|> Checking_tuple_at_degenerated_record (PConstant name)
          in
          let dim = cod_left_ins ins in
          (* The type of each record field, at which we check the corresponding field supplied in the struct, is the type associated to that field name in general, evaluated at the supplied parameters and at "the term itself".  We don't have the whole term available while typechecking, of course, but we can build a version of it that contains all the previously typechecked fields, which is all we need for a well-typed record.  So we iterate through the fields (in the order specified in the *type*, since that determines the dependencies) while also accumulating the previously typechecked and evaluated fields.  At the end, we throw away the evaluated fields (although as usual, that seems wasteful). *)
          let etms = ref Abwd.empty in
          let labeled_tms = ref tms in
          let ctms =
            Abwd.mapi (fun fld _ -> check_field energy ctx ty dim tms etms labeled_tms fld) fields
          in
          (* We had to typecheck the fields in the order given in the record type, since later ones might depend on earlier ones.  But then we re-order them back to the order given in the struct, to match what the user wrote. *)
          Term.Struct
            ( Eta,
              Bwd.map
                (fun (fld, _) ->
                  match fld with
                  | Some fld -> (fld, Abwd.find fld ctms)
                  | None -> fatal (Extra_field_in_tuple None))
                !labeled_tms )
      | _ ->
          fatal
            (match tmeta with
            | Eta -> Checking_tuple_at_nonrecord (PUninst (ctx, uty))
            | Noeta -> Comatching_at_noncodata (PUninst (ctx, uty))))
  | Constr ({ value = constr; loc = constr_loc }, args), _ -> (
      match uty with
      | Neu
          {
            (* The insertion should always be trivial, since datatypes are always 0-dimensional. *)
            head = Const { name; _ };
            alignment = Lawful (Data { dim; indices = ty_indices; missing = Zero; constrs });
            _;
          } -> (
          (* We don't need the *types* of the parameters or indices, which are stored in the type of the constant name.  ty_indices contains the *values* of the indices of this instance of the datatype, while tyargs (defined by full_inst, way above) contains the instantiation arguments of this instance of the datatype. *)
          let (Dataconstr { env; args = constr_arg_tys; indices = constr_indices }) =
            match Constr.Map.find_opt constr constrs with
            | Some c -> c
            | None ->
                with_loc constr_loc @@ fun () ->
                fatal (No_such_constructor (`Data (PConstant name), constr)) in
          (* To typecheck a higher-dimensional instance of our constructor constr at the datatype, all the instantiation arguments must also be applications of lower-dimensional versions of that same constructor.  We check this, and extract the arguments of those lower-dimensional constructors as a tube of lists. *)
          match compare (TubeOf.inst tyargs) dim with
          | Neq -> fatal (Dimension_mismatch ("checking constr", dim_env env, dim))
          | Eq -> (
              let tyarg_args =
                TubeOf.mmap
                  {
                    map =
                      (fun fa [ tm ] ->
                        match tm.tm with
                        | Constr (tmname, n, tmargs) ->
                            if tmname <> constr then
                              fatal (Missing_instantiation_constructor (constr, `Constr tmname))
                            else
                              (* Assuming the instantiation is well-typed, we must have n = dom_tface fa.  I'd like to check that, but for some reason, matching this compare against Eq claims that the type variable n would escape its scope. *)
                              let _ = compare n (dom_tface fa) in
                              Bwd.fold_right (fun a args -> CubeOf.find_top a :: args) tmargs []
                        | _ ->
                            fatal
                              (Missing_instantiation_constructor
                                 (constr, `Nonconstr (PNormal (ctx, tm)))));
                  }
                  [ tyargs ] in
              (* Now we evaluate each argument *type* of the constructor at (the parameters and) the previous evaluated argument *values*, check each argument value against the corresponding argument type, and then evaluate it and add it to the environment (to substitute into the subsequent types, and also later to the indices). *)
              let env, newargs =
                check_at_tel constr ctx env (Bwd.to_list args) constr_arg_tys tyarg_args in
              (* Now we substitute all those evaluated arguments into the indices, to get the actual (higher-dimensional) indices of our constructor application. *)
              let constr_indices =
                Bwv.map
                  (fun ix ->
                    CubeOf.build dim
                      { build = (fun fa -> eval_term (Act (env, op_of_sface fa)) ix) })
                  constr_indices in
              (* The last thing to do is check that these indices are equal to those of the type we are checking against.  (So a constructor application "checks against the parameters but synthesizes the indices" in some sense.)  I *think* it should suffice to check the top-dimensional ones, the lower-dimensional ones being automatic.  For now, we check all of them, raising an anomaly in case I was wrong about that.  *)
              let () =
                Bwv.miter
                  (fun [ t1s; t2s ] ->
                    CubeOf.miter
                      {
                        it =
                          (fun fa [ t1; t2 ] ->
                            match equal_at (Ctx.length ctx) t1 t2.tm t2.ty with
                            | Some () -> ()
                            | None -> (
                                match is_id_sface fa with
                                | Some () ->
                                    fatal
                                      (Unequal_indices
                                         (PNormal (ctx, { tm = t1; ty = t2.ty }), PNormal (ctx, t2)))
                                | None ->
                                    fatal (Anomaly "mismatching lower-dimensional constructors")));
                      }
                      [ t1s; t2s ])
                  [ constr_indices; ty_indices ] in
              let c = Term.Constr (constr, dim, Bwd.of_list newargs) in
              match energy with
              | Potential -> Realize c
              | Kinetic -> c))
      (* TODO: If checking against a pi-type, we could automatically eta-expand. *)
      | _ ->
          with_loc constr_loc @@ fun () ->
          fatal (No_such_constructor (`Other (PUninst (ctx, uty)), constr)))
  | Match _, Kinetic -> fatal (Unimplemented "Matching in terms (rather than case trees)")
  | Match (ix, brs), Potential -> (
      (* The variable must not be let-bound to a value.  Checking that it isn't also gives us its De Bruijn level, its type, and its index in the full context including invisible variables. *)
      match Ctx.lookup ctx ix with
      | None, _, ix -> fatal (Matching_on_let_bound_variable (PTerm (ctx, Var ix)))
      | Some lvl, { tm = _; ty = varty }, ix -> (
          (* The type of the variable must be a datatype, without any degeneracy applied outside, and at the same dimension as its instantiation. *)
          let (Fullinst (uvarty, inst_args)) = full_inst varty "check_tree (top)" in
          match uvarty with
          | Neu
              {
                head = Const { name; _ };
                args = varty_args;
                alignment = Lawful (Data { dim; indices; missing = Zero; constrs });
              } -> (
              let n = TubeOf.inst inst_args in
              match compare dim n with
              | Neq -> fatal (Dimension_mismatch ("match", dim, n))
              | Eq ->
                  (* In our simple version of pattern-matching, the "indices" and all their boundaries must be distinct free variables with no degeneracies, so that in the branch for each constructor they can be set equal to the computed value of that index for that constructor (and in which they cannot occur).  This is a special case of the unification algorithm described in CDP "Pattern-matching without K" where the only allowed rule is "Solution".  Later we can try to enhance it with their full unification algorithm, at least for non-higher datatypes.  In addition, for a higher-dimensional match, the instantiation arguments must also all be distinct variables, distinct from the indices. *)
                  let seen = Hashtbl.create 10 in
                  let is_fresh x =
                    match x.tm with
                    | Uninst (Neu { head = Var { level; deg }; args = Emp; alignment = True }, _) ->
                        let () = is_id_deg deg <|> Invalid_match_index (PVal (ctx, x.tm)) in
                        if Hashtbl.mem seen level then
                          fatal (Invalid_match_index (PVal (ctx, x.tm)))
                        else (
                          Hashtbl.add seen level ();
                          level)
                    | _ -> fatal (Invalid_match_index (PVal (ctx, x.tm))) in
                  let index_vars =
                    Bwv.map
                      (fun tm -> CubeOf.mmap { map = (fun _ [ x ] -> is_fresh x) } [ tm ])
                      indices in
                  let inst_vars = TubeOf.mmap { map = (fun _ [ x ] -> is_fresh x) } [ inst_args ] in
                  let constr_vars = TubeOf.plus_cube inst_vars (CubeOf.singleton lvl) in
                  (* We now iterate through the branches supplied by the user, typechecking them and inserting them in the match tree. *)
                  let tbranches =
                    List.fold_left
                      (fun tbranches (Branch (constr, user_args, body)) ->
                        (if Constr.Map.mem constr.value tbranches then
                           with_loc constr.loc @@ fun () ->
                           fatal (Duplicate_constructor_in_match constr.value));
                        (* Get the argument types and index terms for the constructor of this branch. *)
                        let (Dataconstr { env; args = argtys; indices = index_terms }) =
                          match Constr.Map.find_opt constr.value constrs with
                          | Some c -> c
                          | None ->
                              with_loc constr.loc @@ fun () ->
                              fatal (No_such_constructor_in_match (PConstant name, constr.value))
                        in
                        let (Exts efc) = exts (Telescope.length argtys) in
                        (* The user needs to have supplied the right number of pattern variable arguments to the constructor. *)
                        let c = Telescope.length argtys in
                        match
                          (N.compare (exts_right efc) c, N.compare (N.plus_right user_args.value) c)
                        with
                        | Gt _, _ | Lt _, _ -> fatal (Anomaly "length mismatch in check_tree")
                        | _, Gt diff ->
                            with_loc user_args.loc @@ fun () ->
                            fatal
                              (Wrong_number_of_arguments_to_pattern
                                 (constr.value, N.to_int (Nat diff)))
                        | _, Lt diff ->
                            with_loc user_args.loc @@ fun () ->
                            fatal
                              (Wrong_number_of_arguments_to_pattern
                                 (constr.value, -N.to_int (Nat diff)))
                        | Eq, Eq -> (
                            (* Create new level variables for the pattern variables to which the constructor is applied, and add corresponding index variables to the context.  The types of those variables are specified in the telescope argtys, and have to be evaluated at the closure environment 'env' and the previous new variables (this is what ext_tel does).  For a higher-dimensional match, the new variables come with their boundaries in n-dimensional cubes. *)
                            let newctx, newenv, newvars =
                              Ctx.ext_tel ctx env argtys user_args.value efc in
                            (* The type of the match must be specialized in the branches by substituting different constructors for the match variable, as well as the index values for the index variables, and lower-dimensional versions of each constructor for the instantiation variables.  Thus, we readback the type into this extended context, so we can re-evaluate it with those variables bound to values. *)
                            let rty = readback_val newctx ty in
                            (* Evaluate the "index_terms" at the new pattern variables, obtaining what the indices should be for the new term that replaces the match variable in the match body. *)
                            let index_vals =
                              Bwv.map
                                (fun ixtm ->
                                  CubeOf.build n
                                    {
                                      build =
                                        (fun fa -> eval_term (Act (newenv, op_of_sface fa)) ixtm);
                                    })
                                index_terms in
                            (* Assemble a term consisting of the constructor applied to the new variables, along with its boundary, and their types.  To compute their types, we have to extract the datatype applied to its parameters only, pass to boundaries if necessary, and then re-apply it to the new indices. *)
                            let params, _ = Bwv.unappend_bwd (Bwv.length indices) varty_args in
                            let argtbl = Hashtbl.create 10 in
                            let constr_nfs =
                              CubeOf.build n
                                {
                                  build =
                                    (fun fa ->
                                      let k = dom_sface fa in
                                      let tm =
                                        Value.Constr
                                          ( constr.value,
                                            dom_sface fa,
                                            Bwv.to_bwd_map (CubeOf.subcube fa) newvars ) in
                                      let ty =
                                        inst
                                          (Bwv.fold_left
                                             (fun f a -> apply_term f (CubeOf.subcube fa a))
                                             (Bwd.fold_left
                                                (fun f -> function
                                                  | Value.App (Arg arg, _) -> (
                                                      match compare (CubeOf.dim arg) dim with
                                                      | Eq ->
                                                          apply_term f
                                                            (val_of_norm_cube
                                                               (CubeOf.subcube fa arg))
                                                      | Neq ->
                                                          fatal
                                                            (Dimension_mismatch
                                                               ("check match", CubeOf.dim arg, dim))
                                                      )
                                                  | App (Field fld, _) -> field f fld)
                                                (eval_term (Emp (dom_sface fa)) (Const name))
                                                params)
                                             index_vals)
                                          (TubeOf.build D.zero (D.zero_plus k)
                                             {
                                               build =
                                                 (fun fb ->
                                                   Hashtbl.find argtbl
                                                     (SFace_of (comp_sface fa (sface_of_tface fb))));
                                             }) in
                                      let x = { tm; ty } in
                                      Hashtbl.add argtbl (SFace_of fa) x;
                                      x);
                                } in
                            let constr_nf = CubeOf.find_top constr_nfs in
                            (* Since "index_vals" is just a Bwv of Cubes of *values*, we extract the corresponding collection of *normals* from the type.  The main use of this will be to substitute for the index variables, so instead of assembling them into another Bwv of Cubes, we make a hashtable associating those index variables to the corresponding normals.  We also include in the same hashtable the lower-dimensional applications of the same constructor, to be substituted for the instantiation variables. *)
                            let (Fullinst (ucty, _)) = full_inst constr_nf.ty "check_tree (inner)" in
                            match ucty with
                            | Neu { alignment = Lawful (Data { dim = constrdim; indices; _ }); _ }
                              -> (
                                match
                                  ( compare constrdim dim,
                                    N.compare (Bwv.length index_vars) (Bwv.length indices) )
                                with
                                | Eq, Eq ->
                                    let new_vals = Hashtbl.create 10 in
                                    CubeOf.miter
                                      { it = (fun _ [ v; c ] -> Hashtbl.add new_vals v c) }
                                      [ constr_vars; constr_nfs ];
                                    Bwv.iter2
                                      (fun vs cs ->
                                        CubeOf.miter
                                          { it = (fun _ [ v; c ] -> Hashtbl.add new_vals v c) }
                                          [ vs; cs ])
                                      index_vars indices;
                                    (* Now we let-bind the match variable to the constructor applied to these new variables, the "index_vars" to the index values, and the inst_vars to the boundary constructor values. *)
                                    let boundctx =
                                      Ctx.bind_some (Hashtbl.find_opt new_vals) newctx in
                                    (* We have to substitute the values of these newly bound variables into all the other types and terms in the context, which we do by reading them back in the old context and then evaluating in the new one. *)
                                    let thectx =
                                      Ctx.map
                                        (fun x ->
                                          let e = Ctx.env boundctx in
                                          let tm = eval_term e (readback_nf newctx x) in
                                          let ty = eval_term e (readback_val newctx x.ty) in
                                          { tm; ty })
                                        boundctx in
                                    (* We readback the index and instantiation values into this context and discard the result, catching No_such_level to turn it into a user Error.  This has the effect of doing an occurs-check that none of the index variables occur in any of the index values.  This is a bit less general than the CDP Solution rule, which (when applied one variable at a time) prohibits only cycles of occurrence. *)
                                    let _ =
                                      Reporter.try_with ~fatal:(fun d ->
                                          match d.message with
                                          | No_such_level _ -> fatal Index_variable_in_index_value
                                          | _ -> fatal_diagnostic d)
                                      @@ fun () ->
                                      Hashtbl.iter
                                        (fun _ v ->
                                          let _ = readback_nf thectx v in
                                          ())
                                        new_vals in
                                    (* We evaluate "rty" in this new context, to obtain the type at which the branch body will be checked. *)
                                    let newty = Ctx.eval_term thectx rty in
                                    (* Finally, we recurse into the "body" of the branch. *)
                                    tbranches
                                    |> Constr.Map.add constr.value
                                         (Term.Branch (efc, check energy thectx body newty))
                                | Neq, _ -> fatal (Anomaly "created datatype has wrong dimension")
                                | _, _ ->
                                    fatal (Anomaly "created datatype has wrong number of indices"))
                            | _ -> fatal (Anomaly "created datatype is not canonical?")))
                      Constr.Map.empty brs in
                  (* Coverage check *)
                  Constr.Map.iter
                    (fun c _ ->
                      if not (Constr.Map.mem c tbranches) then
                        fatal (Missing_constructor_in_match c))
                    constrs;
                  Match (ix, n, tbranches))
          | _ -> fatal (Matching_on_nondatatype (PUninst (ctx, uvarty)))))
  | Empty_co_match, Kinetic ->
      fatal (Unimplemented "(Co)matching in terms (rather than case trees)")
  | Empty_co_match, Potential -> (
      match uty with
      | Pi _ ->
          check Potential ctx
            {
              value = Raw.Lam (None, `Normal, { value = Match ((Top, None), []); loc = tm.loc });
              loc = tm.loc;
            }
            ty
      | _ -> check Potential ctx { value = Struct (Noeta, Abwd.empty); loc = tm.loc } ty)

and check_field :
    type a b n s.
    s energy ->
    (a, b) Ctx.t ->
    kinetic value ->
    n D.t ->
    (Field.t option, a check located) Abwd.t ->
    (Field.t, s evaluation Lazy.t * [ `Labeled | `Unlabeled ]) Abwd.t ref ->
    (Field.t option, a check located) Abwd.t ref ->
    Field.t ->
    (b, s) term * [ `Labeled | `Unlabeled ] =
 fun tree ctx ty dim tms etms labeled_tms fld ->
  (* Here's a struct containing all the previously typechecked fields. *)
  let str = Value.Struct (!etms, zero_ins dim) in
  let prev_etm =
    match tree with
    | Potential ->
        (* If we're checking a case tree, then those other fields might be case trees as well, and thus they should only appear inside a chaotic neutral.  We aren't currently storing the entire spine of the top-level constant being defined, so instead we create a new temporary constant. *)
        (* TODO: Is this insertion right?  Hopefully it doesn't matter. *)
        let head = Value.Const { name = Constant.make (); ins = zero_ins dim } in
        Uninst (Neu { head; args = Emp; alignment = Chaotic str }, Lazy.from_val ty)
    | Kinetic -> str in
  let ety = tyof_field prev_etm ty fld in
  match Abwd.find_opt (Some fld) tms with
  | Some tm ->
      let ctm = check tree ctx tm ety in
      etms := Abwd.add fld (lazy (Ctx.eval ctx ctm), `Labeled) !etms;
      (ctm, `Labeled)
  | None -> (
      match Abwd.find_opt_and_update_key None (Some fld) !labeled_tms with
      | Some (tm, new_labeled_tms) ->
          labeled_tms := new_labeled_tms;
          let ctm = check tree ctx tm ety in
          etms := Abwd.add fld (lazy (Ctx.eval ctx ctm), `Unlabeled) !etms;
          (ctm, `Unlabeled)
      | None -> fatal (Missing_field_in_tuple fld))

and synth : type a b. (a, b) Ctx.t -> a synth located -> (b, kinetic) term * kinetic value =
 fun ctx tm ->
  with_loc tm.loc @@ fun () ->
  match tm.value with
  | Var i ->
      let _, x, v = Ctx.lookup ctx i in
      (Term.Var v, x.ty)
  | Const name ->
      let ty = Hashtbl.find_opt Global.types name <|> Undefined_constant (PConstant name) in
      (Const name, eval_term (Emp D.zero) ty)
  | Field (tm, fld) ->
      let stm, sty = synth ctx tm in
      (* To take a field of something, the type of the something must be a record-type that contains such a field, possibly substituted to a higher dimension and instantiated. *)
      let etm = Ctx.eval_term ctx stm in
      let fld, newty = tyof_field_withname ~severity:Asai.Diagnostic.Error etm sty fld in
      (Field (stm, fld), newty)
  | UU -> (Term.UU D.zero, universe D.zero)
  | Pi (x, dom, cod) ->
      (* User-level pi-types are always dimension zero, so the domain must be a zero-dimensional type. *)
      let cdom = check Kinetic ctx dom (universe D.zero) in
      let edom = Ctx.eval_term ctx cdom in
      let ccod = check Kinetic (Ctx.ext ctx x edom) cod (universe D.zero) in
      (pi x cdom ccod, universe D.zero)
  | App _ ->
      (* If there's at least one application, we slurp up all the applications, synthesize a type for the function, and then pass off to synth_apps to iterate through all the arguments. *)
      let fn, locs, args = spine tm in
      let sfn, sty = synth ctx fn in
      synth_apps ctx { value = sfn; loc = fn.loc } sty locs args
  | Act (str, fa, x) ->
      let sx, ety = synth ctx x in
      let ex = Ctx.eval_term ctx sx in
      ( Act (sx, fa),
        act_ty ex ety fa ~err:(Low_dimensional_argument_of_degeneracy (str, cod_deg fa)) )
  | Asc (tm, ty) ->
      let cty = check Kinetic ctx ty (universe D.zero) in
      let ety = Ctx.eval_term ctx cty in
      let ctm = check Kinetic ctx tm ety in
      (ctm, ety)
  | Let (x, v, body) ->
      let sv, ty = synth ctx v in
      let tm = Ctx.eval_term ctx sv in
      let sbody, bodyty = synth (Ctx.ext_let ctx x { tm; ty }) body in
      (* The synthesized type of the body is also correct for the whole let-expression, because it was synthesized in a context where the variable is bound not just to its type but to its value. *)
      (Let (x, sv, sbody), bodyty)

(* Given a synthesized function and its type, and a list of arguments, check the arguments in appropriately-sized groups. *)
and synth_apps :
    type a b.
    (a, b) Ctx.t ->
    (b, kinetic) term located ->
    kinetic value ->
    Asai.Range.t option list ->
    a check located list ->
    (b, kinetic) term * kinetic value =
 fun ctx sfn sty locs args ->
  (* Failure of full_inst here is really a bug, not a user error: the user can try to check something against an abstraction as if it were a type, but our synthesis functions should never synthesize (say) a lambda-abstraction as if it were a type. *)
  let (Fullinst (fnty, tyargs)) = full_inst sty "synth_apps" in
  let afn, aty, alocs, aargs = synth_app ctx sfn fnty tyargs locs args in
  (* synth_app fails if there aren't enough arguments.  If it used up all the arguments, we're done; otherwise we continue with the rest of the arguments. *)
  match aargs with
  | [] -> (afn.value, aty)
  | _ :: _ -> synth_apps ctx afn aty alocs aargs

and synth_app :
    type a b n.
    (a, b) Ctx.t ->
    (b, kinetic) term located ->
    uninst ->
    (D.zero, n, n, normal) TubeOf.t ->
    Asai.Range.t option list ->
    a check located list ->
    (b, kinetic) term located * kinetic value * Asai.Range.t option list * a check located list =
 fun ctx sfn fnty tyargs locs args ->
  let module M = Monad.State (struct
    type t = Asai.Range.t option * Asai.Range.t option list * a check located list
  end) in
  (* To determine what to do, we inspect the (fully instantiated) *type* of the function being applied. *)
  match fnty with
  (* The obvious thing we can "apply" is an element of a pi-type. *)
  | Pi (_, doms, cods) -> (
      (* Ensure that the pi-type is (fully) instantiated at the right dimension. *)
      match compare (TubeOf.inst tyargs) (CubeOf.dim doms) with
      | Neq -> fatal (Dimension_mismatch ("applying function", TubeOf.inst tyargs, CubeOf.dim doms))
      | Eq ->
          (* Pick up the right number of arguments for the dimension, leaving the others for a later call to synth_app.  Then check each argument against the corresponding type in "doms", instantiated at the appropriate evaluated previous arguments, and evaluate it, producing Cubes of checked terms and values.  Since each argument has to be checked against a type instantiated at the *values* of the previous ones, we also store those in a hashtable as we go. *)
          let eargtbl = Hashtbl.create 10 in
          let [ cargs; eargs ], (newloc, rlocs, rest) =
            let open CubeOf.Monadic (M) in
            let open CubeOf.Infix in
            pmapM
              {
                map =
                  (fun fa [ dom ] ->
                    let open Monad.Ops (M) in
                    let* loc, ls, ts = M.get in
                    let* tm =
                      match (ls, ts) with
                      | _, [] | [], _ ->
                          with_loc loc @@ fun () -> fatal Not_enough_arguments_to_function
                      | l :: ls, t :: ts ->
                          let* () = M.put (l, ls, ts) in
                          return t in
                    let ty =
                      inst dom
                        (TubeOf.build D.zero
                           (D.zero_plus (dom_sface fa))
                           {
                             build =
                               (fun fc ->
                                 Hashtbl.find eargtbl (SFace_of (comp_sface fa (sface_of_tface fc))));
                           }) in
                    let ctm = check Kinetic ctx tm ty in
                    let tm = Ctx.eval_term ctx ctm in
                    Hashtbl.add eargtbl (SFace_of fa) { tm; ty };
                    return (ctm @: [ tm ]));
              }
              [ doms ] (Hlist.Cons (Cons Nil)) (sfn.loc, locs, args) in
          (* Evaluate cod at these evaluated arguments and instantiate it at the appropriate values of tyargs. *)
          let output = tyof_app cods tyargs eargs in
          ({ value = Term.App (sfn.value, cargs); loc = newloc }, output, rlocs, rest))
  (* We can also "apply" a higher-dimensional *type*, leading to a (further) instantiation of it.  Here the number of arguments must exactly match *some* integral instantiation. *)
  | UU n -> (
      (* Ensure that the universe is (fully) instantiated at the right dimension. *)
      match compare (TubeOf.inst tyargs) n with
      | Neq -> fatal (Dimension_mismatch ("instantiating type", TubeOf.inst tyargs, n))
      | Eq -> (
          match D.compare_zero n with
          | Zero -> fatal (Instantiating_zero_dimensional_type (PTerm (ctx, sfn.value)))
          | Pos pn ->
              (* We take enough arguments to instatiate a type of dimension n by one. *)
              let (Is_suc (m, msuc)) = suc_pos pn in
              let open TubeOf.Monadic (M) in
              let open TubeOf.Infix in
              (* We will need random access to the previously evaluated arguments, so we store them in a hashtable as we go. *)
              let eargtbl = Hashtbl.create 10 in
              let tyargs1 = TubeOf.pboundary (D.zero_plus m) msuc tyargs in
              (* What we really want, however, are two tubes of checked arguments *and* evaluated arguments. *)
              let [ cargs; eargs ], (newloc, rlocs, rest) =
                pmapM
                  {
                    map =
                      (fun fa [ tyarg ] ->
                        (* We iterate monadically with the list of available arguments in a state/maybe monad, taking one more argument every time we need it as long as there is one. *)
                        let open Monad.Ops (M) in
                        let* loc, ls, ts = M.get in
                        let* tm =
                          match (ls, ts) with
                          | [], _ | _, [] ->
                              with_loc loc @@ fun () -> fatal Not_enough_arguments_to_instantiation
                          | l :: ls, t :: ts ->
                              let* () = M.put (l, ls, ts) in
                              return t in
                        (* We check each such argument against the corresponding type instantiation argument, itself instantiated at the values of the appropriate previous arguments. *)
                        let fa = sface_of_tface fa in
                        let k = dom_sface fa in
                        let kargs =
                          TubeOf.build D.zero (D.zero_plus k)
                            {
                              build =
                                (fun fb ->
                                  Hashtbl.find eargtbl
                                    (SFace_of (comp_sface fa (sface_of_tface fb))));
                            } in
                        let ty = inst tyarg.tm kargs in
                        let ctm = check Kinetic ctx tm ty in
                        (* Then we evaluate it and assemble a normal version to store in the hashtbl, before returning the checked and evaluated versions. *)
                        let tm = Ctx.eval_term ctx ctm in
                        let ntm = { tm; ty } in
                        let () = Hashtbl.add eargtbl (SFace_of fa) ntm in
                        return (ctm @: [ ntm ]));
                  }
                  [ tyargs1 ] (Cons (Cons Nil)) (sfn.loc, locs, args) in
              (* The synthesized type *of* the instantiation is itself a full instantiation of a universe, at the instantiations of the type arguments at the evaluated term arguments.  This is computed by tyof_inst. *)
              ( { value = Term.Inst (sfn.value, cargs); loc = newloc },
                tyof_inst tyargs eargs,
                rlocs,
                rest )))
  (* Something that synthesizes a type that isn't a pi-type or a universe cannot be applied to anything, but this is a user error, not a bug. *)
  | _ ->
      with_loc sfn.loc @@ fun () ->
      fatal (Applying_nonfunction_nontype (PTerm (ctx, sfn.value), PUninst (ctx, fnty)))

(* Check a list of terms against the types specified in a telescope, evaluating the latter in a supplied environment and in the context of the previously checked terms, and instantiating them at values given in a tube. *)
and check_at_tel :
    type n a b c bc e.
    Constr.t ->
    (a, e) Ctx.t ->
    (n, b) env ->
    a check located list ->
    (b, c, bc) Telescope.t ->
    (D.zero, n, n, kinetic value list) TubeOf.t ->
    (n, bc) env * (n, (e, kinetic) term) CubeOf.t list =
 fun c ctx env tms tys tyargs ->
  match (tms, tys) with
  | [], Emp ->
      (* tyargs should consist of empty lists here, since it started out being the constructor arguments of the instantiation arguments. *)
      (env, [])
  | tm :: tms, Ext (_, ty, tys) ->
      let ety = eval_term env ty in
      let tyargtbl = Hashtbl.create 10 in
      let [ tyarg; tyargs ] =
        TubeOf.pmap
          {
            map =
              (fun fa [ tyargs ] ->
                match tyargs with
                | [] -> fatal (Anomaly "missing arguments in check_at_tel")
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
      let ctm = check Kinetic ctx tm ity in
      let ctms = TubeOf.mmap { map = (fun _ [ t ] -> readback_nf ctx t) } [ tyarg ] in
      let etm = Ctx.eval_term ctx ctm in
      let newenv, newargs =
        check_at_tel c ctx
          (Ext
             ( env,
               CubeOf.singleton (TubeOf.plus_cube (val_of_norm_tube tyarg) (CubeOf.singleton etm))
             ))
          tms tys tyargs in
      (newenv, TubeOf.plus_cube ctms (CubeOf.singleton ctm) :: newargs)
  | _ ->
      fatal
        (Wrong_number_of_arguments_to_constructor
           (c, List.length tms - N.to_int (Telescope.length tys)))

(* Given a raw telescope and a context, we can check it to produce a checked telescope and also a new context extended by that telescope. *)

type (_, _) checked_tel =
  | Checked_tel : ('b, 'd, 'bd) Telescope.t * ('ac, 'bd) Ctx.t -> ('ac, 'b) checked_tel

let rec check_tel : type a b c ac. (a, b) Ctx.t -> (a, c, ac) Raw.tel -> (ac, b) checked_tel =
 fun ctx tel ->
  match tel with
  | Emp -> Checked_tel (Emp, ctx)
  | Ext (x, ty, tys) ->
      let cty = check Kinetic ctx ty (universe D.zero) in
      let ety = Ctx.eval_term ctx cty in
      let _, newnfs = dom_vars (Ctx.length ctx) (CubeOf.singleton ety) in
      let ctx = Ctx.vis ctx (`Cube x) newnfs in
      let (Checked_tel (ctys, ctx)) = check_tel ctx tys in
      Checked_tel (Ext (x, cty, ctys), ctx)
