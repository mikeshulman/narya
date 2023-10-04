open Bwd
open Util
open Raw
open Value
open Term
open Dim
open Act
open Norm
open Equal
open Readback

(* Typechecking errors.  Once we have pretty-printing of terms, it will become useful for these to include data about the terms that generated the error.  Eventually we'll probably also want to include information about the location in the source. *)

module CheckErr = struct
  type t =
    | Not_enough_lambdas
    | Type_not_fully_instantiated
    | Unequal_synthesized_type
    | Record_has_degeneracy
    | Missing_field_in_struct
    | Checking_struct_against_nonrecord
    | No_such_constructor of Constr.t
    | Missing_instantiation_constructor
    | Unequal_indices
    | Checking_constructor_against_nondatatype
    | Checking_mismatch
    | No_such_constant of Constant.t
    | No_such_field of Field.t
    | Nonsynthesizing_argument_of_refl
    | Nonsynthesizing_argument_of_sym
    | Low_dimensional_argument_of_sym
    | Missing_arguments_of_symbol
    | Not_enough_arguments_to_function
    | Instantiating_zero_dimensional_type
    | Not_enough_arguments_to_instantiation
    | Applying_nonfunction_nontype
    | Wrong_number_of_arguments_to_constructor

  let to_string = function
    | Not_enough_lambdas -> "Not enough variables for a higher-dimensional abstraction"
    | Type_not_fully_instantiated ->
        "Can't check against a non-fully-instantiated higher-dimensional type"
    | Unequal_synthesized_type ->
        "Term synthesized a different type than it's being checked against"
    | Record_has_degeneracy ->
        "Can't check a struct against a record with a nonidentity degeneracy applied"
    | Missing_field_in_struct -> "Missing record field in struct"
    | Checking_struct_against_nonrecord -> "Attempting to check struct against non-record type"
    | No_such_constructor c -> "Datatype has no constructor named " ^ Constr.to_string c
    | Missing_instantiation_constructor ->
        "Instantiation arguments of datatype must be matching constructors"
    | Unequal_indices -> "Indices of constructor application don't match those of datatype instance"
    | Checking_constructor_against_nondatatype ->
        "Attempting to check constructor against non-datatype"
    | Checking_mismatch -> "Checking term doesn't check against that type"
    | No_such_constant c -> "Unbound variable: " ^ Constant.to_string c
    | No_such_field f -> "Record has no field named " ^ Field.to_string f
    | Nonsynthesizing_argument_of_refl -> "Argument of refl must synthesize"
    | Nonsynthesizing_argument_of_sym -> "Argument of sym much synthesize"
    | Low_dimensional_argument_of_sym -> "Argument of sym must be at least two-dimensional"
    | Missing_arguments_of_symbol -> "Missing arguments of symbol"
    | Not_enough_arguments_to_function ->
        "Not enough arguments for a higher-dimensional function application"
    | Instantiating_zero_dimensional_type -> "Can't apply/instantiate a zero-dimensional type"
    | Not_enough_arguments_to_instantiation ->
        "Not enough arguments to instantiate a higher-dimensional type"
    | Applying_nonfunction_nontype -> "Attempt to apply/instantiate a non-function, non-type"
    | Wrong_number_of_arguments_to_constructor -> "Wrong number of arguments to constructor"
end

module Err = Monad.Error (CheckErr)
open Monad.Ops (Err)

let ( <|> ) (x : 'a option) (e : CheckErr.t) : 'a Err.t = Option.to_result ~none:e x

(* Look through a specified number of lambdas to find an inner body. *)
let rec lambdas : type a b ab. (a, b, ab) N.plus -> a check -> ab check Err.t =
 fun ab tm ->
  match (ab, tm) with
  | Zero, _ -> return tm
  | Suc _, Lam body -> lambdas (N.suc_plus'' ab) body
  (* Not enough lambdas.  TODO: We could eta-expand in this case, as long as we've picked up at least one lambda. *)
  | _ -> Error Not_enough_lambdas

(* Slurp up an entire application spine *)
let spine : type a. a synth -> a synth * a check list =
 fun tm ->
  let rec spine tm args =
    match tm with
    | Raw.App (fn, arg) -> spine fn (arg :: args)
    | _ -> (tm, args) in
  spine tm []

let rec check : type a. a Ctx.t -> a check -> value -> a term Err.t =
 fun ctx tm ty ->
  (* If the "type" is not a type here, or not fully instantiated, that's a user error, not a bug. *)
  let* (Fullinst (uty, tyargs)) = full_inst_opt ty <|> Type_not_fully_instantiated in
  match (tm, uty) with
  | Synth stm, _ ->
      let* sval, sty = synth ctx stm in
      let* () = equal_val (Ctx.level ctx) sty ty <|> Unequal_synthesized_type in
      return sval
  | Lam _, Pi (doms, cods) -> (
      let m = CubeOf.dim doms in
      match compare (TubeOf.inst tyargs) m with
      | Neq -> raise (Failure "Dimension mismatch checking lambda")
      | Eq ->
          let Eq = D.plus_uniq (TubeOf.plus tyargs) (D.zero_plus m) in
          (* Slurp up the right number of lambdas for the dimension of the pi-type, and pick up the body inside them. *)
          let (Faces dom_faces) = count_faces (CubeOf.dim doms) in
          let (Plus af) = N.plus (faces_out dom_faces) in
          let* body = lambdas af tm in
          (* Extend the context by one variable for each type in doms, instantiated at the appropriate previous ones. *)
          let _, newargs, newnfs, _ = dom_vars (Ctx.level ctx) doms in
          let ctx = CubeOf.flatten_append ctx newnfs dom_faces af in
          (* Apply and instantiate the codomain to those arguments to get a type to check the body at. *)
          let output = tyof_app cods tyargs newargs in
          let* cbody = check ctx body output in
          return (Term.Lam (Bind (dom_faces, af, cbody))))
  | Struct tms, Canonical (name, _, ins) -> (
      (* We don't need to name the arguments of Canonical here because tyof_field, called below, uses them. *)
      match Hashtbl.find Global.constants name with
      | Record { fields; _ } ->
          let* () = is_id_perm (perm_of_ins ins) <|> Record_has_degeneracy in
          let dim = cod_left_ins ins in
          let module (* The type of each record field, at which we check the corresponding field supplied in the struct, is the type associated to that field name in general, evaluated at the supplied parameters and at "the term itself".  We don't have the whole term available while typechecking, of course, but we can build a version of it that contains all the previously typechecked fields, which is all we need for a well-typed record.  So we iterate through the fields (in order) using a state monad as well that accumulates the previously typechecked and evaluated fields. *)
          M =
            Monad.StateT
              (Err)
              (struct
                type t = a term Field.Map.t * value Field.Map.t
              end)
          in
          let open Mlist.Monadic (M) in
          (* We have to accumulate the evaluated terms for use as we go in typechecking, but we throw them away at the end.  (As usual, that seems wasteful.) *)
          let* (), (ctms, _) =
            miterM
              (fun [ (fld, _) ] ->
                let open Monad.Ops (M) in
                let* ctms, etms = M.get in
                let prev_etm = Value.Struct (etms, zero_ins dim) in
                let ety = tyof_field prev_etm ty fld in
                let* tm = M.stateless (Field.Map.find_opt fld tms <|> Missing_field_in_struct) in
                let* ctm = M.stateless (check ctx tm ety) in
                let etm = Ctx.eval ctx ctm in
                M.put (Field.Map.add fld ctm ctms, Field.Map.add fld etm etms))
              [ fields ]
              (Field.Map.empty, Field.Map.empty) in
          return (Struct ctms)
      | _ -> Error Checking_struct_against_nonrecord)
  | Constr (constr, args), Canonical (name, ty_params_indices, ins) -> (
      (* The insertion should always be trivial, since datatypes are always 0-dimensional. *)
      let dim = TubeOf.inst tyargs in
      match compare (cod_left_ins ins) dim with
      | Neq -> raise (Failure "Dimension mismatch checking constr")
      | Eq -> (
          (* We don't need the *types* of the parameters or indices, which are stored in the type of the constant name.  ty_params_indices contains the *values* of the parameters and indices of this instance of the datatype, while tyargs (defined by full_inst, way above) contains the instantiation arguments of this instance of the datatype. *)
          match Hashtbl.find Global.constants name with
          (* We do need the constructors of the datatype, as well as its *number* of parameters and indices. *)
          | Data { constrs; params; indices } -> (
              match is_id_perm (perm_of_ins ins) with
              | None -> raise (Failure "Datatypes with degeneracy shouldn't exist")
              | Some () ->
                  (* The datatype must contain a constructor with our current name. *)
                  let* (Constr { args = constr_arg_tys; indices = constr_indices }) =
                    Constr.Map.find_opt constr constrs <|> No_such_constructor constr in
                  (* We split the values of the parameters and the indices, putting the parameters into the environment, and keeping the indices for later comparison. *)
                  let env, ty_indices =
                    take_canonical_args (Emp dim) ty_params_indices (N.zero_plus params) indices
                  in
                  (* To typecheck a higher-dimensional instance of our constructor constr at the datatype, all the instantiation arguments must also be applications of lower-dimensional versions of that same constructor.  We check this, and extract the arguments of those lower-dimensional constructors as a tube of lists. *)
                  let open TubeOf.Monadic (Err) in
                  let* tyarg_args =
                    mmapM
                      {
                        map =
                          (fun fa [ tm ] ->
                            match tm.tm with
                            | Constr (tmname, n, tmargs) ->
                                let* () =
                                  if tmname = constr then return ()
                                  else Error Missing_instantiation_constructor in
                                (* Assuming the instantiation is well-typed, we must have n = dom_tface fa.  I'd like to check that, but for some reason, matching this compare against Eq claims that the type variable n would escape its scope. *)
                                let _ = compare n (dom_tface fa) in
                                return
                                  (Bwd.fold_right
                                     (fun a args -> CubeOf.find a (id_sface n) :: args)
                                     tmargs [])
                            | _ -> Error Missing_instantiation_constructor);
                      }
                      [ tyargs ] in
                  (* Now we evaluate each argument *type* of the constructor at the parameters and the previous evaluated argument *values*, check each argument value against the corresponding argument type, and then evaluate it and add it to the environment (to substitute into the subsequent types, and also later to the indices). *)
                  let* env, newargs =
                    check_tel ctx env (Bwd.to_list args) constr_arg_tys tyarg_args in
                  (* Now we substitute all those evaluated arguments into the indices, to get the actual (higher-dimensional) indices of our constructor application. *)
                  let constr_indices =
                    Bwv.map
                      (fun ix ->
                        CubeOf.build dim { build = (fun fa -> eval (Act (env, op_of_sface fa)) ix) })
                      constr_indices in
                  (* The last thing to do is check that these indices are equal to those of the type we are checking against.  (So a constructor application "checks against the parameters but synthesizes the indices" in some sense.)  I *think* it should suffice to check the top-dimensional ones, the lower-dimensional ones being automatic.  For now, we check all of them, throwing an exception in case I was wrong about that.  *)
                  let open Bwv.Monadic (Err) in
                  let* () =
                    miterM
                      (fun [ t1s; t2s ] ->
                        let open CubeOf.Monadic (Err) in
                        miterM
                          {
                            it =
                              (fun fa [ t1; t2 ] ->
                                match equal_at (Ctx.level ctx) t1 t2.tm t2.ty with
                                | Some () -> return ()
                                | None -> (
                                    match is_id_sface fa with
                                    | Some () -> Error Unequal_indices
                                    | None ->
                                        raise (Failure "Mismatching lower-dimensional constructors")
                                    ));
                          }
                          [ t1s; t2s ])
                      [ constr_indices; ty_indices ] in
                  return (Constr (constr, dim, Bwd.of_list newargs)))
          | _ -> Error Checking_constructor_against_nondatatype))
  | _ -> Error Checking_mismatch

and synth : type a. a Ctx.t -> a synth -> (a term * value) Err.t =
 fun ctx tm ->
  match tm with
  | Var v -> return (Term.Var v, (snd (Bwv.nth v ctx)).ty)
  | Const name ->
      let* ty = Hashtbl.find_opt Global.types name <|> No_such_constant name in
      return (Const name, eval (Emp D.zero) ty)
  | Field (tm, fld) ->
      let* stm, sty = synth ctx tm in
      (* To take a field of something, the type of the something must be a record-type that contains such a field, possibly substituted to a higher dimension and instantiated. *)
      let etm = Ctx.eval ctx stm in
      let* newty = tyof_field_opt etm sty fld <|> No_such_field fld in
      return (Field (stm, fld), newty)
  | Symbol (UU, Zero, Emp) -> return (Term.UU D.zero, universe D.zero)
  | Pi (dom, cod) ->
      (* User-level pi-types are always dimension zero, so the domain must be a zero-dimensional type. *)
      let* cdom = check ctx dom (universe D.zero) in
      let edom = Ctx.eval ctx cdom in
      let* ccod = check (Ctx.ext ctx edom) cod (universe D.zero) in
      return (pi cdom ccod, universe D.zero)
  | App _ ->
      (* If there's at least one application, we slurp up all the applications, synthesize a type for the function, and then pass off to synth_apps to iterate through all the arguments. *)
      let fn, args = spine tm in
      let* sfn, sty = synth ctx fn in
      synth_apps ctx sfn sty args
  | Symbol (Refl, Zero, Snoc (Emp, x)) -> (
      match x with
      | Synth x ->
          let* sx, ety = synth ctx x in
          let ex = Ctx.eval ctx sx in
          return (Act (sx, refl), act_ty ex ety refl)
      | _ -> Error Nonsynthesizing_argument_of_refl)
  | Symbol (Sym, Zero, Snoc (Emp, x)) -> (
      match x with
      | Synth x -> (
          let* sx, ety = synth ctx x in
          let ex = Ctx.eval ctx sx in
          try
            let symty = act_ty ex ety sym in
            return (Act (sx, sym), symty)
          with Invalid_uninst_action -> Error Low_dimensional_argument_of_sym)
      | _ -> Error Nonsynthesizing_argument_of_sym)
  (* If a symbol isn't applied to enough arguments yet, it doesn't typecheck. *)
  | Symbol (_, Suc _, _) -> Error Missing_arguments_of_symbol
  | Asc (tm, ty) ->
      let* cty = check ctx ty (universe D.zero) in
      let ety = Ctx.eval ctx cty in
      let* ctm = check ctx tm ety in
      return (ctm, ety)
  | Let (v, body) ->
      let* sv, ty = synth ctx v in
      let tm = Ctx.eval ctx sv in
      let* sbody, bodyty = synth (Bwv.Snoc (ctx, (None, { tm; ty }))) body in
      (* The synthesized type of the body is also correct for the whole let-expression, because it was synthesized in a context where the variable is bound not just to its type but to its value. *)
      return (Let (sv, sbody), bodyty)

(* Given a synthesized function and its type, and a list of arguments, check the arguments in appropriately-sized groups. *)
and synth_apps : type a. a Ctx.t -> a term -> value -> a check list -> (a term * value) Err.t =
 fun ctx sfn sty args ->
  (* Failure of full_inst here is really a bug, not a user error: the user can try to check something against an abstraction as if it were a type, but our synthesis functions should never synthesize (say) a lambda-abstraction as if it were a type. *)
  let (Fullinst (fnty, tyargs)) = full_inst sty "synth_apps" in
  let* afn, aty, aargs = synth_app ctx sfn fnty tyargs args in
  (* synth_app fails if there aren't enough arguments.  If it used up all the arguments, we're done; otherwise we continue with the rest of the arguments. *)
  match aargs with
  | [] -> return (afn, aty)
  | _ :: _ -> synth_apps ctx afn aty aargs

and synth_app :
    type a n.
    a Ctx.t ->
    a term ->
    uninst ->
    (D.zero, n, n, normal) TubeOf.t ->
    a check list ->
    (a term * value * a check list) Err.t =
 fun ctx sfn fnty tyargs args ->
  let module M =
    Monad.StateT
      (Err)
      (struct
        type t = a check list
      end)
  in
  (* To determine what to do, we inspect the (fully instantiated) *type* of the function being applied. *)
  match fnty with
  (* The obvious thing we can "apply" is an element of a pi-type. *)
  | Pi (doms, cods) -> (
      (* Ensure that the pi-type is (fully) instantiated at the right dimension. *)
      match compare (TubeOf.inst tyargs) (CubeOf.dim doms) with
      | Neq -> raise (Failure "Dimension mismatch applying function")
      | Eq ->
          (* Pick up the right number of arguments for the dimension, leaving the others for a later call to synth_app.  Then check each argument against the corresponding type in "doms", instantiated at the appropriate evaluated previous arguments, and evaluate it, producing Cubes of checked terms and values.  Since each argument has to be checked against a type instantiated at the *values* of the previous ones, we also store those in a hashtable as we go. *)
          let eargtbl = Hashtbl.create 10 in
          let* [ cargs; eargs ], rest =
            let open CubeOf.Monadic (M) in
            let open CubeOf.Infix in
            pmapM
              {
                map =
                  (fun fa [ dom ] ->
                    let open Monad.Ops (M) in
                    let* ts = M.get in
                    let* tm =
                      match ts with
                      | [] -> M.stateless (Error Not_enough_arguments_to_function)
                      | t :: ts ->
                          let* () = M.put ts in
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
                    let* ctm = M.stateless (check ctx tm ty) in
                    let tm = Ctx.eval ctx ctm in
                    Hashtbl.add eargtbl (SFace_of fa) { tm; ty };
                    return (ctm @: [ tm ]));
              }
              [ doms ] (Cons (Cons Nil)) args in
          (* Evaluate cod at these evaluated arguments and instantiate it at the appropriate values of tyargs. *)
          let output = tyof_app cods tyargs eargs in
          return (Term.App (sfn, cargs), output, rest))
  (* We can also "apply" a higher-dimensional *type*, leading to a (further) instantiation of it.  Here the number of arguments must exactly match *some* integral instantiation. *)
  | UU n -> (
      (* Ensure that the universe is (fully) instantiated at the right dimension. *)
      match compare (TubeOf.inst tyargs) n with
      | Neq -> raise (Failure "Dimension mismatch instantiating type")
      | Eq -> (
          match D.compare_zero n with
          | Zero -> Error Instantiating_zero_dimensional_type
          | Pos pn ->
              (* We take enough arguments to instatiate a type of dimension n by one. *)
              let (Is_suc (m, msuc)) = suc_pos pn in
              let open TubeOf.Monadic (M) in
              let open TubeOf.Infix in
              (* We will need random access to the previously evaluated arguments, so we store them in a hashtable as we go. *)
              let eargtbl = Hashtbl.create 10 in
              let tyargs1 = TubeOf.pboundary (D.zero_plus m) msuc tyargs in
              (* What we really want, however, are two tubes of checked arguments *and* evaluated arguments. *)
              let* [ cargs; eargs ], rest =
                pmapM
                  {
                    map =
                      (fun fa [ tyarg ] ->
                        (* We iterate monadically with the list of available arguments in a state/maybe monad, taking one more argument every time we need it as long as there is one. *)
                        let open Monad.Ops (M) in
                        let* ts = M.get in
                        let* tm =
                          match ts with
                          | [] -> M.stateless (Error Not_enough_arguments_to_instantiation)
                          | t :: ts ->
                              let* () = M.put ts in
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
                        let* ctm = M.stateless (check ctx tm ty) in
                        (* Then we evaluate it and assemble a normal version to store in the hashtbl, before returning the checked and evaluated versions. *)
                        let tm = Ctx.eval ctx ctm in
                        let ntm = { tm; ty } in
                        let () = Hashtbl.add eargtbl (SFace_of fa) ntm in
                        return (ctm @: [ ntm ]));
                  }
                  [ tyargs1 ] (Cons (Cons Nil)) args in
              (* The synthesized type *of* the instantiation is itself a full instantiation of a universe, at the instantiations of the type arguments at the evaluated term arguments.  This is computed by tyof_inst. *)
              return (Term.Inst (sfn, cargs), tyof_inst tyargs eargs, rest)))
  (* Something that synthesizes a type that isn't a pi-type or a universe cannot be applied to anything, but this is a user error, not a bug. *)
  | _ -> Error Applying_nonfunction_nontype

(* Check a list of terms against the types specified in a telescope, evaluating the latter in a supplied environment and in the context of the previously checked terms, and instantiating them at values given in a tube. *)
and check_tel :
    type n a b c bc.
    a Ctx.t ->
    (n, b) env ->
    a check list ->
    (b, c, bc) Telescope.t ->
    (D.zero, n, n, value list) TubeOf.t ->
    ((n, bc) env * (n, a term) CubeOf.t list) Err.t =
 fun ctx env tms tys tyargs ->
  match (tms, tys) with
  | [], Emp ->
      (* tyargs should consist of empty lists here, since it started out being the constructor arguments of the instantiation arguments. *)
      return (env, [])
  | tm :: tms, Ext (ty, tys) ->
      let ety = eval env ty in
      let tyargtbl = Hashtbl.create 10 in
      let [ tyarg; tyargs ] =
        TubeOf.pmap
          {
            map =
              (fun fa [ tyargs ] ->
                match tyargs with
                | [] -> raise (Failure "Missing arguments in check_tel")
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
                    Hashtbl.add tyargtbl (SFace_of fa) argnorm;
                    [ argnorm; argrest ]);
          }
          [ tyargs ] (Cons (Cons Nil)) in
      let ity = inst ety tyarg in
      let* ctm = check ctx tm ity in
      let coctx = Coctx.of_ctx ctx in
      let ctms = TubeOf.mmap { map = (fun _ [ t ] -> readback_nf coctx t) } [ tyarg ] in
      let etm = Ctx.eval ctx ctm in
      let* newenv, newargs =
        check_tel ctx
          (Ext (env, TubeOf.plus_cube (val_of_norm_tube tyarg) (CubeOf.singleton etm)))
          tms tys tyargs in
      return (newenv, TubeOf.plus_cube ctms (CubeOf.singleton ctm) :: newargs)
  | _ -> Error Wrong_number_of_arguments_to_constructor
