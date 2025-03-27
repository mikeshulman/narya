open Bwd
open Util
open Perhaps
open Tbwd
open Reporter
open Term
open Value
open Domvars
open Raw
open Dim
open Act
open Norm
open Equal
open Readback
open Degctx
open Printable
open Asai.Range
include Status

let discard : type a. a -> unit = fun _ -> ()

module OracleData = struct
  type question = Ask : ('a, 'b) Ctx.t * kinetic value -> question
  type answer = (unit, Code.t) Result.t
end

module Oracle = Query.Make (OracleData)

(* Check that a given value is a zero-dimensional type family (something where an indexed datatype could live) and return the length of its domain telescope (the number of indices).  Unfortunately I don't see an easy way to do this without essentially going through all the same steps of extending the context that we would do to check something at that type family.  Also check whether all of its domain types are either discrete or belong to the given set of constants. *)
let rec typefam : type a b.
    ?discrete:unit Constant.Map.t -> (a, b) Ctx.t -> kinetic value -> int * bool =
 fun ?discrete ctx ty ->
  match view_type ~severity:Asai.Diagnostic.Error ty "typefam" with
  | UU tyargs -> (
      match D.compare (TubeOf.inst tyargs) D.zero with
      | Eq -> (0, true)
      | Neq -> fatal (Unimplemented "higher-dimensional datatypes"))
  | Pi (x, doms, cods, tyargs) -> (
      (* In practice, these dimensions will always be zero also if the function succeeds, otherwise the eventual output would have to be higher-dimensional too.  But it doesn't hurt to be more general, and will require less change if we eventually implement higher-dimensional datatypes. *)
      match D.compare (TubeOf.inst tyargs) (CubeOf.dim doms) with
      | Eq ->
          let newargs, newnfs = dom_vars (Ctx.length ctx) doms in
          let output = tyof_app cods tyargs newargs in
          let n, d = typefam ?discrete (Ctx.cube_vis ctx x newnfs) output in
          let disc =
            (* For indices of discrete datatypes, we only allow zero-dimensional pi-types. *)
            match D.compare (CubeOf.dim doms) D.zero with
            | Eq -> is_discrete ?discrete (CubeOf.find_top doms)
            | Neq -> false in
          (n + 1, d && disc)
      | Neq -> fatal (Dimension_mismatch ("typefam", TubeOf.inst tyargs, CubeOf.dim doms)))
  | _ -> fatal (Checking_canonical_at_nonuniverse ("datatype", PVal (ctx, ty)))

let rec motive_of_family : type a b.
    (a, b) Ctx.t -> kinetic value -> kinetic value -> (b, kinetic) term =
 fun ctx tm ty ->
  let module F = struct
    type (_, _, _, _) t =
      | Rbtm : ('left, kinetic) term -> ('left, 'c, 'any, ('left, D.zero) snoc) t
  end in
  let module FCube = Icube (F) in
  let module C = struct
    type _ t = Any_ctx : ('a, 'c) Ctx.t -> 'c t
  end in
  let module T = struct
    type 'c t = ('c, kinetic) term
  end in
  let module MC = FCube.Traverse (C) in
  let module MT = FCube.Traverse (T) in
  let folder : type left m any right.
      (left, m, any, right) F.t -> right T.t -> left T.t * (left, m, any, right) F.t =
   fun (Rbtm dom) cod -> (Pi (None, CubeOf.singleton dom, CodCube.singleton cod), Rbtm dom) in
  let builder : type left n m.
      string option ->
      (n, Binding.t) CubeOf.t ->
      (m, n) sface ->
      left C.t ->
      (left, m, b) MC.fwrap_left =
   fun x newnfs fa (Any_ctx ctx) ->
    let v = CubeOf.find newnfs fa in
    let cv = readback_val ctx (Binding.value v).ty in
    Fwrap (Rbtm cv, Any_ctx (Ctx.cube_vis ctx x (CubeOf.singleton v))) in
  match view_type ty "motive_of_family" with
  | Pi (x, doms, cods, tyargs) ->
      let newvars, newnfs = dom_vars (Ctx.length ctx) doms in
      let newtm = apply_term tm newvars in
      (* We extend the context, not by the cube of types of newnfs, but by its elements one at a time as singletons.  This is because we want eventually to construct a 0-dimensional pi-type.  As we go, we also read back thesetypes and store them to later take the pi-type over.  Since they are all in different contexts, and we need to keep track of the type-indexed checked length of those contexts to ensure the later pis are well-typed, we use an indexed cube indexed over Tbwds. *)
      let (Wrap (newdoms, Any_ctx newctx)) =
        MC.build_left (CubeOf.dim newnfs)
          { build = (fun fa ctx -> builder x newnfs fa ctx) }
          (Any_ctx ctx) in
      let motive = motive_of_family newctx newtm (tyof_app cods tyargs newvars) in
      let motive, _ = MT.fold_map_right { foldmap = (fun _ x y -> folder x y) } newdoms motive in
      motive
  | UU tyargs ->
      (* This is similar, except that we add the datatype itself to the instantiation argument to get the cube of domains, and take a pi over the 0-dimensional universe rather than a recursive call. *)
      let doms = TubeOf.plus_cube (val_of_norm_tube tyargs) (CubeOf.singleton tm) in
      let _, newnfs = dom_vars (Ctx.length ctx) doms in
      let (Wrap (newdoms, _)) =
        MC.build_left (CubeOf.dim newnfs)
          { build = (fun fa ctx -> builder None newnfs fa ctx) }
          (Any_ctx ctx) in
      let motive, _ =
        MT.fold_map_right { foldmap = (fun _ x y -> folder x y) } newdoms (UU D.zero) in
      motive
  | _ -> fatal (Anomaly "non-family in motive_of_family")

type (_, _, _) vars_of_names =
  | Vars :
      ('a, 'b, 'abc) N.plus * (N.zero, 'n, string option, 'b) NICubeOf.t
      -> ('a, 'abc, 'n) vars_of_names

let vars_of_names : type a c abc n.
    Asai.Range.t option -> n D.t -> (a, c, abc) Namevec.t -> (a, abc, n) vars_of_names =
 fun loc dim xs ->
  let module S = struct
    type 'b t = Ok : (a, 'b, 'ab) N.plus * ('ab, 'c, abc) Namevec.t -> 'b t | Missing of int
  end in
  let module Build = NICubeOf.Traverse (S) in
  match
    Build.build_left dim
      {
        build =
          (fun _ -> function
            | Ok (ab, x :: xs) -> Fwrap (NFamOf x, Ok (Suc ab, xs))
            | Ok _ -> Fwrap (NFamOf None, Missing (-1))
            | Missing j -> Fwrap (NFamOf None, Missing (j - 1)));
      }
      (Ok (Zero, xs))
  with
  | Wrap (names, Ok (ab, [])) -> Vars (ab, names)
  | Wrap (_, Ok (_, xs)) -> fatal ?loc (Wrong_boundary_of_record (Fwn.to_int (Namevec.length xs)))
  | Wrap (_, Missing j) -> fatal ?loc (Wrong_boundary_of_record j)

(* Slurp up an entire application spine.  Returns the function, and all the arguments, where each argument is paired with the location of its application.  So spine "f x y" would return "f" (located) along with [(location of "f x", "x" (located)); (location of "f x y", "y" (located))]. *)
let spine : type a.
    a synth located ->
    a synth located
    * (Asai.Range.t option * a check located * [ `Implicit | `Explicit ] located) list =
 fun tm ->
  let rec spine tm args =
    match tm.value with
    | Raw.App (fn, arg, impl) -> spine fn ((tm.loc, arg, impl) :: args)
    | _ -> (tm, args) in
  spine tm []

(* Temporarily define a given head (constant or meta) to be a given value, in executing a callback.  However, if an error has occurred earlier in typechecking other parts of it, then instead bind that head to an error value that doesn't allow it to be used. *)
let run_with_definition : type a c.
    a potential_head -> (a, potential) term -> Code.t Asai.Diagnostic.t Bwd.t -> (unit -> c) -> c =
 fun head tm errs f ->
  match (head, errs) with
  (* In the case of an error, we bind the head to the error "Accumulated Emp".  That has the effect that accesses to it fail, but aren't displayed to the user as anything, since what's really going on is that we refuse to even try to typecheck later parts of a term that depend on previous parts that already failed, and this "error" is just detecting that dependence. *)
  (* We ignore the substituted dimension of the head, since this is really setting the *global* definition, which is not substituted. *)
  | Constant (c, _), Emp -> Global.with_definition c (Global.Defined tm) f
  | Constant (c, _), Snoc _ -> Global.without_definition c (Accumulated ("dependence", Emp)) f
  | Meta (m, _), Emp -> Global.with_meta_definition m tm f
  | Meta (m, _), Snoc _ -> Global.without_meta_definition m (Accumulated ("dependence", Emp)) f

let unless_error (v : 'a) (err : 'b Bwd.t) : ('a, Code.t) Result.t =
  match err with
  | Emp -> Ok v
  | Snoc _ -> Error (Accumulated ("dependence", Emp))

(* A "checkable branch" stores all the information about a branch in a match, both that coming from what the user wrote in the match and what is stored as properties of the datatype.  *)
type (_, _, _) checkable_branch =
  | Checkable_branch : {
      xs : ('a, 'c, 'ac) Namevec.t;
      (* If the body is None, that means the user omitted this branch.  (That might be ok, if it can be refuted by a pattern variable belonging to an empty type.) *)
      body : 'ac check located option;
      env : ('m, 'b) env;
      argtys : ('b, 'c, 'bc) Telescope.t;
      index_terms : (('bc, kinetic) term, 'ij) Vec.t;
    }
      -> ('a, 'm, 'ij) checkable_branch

(* A "synthable branch" is similar, but records the fact that the user gave a synthesizing term.  *)
type (_, _, _) synthable_branch =
  | Synthable_branch : {
      xs : ('a, 'c, 'ac) Namevec.t;
      body : 'ac synth located;
      env : ('m, 'b) env;
      argtys : ('b, 'c, 'bc) Telescope.t;
      index_terms : (('bc, kinetic) term, 'ij) Vec.t;
    }
      -> ('a, 'm, 'ij) synthable_branch

(* This preprocesssing step pairs each user-provided branch with the corresponding constructor information from the datatype. *)
let merge_branches head user_branches data_constrs =
  let user_branches, leftovers =
    Bwd.fold_left
      (fun (userbrs, databrs) (constr, Branch ({ value = xs; loc }, body)) ->
        (* We check at the preprocessing stage that there are no duplicate constructors in the match. *)
        if Abwd.mem constr userbrs then fatal ?loc (Duplicate_constructor_in_match constr);
        let databrs, databr = Abwd.extract constr databrs in
        let (Value.Dataconstr { env; args = argtys; indices = index_terms }) =
          match databr with
          | Some db -> db
          | None -> fatal ?loc (No_such_constructor_in_match (phead head, constr)) in
        (* We also check during preprocessing that the user has supplied the right number of pattern variable arguments to the constructor.  The positive result of this check is then recorded in the common existential types bound by Checkable_branch. *)
        match Fwn.compare (Namevec.length xs) (Telescope.length argtys) with
        | Neq ->
            fatal ?loc
              (Wrong_number_of_arguments_to_pattern
                 (constr, Fwn.to_int (Namevec.length xs) - Fwn.to_int (Telescope.length argtys)))
        | Eq ->
            let br = Checkable_branch { xs; body = Some body; env; argtys; index_terms } in
            (Snoc (userbrs, (constr, br)), databrs))
      (Bwd.Emp, data_constrs) user_branches in
  (* If there are any constructors in the datatype left over that the user didn't supply branches for, we add them to the list at the end.  They will be tested for refutability. *)
  Bwd.prepend user_branches
    (Bwd_extra.to_list_map
       (fun (c, Value.Dataconstr { env; args = argtys; indices = index_terms }) ->
         let b = Telescope.length argtys in
         let (Bplus plus_args) = Raw.Indexed.bplus b in
         let xs = Namevec.none plus_args in
         (c, Checkable_branch { xs; body = None; env; argtys; index_terms }))
       leftovers)

exception Case_tree_construct_in_let

(* The output of checking a telescope includes an extended context. *)
type (_, _, _, _) checked_tel =
  | Checked_tel : ('b, 'c, 'bc) Telescope.t * ('ac, 'bc) Ctx.t -> ('a, 'b, 'c, 'ac) checked_tel

(* A telescope of metavariables instead of types.  Created from a telescope of types by make_letrec_metas. *)
type (_, _, _) meta_tel =
  | Nil : ('b, Fwn.zero, 'b) meta_tel
  | Ext :
      string option * ('a, 'b, potential) Meta.t * (('b, D.zero) snoc, 'c, 'bc) meta_tel
      -> ('b, 'c Fwn.suc, 'bc) meta_tel

(* Check a term or case tree (depending on the energy: terms are kinetic, case trees are potential).  The ?discrete parameter is supplied if the term we are currently checking might be a discrete datatype, in which case it is a set of all the currently-being-defined mutual constants.  Most term-formers are nondiscrete, so they can just ignore this argument and make their recursive calls without it. *)
let rec check : type a b s.
    ?discrete:unit Constant.Map.t ->
    (b, s) status ->
    (a, b) Ctx.t ->
    a check located ->
    kinetic value ->
    (b, s) term =
 fun ?discrete status ctx tm ty ->
  let go () : (b, s) term =
    (* If the "type" is not a type here, or not fully instantiated, that's a user error, not a bug. *)
    let severity = Asai.Diagnostic.Error in
    match (tm.value, status) with
    (* A Let is a "synthesizing" term so that it *can* synthesize, but in checking position it checks instead. *)
    | Synth (Let (x, v, body)), _ ->
        let clet, Not_some = synth_or_check_let status ctx x v body (Some ty) in
        clet
    | Synth (Letrec (vtys, vs, body)), _ ->
        let clet, Not_some = synth_or_check_letrec status ctx vtys vs body (Some ty) in
        clet
    (* An action can always synthesize, but can also check if its degeneracy is a pure permutation, since then the type of the argument can be inferred by applying the inverse permutation to the ambient type. *)
    | Synth (Act (str, fa, x) as stm), _ -> (
        match perm_of_deg fa with
        | None -> check_of_synth status ctx stm tm.loc ty
        | Some pfa ->
            let fainv = deg_of_perm (perm_inv pfa) in
            Reporter.try_with ~fatal:(fun d ->
                (* If the user has given a symmetrized term that synthesizes but doesn't match the checking type, we want the error reported to be Unequal_synthesized_type.  So we fall back to synthesizing if the checking type doesn't symmetrize.  *)
                match d.message with
                | Low_dimensional_argument_of_degeneracy _ ->
                    check_of_synth status ctx stm tm.loc ty
                | _ -> fatal_diagnostic d)
            @@ fun () ->
            let ty_fainv =
              gact_ty None ty fainv ~err:(Low_dimensional_argument_of_degeneracy (str, cod_deg fa))
            in
            (* A pure permutation shouldn't ever be locking, but we may as well keep this here for consistency.  *)
            let ctx = if locking fa then Ctx.lock ctx else ctx in
            let cx = check (Kinetic `Nolet) ctx x ty_fainv in
            realize status (Term.Act (cx, fa)))
    | Lam ({ value = x; _ }, cube, body), _ -> (
        match view_type ~severity ty "typechecking lambda" with
        | Pi (_, doms, cods, tyargs) -> (
            (* TODO: Move this into a helper function, it's too long to go in here. *)
            let m = CubeOf.dim doms in
            (* A zero-dimensional parameter that is a discrete type doesn't block discreteness, but others do. *)
            let discrete =
              match D.compare m D.zero with
              | Eq -> if is_discrete ?discrete (CubeOf.find_top doms) then discrete else None
              | Neq -> None in
            let Eq = D.plus_uniq (TubeOf.plus tyargs) (D.zero_plus m) in
            (* Extend the context by one variable for each type in doms, instantiated at the appropriate previous ones. *)
            let newargs, newnfs = dom_vars (Ctx.length ctx) doms in
            (* A helper function to update the status *)
            let mkstatus (type n) (xs : n variables) : (b, s) status -> ((b, n) snoc, s) status =
              function
              | Kinetic l -> Kinetic l
              | Potential (c, args, hyp) ->
                  let arg =
                    Arg (CubeOf.mmap { map = (fun _ [ x ] -> Ctx.Binding.value x) } [ newnfs ])
                  in
                  Potential (c, Snoc (args, App (arg, ins_zero m)), fun tm -> hyp (Lam (xs, tm)))
            in
            (* Apply and instantiate the codomain to those arguments to get a type to check the body at. *)
            let output = tyof_app cods tyargs newargs in
            match cube with
            (* If the abstraction is a cube, we slurp up the right number of lambdas for the dimension of the pi-type, and pick up the body inside them.  We do this by building a cube of variables of the right dimension while maintaining the current term as an indexed state.  We also build a sum of raw lengths, since we need that to extend the context.  Note that we never need to manually "count" how many faces there are in a cube of any dimension, or discuss how to put them in order: the counting and ordering is handled automatically by iterating through a cube. *)
            | `Normal -> (
                let module S = struct
                  type 'b t =
                    | Ok : Asai.Range.t option * (a, 'b, 'ab) N.plus * 'ab check located -> 'b t
                    | Missing of Asai.Range.t option * int
                end in
                let module Build = NICubeOf.Traverse (S) in
                match
                  Build.build_left m
                    {
                      build =
                        (fun _ -> function
                          | Ok (_, ab, { value = Lam ({ value = x; loc }, `Normal, body); _ }) ->
                              Fwrap (NFamOf x, Ok (loc, Suc ab, body))
                          | Ok (loc, _, _) -> Fwrap (NFamOf None, Missing (loc, 1))
                          | Missing (loc, j) -> Fwrap (NFamOf None, Missing (loc, j + 1)));
                    }
                    (Ok (None, Zero, tm))
                with
                | Wrap (names, Ok (_, af, body)) ->
                    let xs = Variables (D.zero, D.zero_plus m, names) in
                    let ctx = Ctx.vis ctx D.zero (D.zero_plus m) names newnfs af in
                    Lam (xs, check ?discrete (mkstatus xs status) ctx body output)
                | Wrap (_, Missing (loc, j)) -> fatal ?loc (Not_enough_lambdas j))
            | `Cube ->
                (* Here we don't need to slurp up lots of lambdas, but can make do with one. *)
                let xs = singleton_variables m x in
                let ctx = Ctx.cube_vis ctx x newnfs in
                Lam (xs, check ?discrete (mkstatus xs status) ctx body output))
        | _ -> fatal (Checking_lambda_at_nonfunction (PVal (ctx, ty))))
    | Struct (Noeta, tms), Potential _ -> (
        match view_type ~severity ty "typechecking comatch" with
        | Canonical (name, Codata ({ eta = Noeta; ins; _ } as codata_args), tyargs) ->
            let mn = is_id_ins ins <|> Comatching_at_degenerated_codata (phead name) in
            check_struct status Noeta ctx ty (cod_left_ins ins) mn codata_args tyargs tms
        | _ -> fatal (Comatching_at_noncodata (PVal (ctx, ty))))
    | Struct (Eta, tms), _ -> (
        match view_type ~severity ty "typechecking tuple" with
        | Canonical (name, Codata ({ eta = Eta; ins; _ } as codata_args), tyargs) ->
            let mn = is_id_ins ins <|> Checking_tuple_at_degenerated_record (phead name) in
            check_struct status Eta ctx ty (cod_left_ins ins) mn codata_args tyargs tms
        | _ -> fatal (Checking_tuple_at_nonrecord (PVal (ctx, ty))))
    | Constr ({ value = constr; loc = constr_loc }, args), _ -> (
        (* TODO: Move this into a helper function, it's too long to go in here. *)
        match view_type ~severity ty "typechecking constr" with
        | Canonical
            ( name,
              Data { dim; indices = Filled ty_indices; constrs; discrete = _; tyfam = _ },
              tyargs ) -> (
            (* We don't need the *types* of the parameters or indices, which are stored in the type of the constant name.  The variable ty_indices (defined above) contains the *values* of the indices of this instance of the datatype, while tyargs (defined by view_type, way above) contains the instantiation arguments of this instance of the datatype.  We check that the dimensions agree, and find our current constructor in the datatype definition. *)
            match Abwd.find_opt constr constrs with
            | None -> fatal ?loc:constr_loc (No_such_constructor (`Data (phead name), constr))
            | Some (Dataconstr { env; args = constr_arg_tys; indices = constr_indices }) ->
                (* To typecheck a higher-dimensional instance of our constructor constr at the datatype, all the instantiation arguments must also be applications of lower-dimensional versions of that same constructor.  We check this, and extract the arguments of those lower-dimensional constructors as a tube of lists in the variable "tyarg_args". *)
                let tyarg_args =
                  TubeOf.mmap
                    {
                      map =
                        (fun fa [ tm ] ->
                          match view_term tm.tm with
                          | Constr (tmname, n, tmargs) ->
                              if tmname <> constr then
                                fatal (Missing_instantiation_constructor (constr, `Constr tmname))
                              else
                                (* Assuming the instantiation is well-typed, we must have n = dom_tface fa.  I'd like to check that, but for some reason, matching this compare against Eq claims that the type variable n would escape its scope. *)
                                let _ = D.compare n (dom_tface fa) in
                                List.fold_right (fun a args -> CubeOf.find_top a :: args) tmargs []
                          | _ ->
                              fatal
                                (Missing_instantiation_constructor
                                   (constr, `Nonconstr (PNormal (ctx, tm)))));
                    }
                    [ tyargs ] in
                (* Now, for each argument of the constructor, we:
                   1. Evaluate the argument *type* of the constructor (which are assembled in the telescope constr_arg_tys) at the parameters (which are in the environment already) and the previous evaluated argument *values* (which get added to the environment as we go throurgh check_at_tel);
                   2. Instantiate the result at the corresponding arguments of the lower-dimensional versions of the constructor, from tyarg_args;
                   3. Check the coressponding argument *value*, supplied by the user, against this type;
                   4. Evaluate this argument value and add it to the environment, to substitute into the subsequent types, and also later to the indices. *)
                let env, newargs = check_at_tel constr ctx env args constr_arg_tys tyarg_args in
                (* Now we substitute all those evaluated arguments into the indices, to get the actual (higher-dimensional) indices of our constructor application. *)
                let constr_indices =
                  Vec.mmap
                    (fun [ ix ] ->
                      CubeOf.build dim
                        { build = (fun fa -> eval_term (act_env env (op_of_sface fa)) ix) })
                    [ constr_indices ] in
                (* The last thing to do is check that these indices are equal to those of the type we are checking against.  (So a constructor application "checks against the parameters but synthesizes the indices" in some sense.)  I *think* it should suffice to check the top-dimensional ones, the lower-dimensional ones being automatic.  For now, we check all of them, raising an anomaly in case I was wrong about that.  *)
                Vec.miter
                  (fun [ t1s; t2s ] ->
                    CubeOf.miter
                      {
                        it =
                          (fun fa [ t1; t2 ] ->
                            match equal_at (Ctx.length ctx) t1 t2.tm t2.ty with
                            | Some () -> ()
                            | None -> (
                                match is_id_sface fa with
                                | Some _ ->
                                    fatal
                                      (Unequal_indices
                                         (PNormal (ctx, { tm = t1; ty = t2.ty }), PNormal (ctx, t2)))
                                | None ->
                                    fatal (Anomaly "mismatching lower-dimensional constructors")));
                      }
                      [ t1s; t2s ])
                  [ constr_indices; ty_indices ];
                realize status (Term.Constr (constr, dim, newargs)))
        | _ -> fatal (No_such_constructor (`Other (PVal (ctx, ty)), constr)))
    | Synth (Match { tm; sort = `Implicit; branches; refutables }), Potential _ ->
        check_implicit_match status ctx tm branches refutables ty
    | Synth (Match { tm; sort = `Nondep i; branches; refutables = _ }), Potential _ ->
        let stm, sty = synth (Kinetic `Nolet) ctx tm in
        check_nondep_match status ctx stm sty branches (Some i) ty tm.loc
    (* We don't need to deal with `Explicit matches here, since they can always synthesize a type and hence be caught by the catch-all for checking synthesizing terms, below. *)
    (* Checking [] at a pi-type interprets it as a pattern-matching lambda over some empty datatype. *)
    | Empty_co_match, _ -> (
        match (view_type ~severity ty "checking empty (co)match", status) with
        | Pi _, Potential _ -> check_empty_match_lam ctx ty `First
        | Pi _, Kinetic l -> kinetic_of_potential l ctx tm ty "matching lambda"
        | _, _ -> check status ctx { value = Struct (Noeta, Abwd.empty); loc = tm.loc } ty)
    | Refute (tms, i), Potential _ -> check_refute status ctx tms ty i None
    (* Now we go through the canonical types. *)
    | Codata fields, Potential _ -> (
        match view_type ~severity ty "typechecking codata" with
        | UU tyargs ->
            let has_higher_fields =
              Bwd.fold_left
                (fun acc (Field.Wrap fld, _) ->
                  match acc with
                  | Some () -> Some ()
                  | None -> (
                      match D.compare (Field.dim fld) D.zero with
                      | Eq -> None
                      | Neq -> Some ()))
                None fields in
            check_codata status ctx tyargs Emp (Bwd.to_list fields) Emp ~has_higher_fields
        | _ -> fatal (Checking_canonical_at_nonuniverse ("codatatype", PVal (ctx, ty))))
    | Record (xs, fields, opacity), Potential _ -> (
        match view_type ~severity ty "typechecking record" with
        | UU tyargs ->
            let dim = TubeOf.inst tyargs in
            let (Vars (af, vars)) = vars_of_names xs.loc dim xs.value in
            check_record status dim ctx opacity tyargs vars Emp Zero af Emp fields Emp
        | _ -> fatal (Checking_canonical_at_nonuniverse ("record type", PVal (ctx, ty))))
    | Data constrs, Potential _ ->
        (* For a datatype, the type to check against might not be a universe, it could include indices.  We also check whether all the types of all the indices are discrete or a type being defined, to decide whether to keep evaluating the type for discreteness. *)
        let n, disc = typefam ?discrete ctx ty in
        let (Wrap num_indices) = Fwn.of_int n in
        check_data
          ~discrete:(if disc then discrete else None)
          status ctx ty num_indices Abwd.empty (Bwd.to_list constrs) Emp
    (* If we have a term that's not valid outside a case tree, we bind it to a global metavariable. *)
    | Struct (Noeta, _), Kinetic l -> kinetic_of_potential l ctx tm ty "comatch"
    | Synth (Match _), Kinetic l -> kinetic_of_potential l ctx tm ty "match"
    | Refute _, Kinetic l -> kinetic_of_potential l ctx tm ty "match"
    | Codata _, Kinetic l -> kinetic_of_potential l ctx tm ty "codata"
    | Record _, Kinetic l -> kinetic_of_potential l ctx tm ty "sig"
    | Data _, Kinetic l -> kinetic_of_potential l ctx tm ty "data"
    (* If the user left a hole, we create an eternal metavariable. *)
    | Hole { scope = vars; loc = pos; li; ri; num }, _ ->
        (* Holes aren't numbered by the file they appear in. *)
        let meta = Meta.make_hole (Ctx.raw_length ctx) (Ctx.dbwd ctx) (energy status) in
        num := Meta.hole_number meta;
        let ty, termctx =
          Readback.Displaying.run ~env:true @@ fun () -> (readback_val ctx ty, readback_ctx ctx)
        in
        Global.add_hole meta pos ~vars ~termctx ~ty ~status ~li ~ri;
        Meta (meta, energy status)
    (* If we have a synthesizing term, we synthesize it. *)
    | Synth stm, _ -> check_of_synth status ctx stm tm.loc ty
    (* We pass through case tree leaf markers *)
    | Realize ktm, Potential _ -> Realize (check (Kinetic `Nolet) ctx (locate_opt tm.loc ktm) ty)
    | Realize ktm, Kinetic l -> check (Kinetic l) ctx (locate_opt tm.loc ktm) ty
    (* Nothing is embedded *)
    | Embed _, _ -> .
    (* If we're using the checking type as an implicit first argument: *)
    | ImplicitApp (fn, args), _ -> (
        (* We read it back, so we can put it as the first argument in the generated term. *)
        let cty = readback_val ctx ty in
        (* Now we act like synth on an application. *)
        let sfn, sty = synth (Kinetic `Nolet) ctx fn in
        match view_type sty "ImplicitApp" with
        | Pi (_, doms, cods, tyargs) -> (
            (* Only 0-dimensional applications are allowed. *)
            match D.compare (CubeOf.dim doms) D.zero with
            | Eq -> (
                (* The first argument must be a type. *)
                match view_type (CubeOf.find_top doms) "ImplicitApp argument" with
                | UU _ ->
                    (* We build the implicit application term and its type. *)
                    let new_sfn = locate_opt fn.loc (Term.App (sfn, CubeOf.singleton cty)) in
                    let new_sty = tyof_app cods tyargs (CubeOf.singleton ty) in
                    (* And then proceed applying to the rest of the arguments, if any. *)
                    let stm, sty =
                      match args with
                      | _ :: _ ->
                          let args =
                            List.map (fun (l, x) -> (l, x, locate_opt None `Explicit)) args in
                          synth_apps (Kinetic `Nolet) ctx new_sfn new_sty fn args
                      | _ -> (new_sfn.value, new_sty) in
                    (* Then we have to check that the resulting type of the whole application agrees with the one we're checking against. *)
                    equal_val (Ctx.length ctx) sty ty
                    <|> Unequal_synthesized_type
                          { got = PVal (ctx, sty); expected = PVal (ctx, ty); which = None };
                    realize status stm
                | _ ->
                    fatal ?loc:fn.loc
                      (Anomaly "first argument of an ImplicitMap is not of type Type"))
            | Neq -> fatal ?loc:fn.loc (Dimension_mismatch ("ImplicitApp", CubeOf.dim doms, D.zero))
            )
        | _ -> fatal ?loc:fn.loc (Applying_nonfunction_nontype (PTerm (ctx, sfn), PVal (ctx, sty))))
    | First alts, _ ->
        let rec go errs = function
          | [] -> fatal (Choice_mismatch (PVal (ctx, ty)))
          | (test, alt, passthru) :: alts -> (
              match (view_type ty "check_first", test) with
              | Canonical (_, Data { constrs = data_constrs; _ }, _), `Data constrs ->
                  if
                    List.for_all
                      (fun constr ->
                        Bwd.exists (fun (data_constr, _) -> constr = data_constr) data_constrs)
                      constrs
                  then
                    Reporter.try_with ~fatal:(fun d ->
                        if passthru then go (Snoc (errs, d)) alts else fatal_diagnostic d)
                    @@ fun () -> check ?discrete status ctx (locate_opt tm.loc alt) ty
                  else go errs alts
              | Canonical (_, Codata { fields = codata_fields; _ }, _), `Codata fields ->
                  if
                    List.for_all
                      (fun field ->
                        Bwd.exists
                          (fun (CodatafieldAbwd.Entry (codata_field, _)) ->
                            field = Field.to_string codata_field)
                          codata_fields)
                      fields
                  then
                    Reporter.try_with ~fatal:(fun d ->
                        if passthru then go (Snoc (errs, d)) alts else fatal_diagnostic d)
                    @@ fun () -> check ?discrete status ctx (locate_opt tm.loc alt) ty
                  else go errs alts
              | _, `Any ->
                  Reporter.try_with ~fatal:(fun d ->
                      if passthru then go (Snoc (errs, d)) alts else fatal_diagnostic d)
                  @@ fun () -> check ?discrete status ctx (locate_opt tm.loc alt) ty
              | _ -> go errs alts) in
        go Emp alts
    | Oracle tm, _ -> (
        let ctm = check (Kinetic `Nolet) ctx tm ty in
        let etm = eval_term (Ctx.env ctx) ctm in
        match Oracle.ask (Ask (ctx, etm)) with
        | Ok () -> (
            match status with
            | Kinetic _ -> ctm
            | Potential _ -> Realize ctm)
        | Error err -> fatal err) in
  with_loc tm.loc @@ fun () ->
  Annotate.ctx status ctx tm;
  Annotate.ty ctx ty;
  let result = go () in
  Annotate.tm ctx result;
  result

(* Deal with a synthesizing term in checking position. *)
and check_of_synth : type a b s.
    (b, s) status -> (a, b) Ctx.t -> a synth -> Asai.Range.t option -> kinetic value -> (b, s) term
    =
 fun status ctx stm loc ty ->
  match stm with
  | Asc (ctm, aty) ->
      (* If the term is synthesizing because it is ascribed, then we can accumulate errors: if the ascription fails to check, or if it fails to equal the checking type, we can proceed to check the ascribed term against the supplied type instead.  This will rarely happen in normal use, since there is no need to ascribe a term that's in checking position, but it can occur with some alternative frontends. *)
      Reporter.try_with ~fatal:(fun d1 ->
          Reporter.try_with ~fatal:(fun d2 ->
              fatal (Accumulated ("check_of_synth", Snoc (Snoc (Emp, d1), d2))))
          @@ fun () ->
          let _ = check status ctx ctm ty in
          fatal_diagnostic d1)
      @@ fun () ->
      let cty = check (Kinetic `Nolet) ctx aty (universe D.zero) in
      let ety = eval_term (Ctx.env ctx) cty in
      equal_val (Ctx.length ctx) ety ty
      <|> Unequal_synthesized_type
            { got = PVal (ctx, ety); expected = PVal (ctx, ty); which = None };
      let ctm = check status ctx ctm ety in
      ctm
  | _ ->
      let sval, sty = synth status ctx { value = stm; loc } in
      equal_val (Ctx.length ctx) sty ty
      <|> Unequal_synthesized_type
            { got = PVal (ctx, sty); expected = PVal (ctx, ty); which = None };
      sval

(* Deal with checking a potential term in kinetic position *)
and kinetic_of_potential : type a b.
    [ `Let | `Nolet ] ->
    (a, b) Ctx.t ->
    a check located ->
    kinetic value ->
    string ->
    (b, kinetic) term =
 fun l ctx tm ty sort ->
  match l with
  | `Let -> raise Case_tree_construct_in_let
  | `Nolet ->
      emit (Bare_case_tree_construct sort);
      (* We create a metavariable to store the potential value. *)
      let meta = Meta.make_def sort None (Ctx.raw_length ctx) (Ctx.dbwd ctx) Potential in
      (* We first define the metavariable without a value, as an "axiom", just as we do for global constants.  This isn't necessary for recursion, since this metavariable can't refer to itself, but so that with_meta_definition will be able to find it for consistency. *)
      let termctx = readback_ctx ctx in
      let vty = readback_val ctx ty in
      Global.add_meta meta ~termctx ~tm:`Axiom ~ty:vty ~energy:Potential;
      (* Then we check the value and redefine the metavariable to be that value. *)
      let tmstatus = Potential (Meta (meta, Ctx.env ctx), Emp, fun x -> x) in
      let cv = check tmstatus ctx tm ty in
      Global.set_meta meta ~tm:cv;
      (* Finally, we return the metavariable. *)
      Term.Meta (meta, Kinetic)

and synth_or_check_let : type a b s p.
    (b, s) status ->
    (a, b) Ctx.t ->
    string option ->
    a synth located ->
    a N.suc check located ->
    (kinetic value, p) Perhaps.t ->
    (b, s) term * (kinetic value, p) Perhaps.not =
 fun status ctx name v body ty ->
  let v, nf =
    try
      (* We first try checking the bound term first as an ordinary kinetic term. *)
      let sv, svty = synth (Kinetic `Let) ctx v in
      let ev = eval_term (Ctx.env ctx) sv in
      (sv, { tm = ev; ty = svty })
    with
    (* If that encounters case-tree constructs, then we can allow the bound term to be a case tree, i.e. a potential term.  But in a checked "let" expression, the term being bound is a kinetic one, and must be so that its value can be put into the environment when the term is evaluated.  We deal with this by binding a *metavariable* to the bound term and then taking the value of that metavariable as the kinetic term to actually be bound.  *)
    | Case_tree_construct_in_let ->
      (* First we make the metavariable. *)
      let meta = Meta.make_def "let" name (Ctx.raw_length ctx) (Ctx.dbwd ctx) Potential in
      let termctx = readback_ctx ctx in
      (* A new status in which to check the value of that metavariable; now it is the "current constant" being defined. *)
      let tmstatus = Potential (Meta (meta, Ctx.env ctx), Emp, fun x -> x) in
      let sv, svty =
        match v.value with
        | Asc (vtm, rvty) ->
            (* If the bound term is explicitly ascribed, then we can give the metavariable a type while checking its body.  This is probably mainly only useful with "let rec". *)
            let vty = check (Kinetic `Nolet) ctx rvty (universe D.zero) in
            Global.add_meta meta ~termctx ~tm:`Axiom ~ty:vty ~energy:Potential;
            let evty = eval_term (Ctx.env ctx) vty in
            let cv = check tmstatus ctx vtm evty in
            Global.set_meta meta ~tm:cv;
            (cv, evty)
        | _ ->
            (* Otherwise, we just synthesize the term. *)
            let sv, svty = synth tmstatus ctx v in
            let vty = readback_val ctx svty in
            Global.add_meta meta ~termctx ~tm:(`Defined sv) ~ty:vty ~energy:Potential;
            (sv, svty) in
      (* We turn that metavariable into a value. *)
      let head = Value.Meta { meta; env = Ctx.env ctx; ins = zero_ins D.zero } in
      let tm =
        if GluedEval.read () then
          (* Glued evaluation: we delay evaluating the term until it's needed. *)
          Uninst (Neu { head; args = Emp; value = lazy_eval (Ctx.env ctx) sv }, Lazy.from_val svty)
        else
          match eval (Ctx.env ctx) sv with
          | Realize x -> x
          | value -> Uninst (Neu { head; args = Emp; value = ready value }, Lazy.from_val svty)
      in
      (Term.Meta (meta, Kinetic), { tm; ty = svty }) in
  (* Either way, we end up with a checked term 'v' and a normal form 'nf'.  We use the latter to extend the context. *)
  let newctx = Ctx.ext_let ctx name nf in
  (* Now we update the status of the original constant being checked *)
  let status : ((b, D.zero) snoc, s) status =
    match status with
    | Potential (c, args, hyp) -> Potential (c, args, fun body -> hyp (Let (name, v, body)))
    | Kinetic l -> Kinetic l in
  (* And synthesize or check the body in the extended context. *)
  Annotate.ctx status newctx body;
  match (ty, body) with
  | Some ty, _ ->
      let sbody = check status newctx body ty in
      (Term.Let (name, v, sbody), Not_some)
  | None, { value = Synth body; loc } ->
      let sbody, sbodyty = synth status newctx { value = body; loc } in
      (Term.Let (name, v, sbody), Not_none sbodyty)
  | None, _ -> fatal (Nonsynthesizing "let-expression without synthesizing body")

and synth_or_check_letrec : type a b c ac s p.
    (b, s) status ->
    (a, b) Ctx.t ->
    (a, c, ac) Raw.tel ->
    (ac check located, c) Vec.t ->
    ac check located ->
    (kinetic value, p) Perhaps.t ->
    (b, s) term * (kinetic value, p) Perhaps.not =
 fun status ctx rvtys vtms body ty ->
  (* First we check the types of all the bound variables, which are a telescope since each can depend on the previous ones. *)
  let Checked_tel (type bc) ((vtys, _) : (_, _, bc) Telescope.t * (_, bc) Ctx.t), _ =
    check_tel ctx rvtys in
  (* Then we create the metavariables. *)
  let metas = make_letrec_metas ctx vtys in
  (* Now we check the bound terms. *)
  let ac = Raw.bplus_of_tel rvtys in
  let () = check_letrec_bindings ctx ac metas vtys vtms in
  (* Now we update the status of the original constant being checked *)
  let status : (bc, s) status =
    match status with
    | Potential (c, args, hyp) -> Potential (c, args, fun x -> hyp (let_metas metas x))
    | Kinetic l -> Kinetic l in
  (* Make a context for it *)
  let _, newctx = ext_metas ctx ac metas vtys Zero Zero Zero in
  (* And synthesize or check the body in the extended context. *)
  Annotate.ctx status newctx body;
  match (ty, body) with
  | Some ty, _ ->
      let sbody = check status newctx body ty in
      (let_metas metas sbody, Not_some)
  | None, { value = Synth body; loc } ->
      let sbody, sbodyty = synth status newctx { value = body; loc } in
      (let_metas metas sbody, Not_none sbodyty)
  | None, _ -> fatal (Nonsynthesizing "let-expression without synthesizing body")

and check_letrec_bindings : type a xc b ac bc.
    (a, b) Ctx.t ->
    (a, xc, ac) Fwn.bplus ->
    (b, xc, bc) meta_tel ->
    (b, xc, bc) Telescope.t ->
    (ac check located, xc) Vec.t ->
    unit =
 fun octx oac ometas ovtys vs ->
  let rec go : type x ax bx c.
      (a, x, ax) Fwn.bplus ->
      (x, c, xc) Fwn.plus ->
      (b, x, D.zero, bx) Tbwd.snocs ->
      (* *)
      (ax, c, ac) Fwn.bplus ->
      (bx, c, bc) meta_tel ->
      (bx, c, bc) Telescope.t ->
      (ac check located, c) Vec.t ->
      unit =
   fun ax xc bx ac metas vtys vs ->
    match (ac, metas, vtys, vs) with
    | Zero, Nil, Emp, [] -> ()
    | Suc ac, Ext (_, meta, metas), Ext (name, vty, vtys), v :: vs ->
        let ctx, tmctx = ext_metas octx oac ometas ovtys ax xc bx in
        let evty = eval_term (Ctx.env ctx) vty in
        let hyp b = Term.Let (name, Meta (meta, Kinetic), let_metas metas b) in
        let tmstatus = Potential (Meta (meta, Ctx.env ctx), Emp, hyp) in
        let cv = check tmstatus tmctx v evty in
        Global.set_meta meta ~tm:(hyp cv);
        (* And recurse. *)
        go (Fwn.bplus_suc_eq_suc ax) (Fwn.suc_plus xc) (Tbwd.snocs_suc_eq_snoc bx) ac metas vtys vs
  in
  go Zero Zero Zero oac ometas ovtys vs

(* Given a telescope of types for let-bound variables, create a global metavariable for each of them, and give it the correct type in Global. *)
and make_letrec_metas : type x a b ab. (x, a) Ctx.t -> (a, b, ab) Telescope.t -> (a, b, ab) meta_tel
    =
 fun ctx tel ->
  match tel with
  | Emp -> Nil
  | Ext (x, vty, tel) ->
      (* Create the metavariable. *)
      let meta = Meta.make_def "letrec" x (Ctx.raw_length ctx) (Ctx.dbwd ctx) Potential in
      (* Assign it the correct type. *)
      let termctx = readback_ctx ctx in
      Global.add_meta meta ~termctx ~tm:`Axiom ~ty:vty ~energy:Potential;
      (* Extend the context by it, as an unrealized neutral.  TODO: It's annoying that we have to evaluate the types here to extend the value-context, when the only use we're making of it is to readback that extended value-context into a termctx at each step to save with the global metavariable.  It would make more sense, and be more efficient, to just carry along the termctx and extend it directly at each step with "Term.Meta (meta, Kinetic)" at the term-type "vty".  Unfortunately, termctxs store terms and types in a one-longer context, so that would require directly weakening vty, or perhaps parsing and checking it in a one-longer context originally. *)
      let evty = eval_term (Ctx.env ctx) vty in
      let head = Value.Meta { meta; env = Ctx.env ctx; ins = zero_ins D.zero } in
      let neutm = Uninst (Neu { head; args = Emp; value = ready Unrealized }, Lazy.from_val evty) in
      let ctx = Ctx.ext_let ctx x { tm = neutm; ty = evty } in
      (* And recurse. *)
      Ext (x, meta, make_letrec_metas ctx tel)

and let_metas : type b c bc s. (b, c, bc) meta_tel -> (bc, s) term -> (b, s) term =
 fun metas tm ->
  match metas with
  | Nil -> tm
  | Ext (x, m, metas) -> Let (x, Meta (m, Kinetic), let_metas metas tm)

(* Extend a context by evaluated metavariables.  We return both the fully extended context and a partially extended one. *)
and ext_metas : type a b c ac bc d cd acd bcd.
    (a, b) Ctx.t ->
    (a, cd, acd) Fwn.bplus ->
    (b, cd, bcd) meta_tel ->
    (b, cd, bcd) Telescope.t ->
    (a, c, ac) Fwn.bplus ->
    (c, d, cd) Fwn.plus ->
    (b, c, D.zero, bc) Tbwd.snocs ->
    (ac, bc) Ctx.t * (acd, bcd) Ctx.t =
 fun ctx acd metas vtys ac cd bc ->
  (* First we define a helper function that returns only the fully extended context. *)
  let rec ext_metas' : type a b cd acd bcd.
      (a, b) Ctx.t ->
      (a, cd, acd) Fwn.bplus ->
      (b, cd, bcd) meta_tel ->
      (b, cd, bcd) Telescope.t ->
      (acd, bcd) Ctx.t =
   fun ctx acd metas vtys ->
    match (acd, metas, vtys) with
    | Zero, Nil, Emp -> ctx
    | Suc acd, Ext (_, meta, metas), Ext (x, vty, vtys) ->
        let tm = eval_term (Ctx.env ctx) (Meta (meta, Kinetic)) in
        let ty = eval_term (Ctx.env ctx) vty in
        ext_metas' (Ctx.ext_let ctx x { tm; ty }) acd metas vtys in
  match (ac, cd, bc, acd, metas, vtys) with
  | Zero, Zero, Zero, _, _, _ -> (ctx, ext_metas' ctx acd metas vtys)
  | Suc ac, Suc cd, Suc bc, Suc acd, Ext (_, meta, metas), Ext (x, vty, vtys) ->
      let tm = eval_term (Ctx.env ctx) (Meta (meta, Kinetic)) in
      let ty = eval_term (Ctx.env ctx) vty in
      ext_metas (Ctx.ext_let ctx x { tm; ty }) acd metas vtys ac cd bc

(* Check a match statement without an explicit motive supplied by the user.  This means if the discriminee is a well-behaved variable, it can be a variable match; otherwise it reverts back to a non-dependent match. *)
and check_implicit_match : type a b.
    (b, potential) status ->
    (a, b) Ctx.t ->
    a synth located ->
    (Constr.t, a branch) Abwd.t ->
    a refutables option ->
    kinetic value ->
    (b, potential) term =
 fun status ctx tm brs refutables motive ->
  match tm with
  (* For a variable match, the variable must not be let-bound to a value or be a field access variable.  Checking that it isn't also gives us its De Bruijn level, its type, and its checked-index.  If it's not a free variable, or if we're not in a case tree or if the motive was supplied explicitly, we obtain its value and type; then we pass on to the appropriate checking function. *)
  | { value = Var ix; loc } -> (
      match Ctx.lookup ctx ix with
      | `Field (_, _, fld) ->
          emit ?loc (Matching_wont_refine ("discriminee is record field", Some (PField fld)));
          let stm, varty = synth (Kinetic `Nolet) ctx tm in
          check_nondep_match status ctx stm varty brs None motive tm.loc
      | `Var (None, _, ix) ->
          emit ?loc (Matching_wont_refine ("discriminee is let-bound", Some (PTerm (ctx, Var ix))));
          let stm, varty = synth (Kinetic `Nolet) ctx tm in
          check_nondep_match status ctx stm varty brs None motive tm.loc
      | `Var (Some level, { tm = _; ty = varty }, index) ->
          with_loc loc (fun () ->
              Annotate.ctx status ctx (locate_opt loc (Synth (Var ix)));
              Annotate.ty ctx varty;
              Annotate.tm ctx (realize status (Term.Var index)));
          check_var_match status ctx level index varty brs refutables motive loc)
  | _ ->
      let stm, varty = synth (Kinetic `Nolet) ctx tm in
      check_nondep_match status ctx stm varty brs None motive tm.loc

(* Check a non-dependent match against a specified type. *)
and check_nondep_match : type a b.
    (b, potential) status ->
    (a, b) Ctx.t ->
    (b, kinetic) term ->
    kinetic value ->
    (Constr.t, a branch) Abwd.t ->
    int located option ->
    kinetic value ->
    Asai.Range.t option ->
    (b, potential) term =
 fun status ctx tm varty brs i motive loc ->
  (* We look up the type of the discriminee, which must be a datatype, without any degeneracy applied outside, and at the same dimension as its instantiation. *)
  match view_type varty "check_nondep_match" with
  | Canonical
      (type m)
      (( name,
         Data
           (type j ij)
           ({ dim; indices = Filled indices; constrs = data_constrs; discrete = _; tyfam = _ } :
             (_, j, ij) data_args),
         _ ) :
        _ * m canonical * _) -> (
      (* Yes, we really don't care what the instantiation arguments are in this case, and we really don't care what the indices are either except to check there are the right number of them.  This is because in the non-dependent case, we are just applying a recursor to a value, so we don't need to know that the indices and instantiation arguments are variables; in the branches they will be whatever they will be, but we don't even need to *know* what they will be because the output type isn't getting refined either. *)
      (match i with
      | Some { value; loc } ->
          let needed = Fwn.to_int (Vec.length indices) + 1 in
          if value <> needed then fatal ?loc (Wrong_number_of_arguments_to_motive needed)
      | None -> ());
      (* We start with a preprocesssing step that pairs each user-provided branch with the corresponding constructor information from the datatype. *)
      let user_branches = merge_branches name brs data_constrs in
      (* We now iterate through the constructors, typechecking the corresponding branches and inserting them in the match tree. *)
      let branches, errs =
        List.fold_left
          (fun (branches, errs)
               ( constr,
                 (Checkable_branch { xs; body; env; argtys; index_terms = _ } :
                   (a, m, ij) checkable_branch) ) ->
            let (Snocs efc) = Tbwd.snocs (Telescope.length argtys) in
            (* Create new level variables for the pattern variables to which the constructor is applied, and add corresponding index variables to the context.  The types of those variables are specified in the telescope argtys, and have to be evaluated at the closure environment 'env' and the previous new variables (this is what ext_tel does).  For a higher-dimensional match, the new variables come with their boundaries in n-dimensional cubes. *)
            let newctx, _, _, newnfs = ext_tel ctx env xs argtys efc in
            let perm = Tbwd.id_perm in
            let status = make_match_status status tm dim branches efc None perm constr in
            (* Finally, we recurse into the "body" of the branch.  We catch errors and accumuate them so that later branches can continue to be checked and produce their own errors even if earlier ones fail, but we pass through the errors that are getting caught elsewhere. *)
            Reporter.try_with ~fatal:(fun e ->
                match e.message with
                | Missing_constructor_in_match _ -> fatal_diagnostic e
                | _ -> (branches, Snoc (errs, e)))
            @@ fun () ->
            match body with
            | Some body ->
                ( branches
                  |> Constr.Map.add constr
                       (Term.Branch (efc, perm, check status newctx body motive)),
                  errs )
            | None ->
                if any_empty newnfs then (branches |> Constr.Map.add constr Term.Refute, errs)
                else fatal (Missing_constructor_in_match constr))
          (Constr.Map.empty, Emp) user_branches in
      match errs with
      | Snoc _ -> fatal (Accumulated ("check_nondep_match", errs))
      | Emp -> Match { tm; dim; branches })
  | _ -> fatal ?loc (Matching_on_nondatatype (PVal (ctx, varty)))

(* Try to synthesize a type from all the branches.  If any succeed, check the remaining branches against that synthesized type. *)
and synth_nondep_match : type a b.
    (b, potential) status ->
    (a, b) Ctx.t ->
    a synth located ->
    (Constr.t, a branch) Abwd.t ->
    int located option ->
    (b, potential) term * kinetic value =
 fun status ctx tm brs i ->
  (* First we synthesize the discriminee.  If that fails, we give up completely, as we don't even have a context in which to try synthesizing the branches. *)
  let (tm, varty), loc = (synth (Kinetic `Nolet) ctx tm, tm.loc) in
  (* The preprocessing is the same as in check_nondep_match; see there for comments. *)
  match view_type varty "synth_nondep_match" with
  | Canonical
      (type m)
      (( name,
         Data
           (type j ij)
           ({ dim; indices = Filled indices; constrs = data_constrs; discrete = _; tyfam = _ } :
             (_, j, ij) data_args),
         _ ) :
        _ * m canonical * _) -> (
      (match i with
      | Some { value; loc } ->
          let needed = Fwn.to_int (Vec.length indices) + 1 in
          if value <> needed then fatal ?loc (Wrong_number_of_arguments_to_motive needed)
      | None -> ());
      (* Now we split the branches into the synthesizing and non-synthesizing ones. *)
      let synth_branches, check_branches =
        List.partition_map
          (fun (c, (Checkable_branch { xs; body; env; argtys; index_terms } as cb)) ->
            match body with
            | Some { value = Synth sbody; loc } ->
                let body = locate_opt loc sbody in
                Left (c, Synthable_branch { xs; body; env; argtys; index_terms })
            | _ -> Right (c, cb))
          (merge_branches name brs data_constrs) in
      (* We iterate through the synthesizing branches looking for the first one that succeeds at synthesizing, accumulating errors from the ones that fail. *)
      let rec find_synthing_branch errs = function
        | [] ->
            (* If they all fail, then we report the accumulated errors (we can't go on to the checking branches, since we don't have anything to even try to typecheck them against).  If there weren't any to begin with, we instead report their absence. *)
            let errs =
              if Bwd.is_empty errs then
                Snoc (Emp, diagnostic (Nonsynthesizing "match without synthesizing branches"))
              else errs in
            (None, errs, Constr.Map.empty, [])
        | ( constr,
            (Synthable_branch { xs; body; env; argtys; index_terms = _ } :
              (a, m, ij) synthable_branch) )
          :: brs ->
            (* Again, same preprocessing as in check_nondep_match. *)
            let (Snocs efc) = Tbwd.snocs (Telescope.length argtys) in
            let newctx, _, _, _ = ext_tel ctx env xs argtys efc in
            let perm = Tbwd.id_perm in
            let status = make_match_status status tm dim Constr.Map.empty efc None perm constr in
            Annotate.ctx status newctx (locate_opt body.loc (Synth body.value));
            (* Trap errors and accumulate them, going on to look for other synthesizing branches. *)
            Reporter.try_with ~fatal:(fun e -> find_synthing_branch (Snoc (errs, e)) brs)
            @@ fun () ->
            let sbr, sty = synth status newctx body in
            (* The type synthesized is only valid for the whole match if it doesn't depend on the pattern variables.  We check that by reading it back into the original context. *)
            ( Reporter.try_with ~fatal:(fun d ->
                  match d.message with
                  | No_such_level _ ->
                      fatal
                        (Invalid_synthesized_type
                           ("synthesizing branch of match", PVal (newctx, sty)))
                  | _ -> fatal_diagnostic d)
            @@ fun () -> discard (readback_val ctx sty) );
            (* Finally, if we found a synthesizing branch that works, return the synthesized type, the accumulated errors, the successful typechecked branch, and the remaining synthesizing branches. *)
            (Some sty, errs, Constr.Map.singleton constr (Term.Branch (efc, perm, sbr)), brs) in
      let motive, errs, branches, synth_branches = find_synthing_branch Emp synth_branches in
      (* We put the remaining synthesizing branches back on the front of the checking ones. *)
      let check_branches =
        List.fold_right
          (fun (c, Synthable_branch { xs; body; env; argtys; index_terms }) cbs ->
            let body = Some { value = Synth body.value; loc = body.loc } in
            (c, Checkable_branch { xs; body; env; argtys; index_terms }) :: cbs)
          synth_branches check_branches in
      (* Now we proceed to check these branches, as in check_nondep_match.  See there for comments. *)
      let branches, errs =
        List.fold_left
          (fun (branches, errs)
               ( constr,
                 (Checkable_branch { xs; body; env; argtys; index_terms = _ } :
                   (a, m, ij) checkable_branch) ) ->
            let (Snocs efc) = Tbwd.snocs (Telescope.length argtys) in
            let newctx, _, _, newnfs = ext_tel ctx env xs argtys efc in
            let perm = Tbwd.id_perm in
            let status = make_match_status status tm dim branches efc None perm constr in
            Reporter.try_with ~fatal:(fun e ->
                match e.message with
                | Missing_constructor_in_match _ -> fatal_diagnostic e
                | _ -> (branches, Snoc (errs, e)))
            @@ fun () ->
            match (body, motive) with
            (* The difference with the checking case is that we might have no motive, if all the synthesis failed.  In that case, the only reason we're going through this is to annotate the contexts of each branch. *)
            | Some body, None ->
                Annotate.ctx status newctx body;
                (branches, errs)
            | Some body, Some motive ->
                ( branches
                  |> Constr.Map.add constr
                       (Term.Branch (efc, perm, check status newctx body motive)),
                  errs )
            | None, _ ->
                if any_empty newnfs then (branches |> Constr.Map.add constr Term.Refute, errs)
                else fatal (Missing_constructor_in_match constr))
          (branches, errs) check_branches in
      match (errs, motive) with
      | Snoc _, _ -> fatal (Accumulated ("synth_nondep_match", errs))
      | Emp, None -> fatal (Anomaly "no synthesized type of match but no errors")
      | Emp, Some motive -> (Match { tm; dim; branches }, motive))
  | _ -> fatal ?loc (Matching_on_nondatatype (PVal (ctx, varty)))

(* Check a dependently typed match, with motive supplied by the user.  (Thus we have to typecheck the motive as well.) *)
and synth_dep_match : type a b.
    (b, potential) status ->
    (a, b) Ctx.t ->
    a synth located ->
    (Constr.t, a branch) Abwd.t ->
    a check located ->
    (b, potential) term * kinetic value =
 fun status ctx tm brs motive ->
  let module S = Monad.State (struct
    type t = kinetic value
  end) in
  let module MC = CubeOf.Monadic (S) in
  let module MT = TubeOf.Monadic (S) in
  (* We look up the type of the discriminee, which must be a datatype, without any degeneracy applied outside, and at the same dimension as its instantiation. *)
  let ctm, varty = synth (Kinetic `Nolet) ctx tm in
  match view_type varty "synth_dep_match" with
  | Canonical
      (type m)
      (( name,
         Data
           (type j ij)
           ({ dim; indices = Filled var_indices; constrs = data_constrs; discrete = _; tyfam } :
             (_, j, ij) data_args),
         inst_args ) :
        _ * m canonical * _) -> (
      let tyfam =
        match !tyfam with
        | Some tyfam -> Lazy.force tyfam
        | None -> fatal (Anomaly "tyfam unset") in
      let emotivety = eval_term (Ctx.env ctx) (motive_of_family ctx tyfam.tm tyfam.ty) in
      let cmotive = check (Kinetic `Nolet) ctx motive emotivety in
      let emotive = eval_term (Ctx.env ctx) cmotive in
      (* We start with a preprocesssing step that pairs each user-provided branch with the corresponding constructor information from the datatype. *)
      let user_branches = merge_branches name brs data_constrs in
      (* We now iterate through the constructors, typechecking the corresponding branches and inserting them in the match tree. *)
      let branches, errs =
        List.fold_left
          (fun (branches, errs)
               ( constr,
                 (Checkable_branch { xs; body; env; argtys; index_terms } :
                   (a, m, ij) checkable_branch) ) ->
            let (Snocs efc) = Tbwd.snocs (Telescope.length argtys) in
            (* Create new level variables for the pattern variables to which the constructor is applied, and add corresponding index variables to the context.  The types of those variables are specified in the telescope argtys, and have to be evaluated at the closure environment 'env' and the previous new variables (this is what ext_tel does).  For a higher-dimensional match, the new variables come with their boundaries in n-dimensional cubes. *)
            let newctx, newenv, newvars, newnfs = ext_tel ctx env xs argtys efc in
            let perm = Tbwd.id_perm in
            let status = make_match_status status ctm dim branches efc None perm constr in
            (* To get the type at which to typecheck the body of the branch, we have to evaluate the general dependent motive at the indices of this constructor, its boundaries, and itself.  First we compute the indices. *)
            let index_vals =
              Vec.mmap (fun [ ixtm ] -> eval_with_boundary newenv ixtm) [ index_terms ] in
            let bmotive = Vec.fold_left apply_singletons emotive index_vals in
            (* Now we compute the constructor and its boundaries. *)
            let constr_vals =
              CubeOf.build dim
                {
                  build =
                    (fun fa ->
                      Value.Constr (constr, dom_sface fa, List.map (CubeOf.subcube fa) newvars));
                } in
            let bmotive = apply_singletons bmotive constr_vals in
            (* Finally, we recurse into the "body" of the branch. *)
            match body with
            | Some body ->
                (* We catch and accumulate errors so that later branches can continue to be checked and produce their own errors even if earlier ones fail, but we pass through the errors that are getting caught elsewhere. *)
                Reporter.try_with ~fatal:(fun e ->
                    match e.message with
                    | Missing_constructor_in_match _ -> fatal_diagnostic e
                    | _ -> (branches, Snoc (errs, e)))
                @@ fun () ->
                ( branches
                  |> Constr.Map.add constr
                       (Term.Branch (efc, perm, check status newctx body bmotive)),
                  errs )
            | None ->
                if any_empty newnfs then (branches |> Constr.Map.add constr Term.Refute, errs)
                else fatal (Missing_constructor_in_match constr))
          (Constr.Map.empty, Emp) user_branches in
      match errs with
      | Snoc _ -> fatal (Accumulated ("synth_dep_match", errs))
      | Emp ->
          (* Now we compute the output type by evaluating the dependent motive at the match term's indices, boundary, and itself. *)
          let result =
            Vec.fold_left
              (fun fn xs ->
                snd
                  (MC.miterM
                     { it = (fun _ [ x ] fn -> ((), apply_term fn (CubeOf.singleton x.tm))) }
                     [ xs ] fn))
              emotive var_indices in
          let result =
            snd
              (MT.miterM
                 { it = (fun _ [ x ] fn -> ((), apply_term fn (CubeOf.singleton x.tm))) }
                 [ inst_args ] result) in
          let result = apply_term result (CubeOf.singleton (eval_term (Ctx.env ctx) ctm)) in
          (* We readback the result so we can store it in the term, so that when evaluating it we know what its type must be without having to do all the work again. *)
          (Match { tm = ctm; dim; branches }, result))
  | _ -> fatal ?loc:tm.loc (Matching_on_nondatatype (PVal (ctx, varty)))

(* Check a match against a well-behaved variable, which can only appear in a case tree and refines not only the goal but the context (possibly with permutation). *)
and check_var_match : type a b.
    (b, potential) status ->
    (a, b) Ctx.t ->
    level ->
    b Term.index ->
    kinetic value ->
    (Constr.t, a branch) Abwd.t ->
    a refutables option ->
    kinetic value ->
    Asai.Range.t option ->
    (b, potential) term =
 fun status ctx level index varty brs refutables motive loc ->
  (* We look up the type of the discriminee, which must be a datatype, without any degeneracy applied outside, and at the same dimension as its instantiation. *)
  match view_type varty "check_var_match" with
  | Canonical
      (type m)
      (( name,
         Data
           (type j ij)
           ({ dim; indices = Filled var_indices; constrs = data_constrs; discrete = _; tyfam } :
             (_, j, ij) data_args),
         inst_args ) :
        _ * m canonical * _) -> (
      let tyfam =
        match !tyfam with
        | Some tyfam -> Lazy.force tyfam
        | None -> fatal (Anomaly "tyfam unset") in
      let tyfam_args : (D.zero, m, m, normal) TubeOf.t =
        match view_type tyfam.ty "check_var_match tyfam" with
        | Pi (_, _, _, tyfam_args) -> (
            match D.compare dim (TubeOf.inst tyfam_args) with
            | Neq -> fatal (Dimension_mismatch ("check_var_match", dim, TubeOf.inst tyfam_args))
            | Eq -> tyfam_args)
        | UU tyfam_args -> (
            match D.compare dim (TubeOf.inst tyfam_args) with
            | Neq -> fatal (Dimension_mismatch ("check_var_match", dim, TubeOf.inst tyfam_args))
            | Eq -> tyfam_args)
        | _ -> fatal (Show ("tyfam is not a type family", PVal (ctx, tyfam.ty))) in
      (* In our simple version of pattern-matching against a variable, the "indices" and all their boundaries must be distinct free variables with no degeneracies, so that in the branch for each constructor they can be set equal to the computed value of that index for that constructor (and in which they cannot occur).  This is a special case of the unification algorithm described in CDP "Pattern-matching without K" where the only allowed rule is "Solution".  Later we can try to enhance it with their full unification algorithm, at least for non-higher datatypes.  In addition, for a higher-dimensional match, the instantiation arguments must also all be distinct variables, distinct from the indices.  If any of these conditions fail, we raise an exception, catch it, emit a hint, and revert to doing a non-dependent match. *)
      let seen = Hashtbl.create 10 in
      let is_fresh x =
        match x.tm with
        | Uninst (Neu { head = Var { level; deg }; args = Emp; value }, _) -> (
            match force_eval value with
            | Unrealized ->
                if Option.is_none (is_id_deg deg) then
                  fatal
                    (Matching_wont_refine ("index variable has degeneracy", Some (PNormal (ctx, x))));
                if Hashtbl.mem seen level then
                  fatal
                    (Matching_wont_refine ("duplicate variable in indices", Some (PNormal (ctx, x))));
                Hashtbl.add seen level ();
                level
            | _ -> fatal (Anomaly "local variable bound to a potential term"))
        | _ ->
            fatal (Matching_wont_refine ("index is not a free variable", Some (PNormal (ctx, x))))
      in
      Reporter.try_with ~fatal:(fun d ->
          match d.message with
          | Matching_wont_refine (str, x) ->
              emit (Matching_wont_refine (str, x));
              check_nondep_match status ctx (Term.Var index) varty brs None motive loc
          | No_such_level x ->
              emit (Matching_wont_refine ("index variable occurs in parameter", Some x));
              check_nondep_match status ctx (Term.Var index) varty brs None motive loc
          | _ -> fatal_diagnostic d)
      @@ fun () ->
      let index_vars =
        Vec.mmap
          (fun [ tm ] -> CubeOf.mmap { map = (fun _ [ x ] -> is_fresh x) } [ tm ])
          [ var_indices ] in
      let inst_vars = TubeOf.mmap { map = (fun _ [ x ] -> is_fresh x) } [ inst_args ] in
      let constr_vars = TubeOf.plus_cube inst_vars (CubeOf.singleton level) in
      (* Now we also check that none of these free variables occur in the parameters.  We do this by altering the context to replace all these level variables with unknowns and doing a readback of the pre-indices type family into that context.  If the readback encounters one of the missing level variables, it fails with No_such_level; above we catch that, emit a hint, and fall back to matching against a term. *)
      (* TODO: This doesn't seem to be catching things it should, like attempted proofs of Axiom K; they go on and get caught by No_permutation instead. *)
      let ctx_noindices = Ctx.forget_levels ctx (Hashtbl.mem seen) in
      discard (readback_nf ctx_noindices tyfam);
      (* If all of those checks succeed, we continue on the path of a variable match.  But note that this call is still inside the try_with, so it can still fail and revert back to a non-dependent term match. *)
      (* We start with a preprocesssing step that pairs each user-provided branch with the corresponding constructor information from the datatype. *)
      let user_branches = merge_branches name brs data_constrs in
      (* We now iterate through the constructors, typechecking the corresponding branches and inserting them in the match tree. *)
      let branches, errs =
        List.fold_left
          (fun (branches, errs)
               ( constr,
                 (Checkable_branch { xs; body; env; argtys; index_terms } :
                   (a, m, ij) checkable_branch) ) ->
            let (Snocs efc) = Tbwd.snocs (Telescope.length argtys) in
            (* Create new level variables for the pattern variables to which the constructor is applied, and add corresponding index variables to the context.  The types of those variables are specified in the telescope argtys, and have to be evaluated at the closure environment 'env' and the previous new variables (this is what ext_tel does).  For a higher-dimensional match, the new variables come with their boundaries in n-dimensional cubes. *)
            let newctx, newenv, newvars, newnfs = ext_tel ctx env xs argtys efc in
            (* Evaluate the "index_terms" at the new pattern variables, obtaining what the indices should be for the new term that replaces the match variable in the match body. *)
            let index_vals =
              Vec.mmap
                (fun [ ixtm ] ->
                  CubeOf.build dim
                    { build = (fun fa -> eval_term (act_env newenv (op_of_sface fa)) ixtm) })
                [ index_terms ] in
            (* Assemble a term consisting of the constructor applied to the new variables, along with its boundary, and their types.  To compute their types, we have to extract the datatype applied to its parameters only, pass to boundaries if necessary, and then re-apply it to the new indices. *)
            let constr_tys = TubeOf.plus_cube tyfam_args (CubeOf.singleton tyfam) in
            let argtbl = Hashtbl.create 10 in
            let constr_nfs =
              CubeOf.mmap
                {
                  map =
                    (fun fa [ constrty ] ->
                      let k = dom_sface fa in
                      let tm = Value.Constr (constr, k, List.map (CubeOf.subcube fa) newvars) in
                      let ty =
                        inst
                          (Vec.fold_left
                             (fun f a -> apply_term f (CubeOf.subcube fa a))
                             constrty.tm index_vals)
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
                }
                [ constr_tys ] in
            let constr_nf = CubeOf.find_top constr_nfs in
            (* Since "index_vals" is just a Bwv of Cubes of *values*, we extract the corresponding collection of *normals* from the type.  The main use of this will be to substitute for the index variables, so instead of assembling them into another Bwv of Cubes, we make a hashtable associating those index variables to the corresponding normals.  We also include in the same hashtable the lower-dimensional applications of the same constructor, to be substituted for the instantiation variables. *)
            match view_type constr_nf.ty "check_var_match (inner)" with
            | Canonical (_, Data { dim = constrdim; indices = Filled indices; _ }, _) -> (
                match
                  ( D.compare constrdim dim,
                    Fwn.compare (Vec.length index_terms) (Vec.length indices) )
                with
                | Neq, _ -> fatal (Anomaly "created datatype has wrong dimension")
                | _, Neq -> fatal (Anomaly "created datatype has wrong number of indices")
                | Eq, Eq -> (
                    let new_vals = Hashtbl.create 10 in
                    CubeOf.miter
                      { it = (fun _ [ v; c ] -> Hashtbl.add new_vals v c) }
                      [ constr_vars; constr_nfs ];
                    Vec.miter
                      (fun [ vs; cs ] ->
                        CubeOf.miter
                          { it = (fun _ [ v; c ] -> Hashtbl.add new_vals v c) }
                          [ vs; cs ])
                      [ index_vars; indices ];
                    (* Now we let-bind the match variable to the constructor applied to these new variables, the "index_vars" to the index values, and the inst_vars to the boundary constructor values.  The operation Ctx.bind_some automatically substitutes these new values into the types and values of other variables in the context, and reorders it if necessary so that each variable only depends on previous ones. *)
                    match Bindsome.bind_some (Hashtbl.find_opt new_vals) newctx with
                    | None ->
                        fatal (Matching_wont_refine ("no consistent permutation of context", None))
                    | Bind_some { checked_perm; oldctx; newctx } -> (
                        (* We readback the index and instantiation values into this new context and discard the result, catching No_such_level to turn it into a user Error.  This has the effect of doing an occurs-check that none of the index variables occur in any of the index values.  This is a bit less general than the CDP Solution rule, which (when applied one variable at a time) prohibits only cycles of occurrence.  Note that this exception is still caught by check_var_match, above, causing a fallback to term matching. *)
                        ( Reporter.try_with ~fatal:(fun d ->
                              match d.message with
                              | No_such_level x ->
                                  fatal
                                    (Matching_wont_refine
                                       ("free index variable occurs in inferred index value", Some x))
                              | _ -> fatal_diagnostic d)
                        @@ fun () ->
                          Hashtbl.iter (fun _ v -> discard (readback_nf oldctx v)) new_vals );
                        (* The type of the match must be specialized in the branches by substituting different constructors for the match variable, as well as the index values for the index variables, and lower-dimensional versions of each constructor for the instantiation variables.  Thus, we readback-eval this type into the new context, to obtain the type at which the branch body will be checked. *)
                        let newty = eval_term (Ctx.env newctx) (readback_val oldctx motive) in
                        (* Now we have to modify the "status" data by readback-eval on the arguments and adding a hypothesized current branch to the match.  *)
                        let eval_readback_args x =
                          let tm = eval_term (Ctx.env newctx) (readback_nf oldctx x) in
                          let ty = eval_term (Ctx.env newctx) (readback_val oldctx x.ty) in
                          { tm; ty } in
                        let perm = checked_perm in
                        let status =
                          make_match_status status (Term.Var index) dim branches efc
                            (Some eval_readback_args) perm constr in
                        (* Finally, we typecheck the "body" of the branch, if the user supplied one. *)
                        match body with
                        | Some body ->
                            (* We catch and accumulate errors so that later branches can continue to be checked and produce their own errors even if earlier ones fail, but we pass through the errors that are getting caught elsewhere. *)
                            Reporter.try_with ~fatal:(fun e ->
                                match e.message with
                                | Missing_constructor_in_match _ -> fatal_diagnostic e
                                | _ -> (branches, Snoc (errs, e)))
                            @@ fun () ->
                            let branch = check status newctx body newty in
                            ( branches |> Constr.Map.add constr (Term.Branch (efc, perm, branch)),
                              errs )
                        (* If not, then we look for something to refute. *)
                        | None ->
                            (* First we check whether any of the new pattern variables created by this match belong to an empty datatype. *)
                            if
                              any_empty newnfs
                              ||
                              (* Otherwise, we check the stored "refutables", which include all the previous and succeeding pattern variables. *)
                              List.fold_left
                                (fun s x ->
                                  if s then true
                                  else
                                    let _, sty = synth (Kinetic `Nolet) newctx x in
                                    is_empty sty)
                                false
                                (Option.fold
                                   ~some:(fun r -> r.refutables (Namevec.bplus xs))
                                   ~none:[] refutables)
                              (* If we found something to refute, we mark this branch as refuted in the compiled match. *)
                            then (branches |> Constr.Map.add constr Term.Refute, errs)
                            else fatal (Missing_constructor_in_match constr))))
            | _ -> fatal (Anomaly "created datatype is not canonical?"))
          (Constr.Map.empty, Emp) user_branches in
      match errs with
      | Snoc _ -> fatal (Accumulated ("check_var_match", errs))
      | Emp -> Match { tm = Term.Var index; dim; branches })
  | _ -> fatal ?loc (Matching_on_nondatatype (PVal (ctx, varty)))

and make_match_status : type a b ab c n.
    (a, potential) status ->
    (a, kinetic) term ->
    n D.t ->
    (a, n) Term.branch Constr.Map.t ->
    (a, b, n, ab) Tbwd.snocs ->
    (normal -> normal) option ->
    (c, ab) Tbwd.permute ->
    Constr.t ->
    (c, potential) status =
 fun status newtm dim branches efc eval_readback perm constr ->
  match status with
  | Potential (c, args, hyp) ->
      let args =
        match eval_readback with
        | Some eval_readback ->
            Bwd.map
              (function
                | Value.App (Arg xs, ins) ->
                    Value.App
                      (Arg (CubeOf.mmap { map = (fun _ [ x ] -> eval_readback x) } [ xs ]), ins)
                | fld -> fld)
              args
        | None -> args in
      let hyp tm =
        let branches = branches |> Constr.Map.add constr (Term.Branch (efc, perm, tm)) in
        hyp (Term.Match { tm = newtm; dim; branches }) in
      Potential (c, args, hyp)

(* Try matching against all the supplied terms with zero branches, producing an empty match if any succeeds and raising an error if none succeed. *)
and check_refute : type a b.
    (b, potential) status ->
    (a, b) Ctx.t ->
    a synth located list ->
    kinetic value ->
    [ `Explicit | `Implicit ] ->
    Constr.t option ->
    (b, potential) term =
 fun status ctx tms ty i missing ->
  match tms with
  | [] -> (
      match i with
      | `Implicit -> fatal (Anomaly "no discriminees to refute")
      | `Explicit -> fatal Invalid_refutation)
  (* If all the possibilities fail, we want to report a "missing constructor" error for the particular constructor supplied as an argument, if any, which comes from the first place where the refutation began. *)
  | [ tm ] ->
      let stm, sty = synth (Kinetic `Nolet) ctx tm in
      Reporter.try_with
        (fun () -> check_nondep_match status ctx stm sty Emp None ty tm.loc)
        ~fatal:(fun d ->
          match d.message with
          | Missing_constructor_in_match c -> (
              match (i, missing) with
              | `Explicit, _ -> fatal Invalid_refutation
              | `Implicit, Some missing -> fatal (Missing_constructor_in_match missing)
              | `Implicit, None -> fatal (Missing_constructor_in_match c))
          | _ -> fatal_diagnostic d)
  | tm :: (_ :: _ as tms) ->
      let stm, sty = synth (Kinetic `Nolet) ctx tm in
      Reporter.try_with
        (fun () -> check_nondep_match status ctx stm sty Emp None ty tm.loc)
        ~fatal:(fun d ->
          match d.message with
          | Missing_constructor_in_match c ->
              check_refute status ctx tms ty i (Some (Option.value missing ~default:c))
          | _ -> fatal_diagnostic d)

(* Try empty-matching against each successive domain in an iterated pi-type. *)
and check_empty_match_lam : type a b.
    (a, b) Ctx.t -> kinetic value -> [ `First | `Notfirst ] -> (b, potential) term =
 fun ctx ty first ->
  match view_type ty "check_empty_match_lam" with
  | Pi (type k) ((_, doms, cods, tyargs) : _ * (k, kinetic value) CubeOf.t * _ * _) -> (
      let dim = CubeOf.dim doms in
      let newargs, newnfs = dom_vars (Ctx.length ctx) doms in
      let output = tyof_app cods tyargs newargs in
      let module S = struct
        type 'c t = Ok : kinetic value option * (a, 'c, 'ac) N.plus * k sface_of option -> 'c t
      end in
      let module Build = NICubeOf.Traverse (S) in
      match
        Build.build_left dim
          {
            build =
              (fun fb -> function
                | Ok (firstty, ab, fa) ->
                    let ty = (Binding.value (CubeOf.find newnfs fb)).ty in
                    let firstty = Option.value firstty ~default:ty in
                    if is_empty ty then
                      Fwrap (NFamOf None, Ok (Some firstty, Suc ab, Some (SFace_of fb)))
                    else Fwrap (NFamOf None, Ok (Some firstty, Suc ab, fa)));
          }
          (Ok (None, Zero, None))
      with
      | Wrap (names, Ok (firstty, af, fa)) -> (
          let xs = Variables (D.zero, D.zero_plus dim, names) in
          let ctx = Ctx.vis ctx D.zero (D.zero_plus dim) names newnfs af in
          match (fa, first) with
          | Some (SFace_of fa), _ ->
              Lam (xs, Match { tm = Var (Index (Now, fa)); dim; branches = Constr.Map.empty })
          | None, `Notfirst -> Term.Lam (xs, check_empty_match_lam ctx output `Notfirst)
          | None, `First ->
              Reporter.try_with
                (fun () -> Term.Lam (xs, check_empty_match_lam ctx output `Notfirst))
                ~fatal:(fun d ->
                  match d.message with
                  | Invalid_refutation -> (
                      let firstty = firstty <|> Anomaly "missing firstty in checking []" in
                      match view_type firstty "is_empty" with
                      | Canonical (_, Data { constrs; _ }, _) ->
                          fatal (Missing_constructor_in_match (fst (Bwd_extra.head constrs)))
                      | _ -> fatal (Matching_on_nondatatype (PVal (ctx, firstty))))
                  | _ -> fatal_diagnostic d)))
  | _ -> fatal Invalid_refutation

and is_empty (varty : kinetic value) : bool =
  match view_type varty "is_empty" with
  | Canonical (_, Data { constrs = Emp; _ }, _) -> true
  | _ -> false

and any_empty : type n. (n, Binding.t) CubeOf.t list -> bool =
 fun nfss ->
  let module CM = CubeOf.Monadic (Monad.State (Bool)) in
  List.fold_left
    (fun s nfs ->
      snd (CM.miterM { it = (fun _ [ x ] s -> ((), s || is_empty (Binding.value x).ty)) } [ nfs ] s))
    false nfss

and check_data : type a b i.
    discrete:unit Constant.Map.t option ->
    (b, potential) status ->
    (a, b) Ctx.t ->
    kinetic value ->
    i Fwn.t ->
    (Constr.t, (b, i) Term.dataconstr) Abwd.t ->
    (Constr.t * a Raw.dataconstr located) list ->
    Code.t Asai.Diagnostic.t Bwd.t ->
    (b, potential) term =
 fun ~discrete status ctx ty num_indices checked_constrs raw_constrs errs ->
  match (raw_constrs, status) with
  | [], Potential _ -> (
      match errs with
      | Snoc _ -> fatal (Accumulated ("check_data", errs))
      | Emp ->
          (* If we get to this point and discreteness is still a possibility, we mark it as "Maybe" discrete.  Later, after all the types in a mutual block are checked, if they're all discrete we go through and change the "Maybe"s to "Yes"es.  *)
          let discrete = Option.fold ~none:`No ~some:(fun _ -> `Maybe) discrete in
          Canonical (Data { indices = num_indices; constrs = checked_constrs; discrete }))
  | ( (c, { value = Dataconstr (args, output); loc }) :: raw_constrs,
      Potential (head, current_apps, hyp) ) -> (
      with_loc loc @@ fun () ->
      (* Temporarily bind the current constant to the up-until-now value, for recursive purposes, and also for specifying the output types for indexed inductive families (and presumably, one day, for higher inductive types). *)
      run_with_definition head
        (hyp
           (Term.Canonical
              (Data { indices = num_indices; constrs = checked_constrs; discrete = `No })))
        Emp
      @@ fun () ->
      match (Abwd.find_opt c checked_constrs, output) with
      | Some _, _ -> fatal (Duplicate_constructor_in_data c)
      | None, Some output ->
          let disc, (checked_constrs : (Constr.t, (b, i) Term.dataconstr) Abwd.t), errs =
            Reporter.try_with ~fatal:(fun e -> (true, checked_constrs, Snoc (errs, e))) @@ fun () ->
            let Checked_tel (args, newctx), disc = check_tel ?discrete ctx args in
            (* Note the type of each field is checked *kinetically*: it's not part of the case tree. *)
            let coutput = check (Kinetic `Nolet) newctx output (universe D.zero) in
            match eval_term (Ctx.env newctx) coutput with
            | Uninst (Neu { head = Const { name = out_head; ins }; args = out_apps; value = _ }, _)
              -> (
                match head with
                | Constant (cc, n) when cc = out_head && Option.is_some (is_id_ins ins) -> (
                    match D.compare_zero n with
                    | Pos _ ->
                        fatal ?loc:output.loc
                          (Unimplemented "indexed inductive types nested inside higher comatches")
                    | Zero -> (
                        let (Wrap indices) =
                          get_indices newctx c (Bwd.to_list current_apps) (Bwd.to_list out_apps)
                            output.loc in
                        match Fwn.compare (Vec.length indices) num_indices with
                        | Eq ->
                            ( disc,
                              checked_constrs |> Abwd.add c (Term.Dataconstr { args; indices }),
                              errs )
                        | _ ->
                            (* I think this shouldn't ever happen, no matter what the user writes, since we know at this point that the output is a full application of the correct constant, so it must have the right number of arguments. *)
                            fatal (Anomaly "length of indices mismatch")))
                | _ -> fatal ?loc:output.loc (Invalid_constructor_type c))
            | _ -> fatal ?loc:output.loc (Invalid_constructor_type c) in
          check_data
            ~discrete:(if disc then discrete else None)
            status ctx ty num_indices checked_constrs raw_constrs errs
      | None, None -> (
          match num_indices with
          | Zero ->
              let disc, (checked_constrs : (Constr.t, (b, i) Term.dataconstr) Abwd.t), errs =
                Reporter.try_with ~fatal:(fun e -> (true, checked_constrs, Snoc (errs, e)))
                @@ fun () ->
                let Checked_tel (args, _), disc = check_tel ?discrete ctx args in
                (disc, checked_constrs |> Abwd.add c (Term.Dataconstr { args; indices = [] }), errs)
              in
              check_data
                ~discrete:(if disc then discrete else None)
                status ctx ty Fwn.zero checked_constrs raw_constrs errs
          | Suc _ -> fatal (Missing_constructor_type c)))

and get_indices : type a b.
    (a, b) Ctx.t ->
    Constr.t ->
    app list ->
    app list ->
    Asai.Range.t option ->
    (b, kinetic) term Vec.wrapped =
 fun ctx c current output loc ->
  with_loc loc @@ fun () ->
  match (current, output) with
  | arg1 :: current, arg2 :: output -> (
      match equal_arg (Ctx.length ctx) arg1 arg2 with
      | Some () -> get_indices ctx c current output loc
      | None -> fatal (Invalid_constructor_type c))
  | [], _ ->
      Vec.of_list_map
        (function
          | Value.App (Arg arg, ins) -> (
              match is_id_ins ins with
              | Some _ -> (
                  match D.compare (CubeOf.dim arg) D.zero with
                  | Eq -> readback_nf ctx (CubeOf.find_top arg)
                  | Neq -> fatal (Invalid_constructor_type c))
              | None -> fatal (Invalid_constructor_type c))
          | Value.App (Field _, _) -> fatal (Anomaly "field is not an index"))
        output
  | _ -> fatal (Invalid_constructor_type c)

(* The common prefix of checking a codatatype or record type, which returns a (cube of) variables belonging to the up-until-now type so that later fields can refer to earlier ones.  It also dynamically binds the current constant or metavariable, if possible, to that value for recursive purposes.  Since this binding has to scope over the rest of the functions that are specific to codata or records, it uses CPS. *)
and with_codata_so_far : type a b n c et.
    (b, potential) status ->
    (potential, et) eta ->
    (a, b) Ctx.t ->
    opacity ->
    n D.t ->
    (D.zero, n, n, normal) TubeOf.t ->
    (b * n * et) Term.CodatafieldAbwd.t ->
    has_higher_fields:unit option ->
    Code.t Asai.Diagnostic.t Bwd.t ->
    ((n, Ctx.Binding.t) CubeOf.t -> (b, potential) term -> c) ->
    c =
 fun (Potential (h, args, hyp)) eta ctx opacity dim tyargs checked_fields ~has_higher_fields errs
     cont ->
  let domvars, termctx =
    match errs with
    | Emp ->
        (* We can always create a constant with the (0,0,0) insertion, even if its dimension is actually higher. *)
        let head = head_of_potential h in
        let rec domvars () =
          let value =
            Value.Canonical
              (Codata
                 {
                   eta;
                   opacity;
                   env = Ctx.env ctx;
                   ins = zero_ins dim;
                   fields = checked_fields;
                   termctx = lazy (termctx ());
                 }) in
          let prev_ety =
            Uninst
              (Neu { head; args; value = ready value }, Lazy.from_val (inst (universe dim) tyargs))
          in
          snd
            (dom_vars (Ctx.length ctx)
               (TubeOf.plus_cube
                  (TubeOf.mmap { map = (fun _ [ nf ] -> nf.tm) } [ tyargs ])
                  (CubeOf.singleton prev_ety)))
        and termctx () =
          let newctx = Ctx.cube_vis ctx None (domvars ()) in
          Option.map (fun () -> readback_ctx newctx) has_higher_fields in
        (domvars (), termctx ())
    | Snoc _ ->
        let msg =
          match eta with
          | Eta -> "record dependent"
          | Noeta -> "codata dependent" in
        (CubeOf.build dim { build = (fun _ -> Ctx.Binding.error (Accumulated (msg, Emp))) }, None)
  in
  let codataterm = Term.Canonical (Codata { eta; opacity; dim; fields = checked_fields; termctx }) in
  run_with_definition h (hyp codataterm) errs @@ fun () -> cont domvars codataterm

and check_codata : type a b n.
    (b, potential) status ->
    (a, b) Ctx.t ->
    (D.zero, n, n, normal) TubeOf.t ->
    (b * n * no_eta) Term.CodatafieldAbwd.t ->
    (Field.wrapped * a Raw.codatafield) list ->
    Code.t Asai.Diagnostic.t Bwd.t ->
    has_higher_fields:unit option ->
    (b, potential) term =
 fun status ctx tyargs checked_fields raw_fields errs ~has_higher_fields ->
  let dim = TubeOf.inst tyargs in
  match raw_fields with
  | [] -> (
      match errs with
      | Emp ->
          with_codata_so_far status Noeta ctx `Opaque dim tyargs checked_fields ~has_higher_fields
            errs
          @@ fun _ codataterm -> codataterm
      | Snoc _ -> fatal (Accumulated ("check_codata", errs)))
  | (Wrap fld, Codatafield (x, rty)) :: raw_fields -> (
      with_codata_so_far status Noeta ctx `Opaque dim tyargs checked_fields ~has_higher_fields errs
      @@ fun domvars _ ->
      let newctx = Ctx.cube_vis ctx x domvars in
      match (D.compare_zero (Field.dim fld), D.compare_zero (TubeOf.inst tyargs)) with
      | Zero, _ ->
          let checked_fields, errs =
            Reporter.try_with ~fatal:(fun e -> (checked_fields, Snoc (errs, e))) @@ fun () ->
            (* Note the type of each field is checked *kinetically*: it's not part of the case tree. *)
            let cty = check (Kinetic `Nolet) newctx rty (universe D.zero) in
            (Snoc (checked_fields, Entry (fld, Lower cty)), errs) in
          check_codata status ctx tyargs checked_fields raw_fields errs ~has_higher_fields
      | Pos _, Zero ->
          let (Degctx (plusmap, degctx, _)) = degctx newctx (Field.dim fld) in
          let checked_fields, errs =
            Reporter.try_with ~fatal:(fun e -> (checked_fields, Snoc (errs, e))) @@ fun () ->
            (* Note the type of each field is checked *kinetically*: it's not part of the case tree. *)
            let cty = check (Kinetic `Nolet) degctx rty (universe D.zero) in
            (Snoc (checked_fields, Entry (fld, Codatafield.Higher (plusmap, cty))), errs) in
          check_codata status ctx tyargs checked_fields raw_fields errs ~has_higher_fields
      | Pos _, Pos _ -> fatal (Unimplemented "higher fields in higher-dimensional codatatypes"))

and check_record : type a f1 f2 f af d acd b n.
    (b, potential) status ->
    n D.t ->
    (a, b) Ctx.t ->
    opacity ->
    (D.zero, n, n, normal) TubeOf.t ->
    (N.zero, n, string option, f1) NICubeOf.t ->
    (D.zero Field.t * string, f2) Bwv.t ->
    (f1, f2, f) N.plus ->
    (a, f, af) N.plus ->
    (b * n * has_eta) Term.CodatafieldAbwd.t ->
    (af, d, acd) Raw.tel ->
    Code.t Asai.Diagnostic.t Bwd.t ->
    (b, potential) term =
 fun status dim ctx opacity tyargs vars ctx_fields fplus af checked_fields raw_fields errs ->
  match raw_fields with
  | Emp -> (
      match errs with
      | Snoc _ -> fatal (Accumulated ("check_record", errs))
      | Emp ->
          Term.Canonical
            (Codata { eta = Eta; opacity; dim; fields = checked_fields; termctx = None }))
  | Ext (None, _, _) -> fatal (Anomaly "unnamed field in check_record")
  | Ext (Some name, rty, raw_fields) ->
      with_codata_so_far status Eta ctx opacity dim tyargs checked_fields ~has_higher_fields:None
        errs
      @@ fun domvars _ ->
      let fld = Field.intern name D.zero in
      let checked_fields, ctx_fields, errs =
        Reporter.try_with ~fatal:(fun e ->
            (checked_fields, Bwv.Snoc (ctx_fields, (fld, name)), Snoc (errs, e)))
        @@ fun () ->
        let newctx = Ctx.vis_fields ctx vars domvars ctx_fields fplus af in
        let cty = check (Kinetic `Nolet) newctx rty (universe D.zero) in
        (Snoc (checked_fields, Entry (fld, Lower cty)), Bwv.Snoc (ctx_fields, (fld, name)), errs)
      in
      check_record status dim ctx opacity tyargs vars ctx_fields (Suc fplus) (Suc af) checked_fields
        raw_fields errs

and check_struct : type a b c d s m n mn et.
    (b, s) status ->
    (s, et) eta ->
    (a, b) Ctx.t ->
    (* The type we are checking against *)
    kinetic value ->
    (* m is the dimension to which that type has been substituted, and n is the Gel dimension of that type. *)
    m D.t ->
    (m, n, mn) D.plus ->
    (mn, m, n, d, c, et) codata_args ->
    (D.zero, mn, mn, normal) TubeOf.t ->
    (* The fields supplied by the user *)
    ((string * string list) option, a check located) Abwd.t ->
    (b, s) term =
 fun status eta ctx ty m mn ({ fields; _ } as codata_args) tyargs tms ->
  (* The type of each record field, at which we check the corresponding field supplied in the struct, is the type associated to that field name in general, evaluated at the supplied parameters and at "the term itself".  We don't have the whole term available while typechecking, of course, but we can build a version of it that contains all the previously typechecked fields, which is all we need for a well-typed record.  So we iterate through the fields (in the order specified in the *type*, since that determines the dependencies) while also accumulating the previously typechecked and evaluated fields.  At the end, we throw away the evaluated fields (although as usual, that seems wasteful).  Note that check_fields returns a modified version of the *user* fields 'tms', since it may need to resolve positional fields to named ones. *)
  let tms, ctms =
    check_fields status eta ctx ty m mn codata_args
      (* We convert the backwards alist of fields and types into a forwards list, for forwards recursion.  This should contain each field name only once, even for higher fields, since it comes from the codatatype where all the instances of a higher field are grouped into a pbijmap. *)
      (Bwd.to_list fields)
      tyargs
      (Abwd.map (fun { value; loc } -> { value = Some value; loc }) tms)
      Emp Emp Emp in
  (* We had to typecheck the fields in the order given in the record type, since later ones might depend on earlier ones.  But then we re-order them back to the order given in the struct, to match what the user wrote. *)
  let fields, errs =
    Bwd.fold_left
      (fun (fields, errs) -> function
        (* If the term is still there, or if there are any remaining unlabeled fields, they are extra. *)
        | Some fldins, { value = Some _; loc = tmloc } ->
            (fields, Snoc (errs, diagnostic ?loc:tmloc (extra_field_in_struct eta fldins)))
        | None, tm -> (fields, Snoc (errs, diagnostic ?loc:tm.loc (Extra_field_in_tuple None)))
        | Some (fld, _), { value = None; loc = tmloc } -> (
            (* In the case of higher fields, the same field name will appear more than once in tms, but it will appear only once in the returned ctms; thus we take it only if it hasn't already been taken. *)
            match
              ( Term.StructfieldAbwd.find_string_opt fields fld,
                Term.StructfieldAbwd.find_string_opt ctms fld )
            with
            | Some _, _ -> (fields, errs)
            | None, Some x -> (Snoc (fields, x), errs)
            | None, None ->
                fatal ?loc:tmloc (Anomaly "taken raw field didn't end up in checked fields")))
      (Emp, Emp) tms in
  match errs with
  | Emp -> Term.Struct (eta, m, fields, energy status)
  | Snoc _ -> fatal (Accumulated ("check_struct", errs))

and check_fields : type a b c d s m n mn et.
    (b, s) status ->
    (s, et) eta ->
    (a, b) Ctx.t ->
    (* As before, the type, its substitution dimension, its Gel dimension, and its arguments *)
    kinetic value ->
    m D.t ->
    (m, n, mn) D.plus ->
    (mn, m, n, d, c, et) codata_args ->
    (* The fields from the codatatype, to be checked against *)
    (c * n * et) Term.CodatafieldAbwd.entry list ->
    (D.zero, mn, mn, normal) TubeOf.t ->
    (* The fields supplied by the user *)
    ((string * string list) option, a check option located) Abwd.t ->
    (* The fields we have checked so far *)
    (m * b * s * et) Term.StructfieldAbwd.t ->
    (* Evaluated versions of the fields we have checked so far *)
    (m * s * et) Value.StructfieldAbwd.t ->
    (* Errors we have accumulated so far *)
    Code.t Asai.Diagnostic.t Bwd.t ->
    ((string * string list) option, a check option located) Abwd.t
    * (m * b * s * et) Term.StructfieldAbwd.t =
 fun status eta ctx ty m mn codata_args fields tyargs tms ctms etms errs ->
  (* Build a temporary value-struct consisting of the so-far checked and evaluated fields.  The insertion on a struct being checked is the identity, but it stores the substitution dimension of the type being checked against.  If this is a higher-dimensional record (e.g. Gel), there could be a nontrivial right dimension being trivially inserted, but that will get added automatically by an appropriate symmetry action if it happens. *)
  let str = Value.Struct (etms, ins_zero m, energy status) in
  match (fields, status) with
  | [], _ -> (
      (* If there are no more fields to check, we return.  We have accumulated a Bwd of errors as we progress through the fields, allowing later fields to typecheck (and, more importantly, produce their own meaningful error messages) even if earlier fields already failed.  Then at the end, if there are any such errors, we raise them all together.  *)
      match errs with
      | Emp -> (tms, ctms)
      | Snoc _ -> fatal (Accumulated ("check_struct", errs)))
  | Entry (fld, cdf) :: fields, Potential (name, args, hyp) ->
      (* Temporarily bind the current constant to the up-until-now value (or an error, if any have occurred yet), for (co)recursive purposes.  Note that this means as soon as one field fails, no other fields can be typechecked if they depend *at all* on earlier ones, even ones that didn't fail.  This could be improved in the future. *)
      run_with_definition name (hyp (Term.Struct (eta, m, ctms, energy status))) errs @@ fun () ->
      (* The insertion on the *constant* being checked, by contrast, is always zero, since the constant is not nontrivially substituted at all yet. *)
      let head = head_of_potential name in
      (* The up-until-now term is also maybe an error. *)
      let prev_etm =
        unless_error (Uninst (Neu { head; args; value = ready (Val str) }, Lazy.from_val ty)) errs
      in
      check_field status eta ctx ty m mn codata_args fields tyargs fld cdf prev_etm tms ctms etms
        errs
  | Entry (fld, cdf) :: fields, Kinetic _ ->
      let prev_etm = unless_error str errs in
      check_field status eta ctx ty m mn codata_args fields tyargs fld cdf prev_etm tms ctms etms
        errs

and check_field : type a b c d s m n mn i et.
    (b, s) status ->
    (s, et) eta ->
    (a, b) Ctx.t ->
    (* As before, the type, its dimensions, and its arguments *)
    kinetic value ->
    m D.t ->
    (m, n, mn) D.plus ->
    (mn, m, n, d, c, et) codata_args ->
    (c * n * et) Term.CodatafieldAbwd.entry list ->
    (D.zero, mn, mn, normal) TubeOf.t ->
    (* The field being checked, by name and by data from the codatatype *)
    i Field.t ->
    (i, c * n * et) Term.Codatafield.t ->
    (* The up-until-now term being checked *)
    (kinetic value, Code.t) Result.t ->
    (* As before, user terms, checked terms, value terms, and errors *)
    ((string * string list) option, a check option located) Abwd.t ->
    (m * b * s * et) Term.StructfieldAbwd.t ->
    (m * s * et) Value.StructfieldAbwd.t ->
    Code.t Asai.Diagnostic.t Bwd.t ->
    ((string * string list) option, a check option located) Abwd.t
    * (m * b * s * et) Term.StructfieldAbwd.t =
 fun status eta ctx ty m mn ({ env; termctx; _ } as codata_args) fields tyargs fld cdf prev_etm tms
     ctms etms errs ->
  match (cdf, status, eta, termctx) with
  | Lower fldty, _, _, _ ->
      let ins = ins_zero m in
      let mkstatus lbl : (b, s) status -> (b, s) status = function
        | Kinetic l -> Kinetic l
        | Potential (c, args, hyp) ->
            let args = Snoc (args, App (Field (fld, D.plus_zero m), ins)) in
            let hyp tm =
              let ctms = Snoc (ctms, Entry (fld, Lower (tm, lbl))) in
              hyp (Term.Struct (eta, m, ctms, energy status)) in
            Potential (c, args, hyp) in
      let key = Some (Field.to_string fld, []) in
      let tm, tms, lbl =
        match Abwd.find_opt_and_update key key (fun x -> locate_opt x.loc None) tms with
        | Some ({ value = Some tm; loc }, tms) -> ({ value = tm; loc }, tms, `Labeled)
        | Some ({ value = None; _ }, _) -> fatal (Anomaly "accessing same field twice")
        | None -> (
            match Abwd.find_opt_and_update None key (fun x -> locate_opt x.loc None) tms with
            | Some ({ value = Some tm; loc }, tms) -> ({ value = tm; loc }, tms, `Unlabeled)
            | Some ({ value = None; _ }, _) -> fatal (Anomaly "accessing same field twice")
            | None -> fatal (missing_field_in_struct eta fld)) in
      let etms, ctms, errs =
        (* We trap any errors produced by 'check', adding them instead to the list of accumulated errors and going on.  Note that if any previous fields that have already failed, then prev_etm will be bound to an error value, and so if the type of this field depends on the value of any previous one, tyof_field will raise that error, which we catch and add to the list; but it will be (Accumulated Emp) so it won't be displayed to the user. *)
        Reporter.try_with ~fatal:(fun e -> (etms, ctms, Snoc (errs, e))) @@ fun () ->
        (* We don't need the error-checking of tyof_field, since we are getting our fields directly from the codatatype definition and so we already know that they have the right dimensions.  So we can call directly into the helper function tyof_lower_codatafield.  Note that we pass it prev_etm, env, and tyargs that consist of values in the old context, but the return value ety is in the new degenerated context. *)
        let ety = tyof_lower_codatafield prev_etm fld fldty env tyargs m mn in
        let ctm = check (mkstatus lbl status) ctx tm ety in
        let etms = Snoc (etms, Entry (fld, Lower (lazy_eval (Ctx.env ctx) ctm, lbl))) in
        let ctms = Snoc (ctms, Entry (fld, Lower (ctm, lbl))) in
        (etms, ctms, errs) in
      check_fields status eta ctx ty m mn codata_args fields tyargs tms ctms etms errs
  | Higher (ic0, fldty), Potential _, Noeta, (lazy (Some termctx)) ->
      let Eq = D.plus_uniq mn (D.plus_zero m) in
      let i = Field.dim fld in
      check_higher_field status ctx ty m i codata_args fields termctx tyargs tms ctms etms errs fld
        (PlusPbijmap.build m i { build = (fun _ -> PlusFam None) })
        (InsmapOf.build m i { build = (fun _ -> None) })
        (all_pbij_between m i) prev_etm ic0 fldty
  | Higher _, Potential _, _, (lazy None) ->
      fatal (Anomaly "missing termctx in codatatype with higher fields")
  | Higher _, Kinetic _, _, _ -> .

and check_higher_field : type a b c d m i ic0.
    (b, potential) status ->
    (a, b) Ctx.t ->
    (* Type being checked against and its data *)
    kinetic value ->
    (* m = substitution dimension, i = intrinsic dimension *)
    m D.t ->
    i D.t ->
    (m, m, D.zero, d, c, no_eta) codata_args ->
    (c * D.zero * no_eta) Term.CodatafieldAbwd.entry list ->
    (d, (c, D.zero) snoc) termctx ->
    (D.zero, m, m, normal) TubeOf.t ->
    (* As before, user terms, checked terms, value terms, and errors *)
    ((string * string list) option, a check option located) Abwd.t ->
    (m * b * potential * no_eta) Term.StructfieldAbwd.t ->
    (m * potential * no_eta) Value.StructfieldAbwd.t ->
    Code.t Asai.Diagnostic.t Bwd.t ->
    (* Field being checked *)
    i Field.t ->
    (* Values of this field checked so far, as terms *)
    (m, i, b) PlusPbijmap.t ->
    (* Evaluated versions of those of them that are insertions (hence can be used) *)
    (m, i, potential lazy_eval option) InsmapOf.t ->
    (* Remaining pbijs to check *)
    (m, i) pbij_between Seq.t ->
    (* Term-up-until-now *)
    (kinetic value, Code.t) Result.t ->
    (* The unevaluated type of the current field being checked. *)
    (i, (c, D.zero) snoc, ic0) Plusmap.t ->
    (ic0, kinetic) term ->
    ((string * string list) option, a check option located) Abwd.t
    * (m * b * potential * no_eta) Term.StructfieldAbwd.t =
 fun status ctx ty m intrinsic ({ env; _ } as codata_args) fields termctx tyargs tms ctms etms errs
     fld cvals evals pbijs prev_etm ic0 fldty ->
  (* We recurse through all the partial bijections that could be associated to this field name. *)
  match Seq.uncons pbijs with
  | Some
      ( Pbij_between
          (type r)
          (Pbij (type s h) ((fldins, fldshuf) : (m, s, h) insertion * (r, h, i) shuffle) as pbij :
            (m, i, r) pbij),
        pbijs ) ->
      (* Degenerate the context by the number of remaining dimensions for this partial bijection *)
      let r = remaining pbij in
      let (Degctx
             (type rb)
             ((plusmap, degctx, degenv) : (r, b, rb) Plusmap.t * (a, rb) Ctx.t * (r, b) env)) =
        degctx ctx r in
      (* To make a new status, the arguments need to be eval-readbacked into degctx, and for that to make sense the head needs to be higher-dimensional also. *)
      let newstatus : (rb, potential) status =
        match status with
        | Potential
            (type aa)
            ((head, args, hyp) :
              aa potential_head * app Bwd.t * ((b, potential) term -> (aa, potential) term)) ->
            (* We increase the dimension of the potential_head, and also compute a value for the head.  This value is in the *old* context (not the degenerated one)! *)
            let head : aa potential_head =
              match head with
              | Constant (c, n) ->
                  let (Plus rn) = D.plus n in
                  Constant (c, D.plus_out r rn)
              | Meta (meta, metaenv) ->
                  let (Plus rn) = D.plus (dim_env metaenv) in
                  let d = Global.find_meta meta in
                  (* In the case of a metavariable, we eval-readback its stored environment to raise it to degctx. *)
                  Meta (meta, eval_env degenv rn (readback_env ctx metaenv d.termctx)) in
            (* We also eval-readback the args to raise them to degctx. *)
            let args =
              Bwd.map
                (function
                  | Value.App (Field (f, nk), appins) ->
                      let n = cod_left_ins appins in
                      let (Plus rn) = D.plus n in
                      let (Plus rn_k) = D.plus (D.plus_right nk) in
                      let (Plus r_nz) = D.plus (dom_ins appins) in
                      let newins = plus_ins r r_nz rn appins in
                      Value.App (Field (f, rn_k), newins)
                  | App (type n nz z) ((Arg arg, appins) : n arg * (nz, n, z) insertion) ->
                      let n = CubeOf.dim arg in
                      let (Plus rn) = D.plus n in
                      let (Plus r_nz) = D.plus (dom_ins appins) in
                      let newins = plus_ins r r_nz rn appins in
                      (* First we readback the terms and types. *)
                      let [ tms; tys ] =
                        CubeOf.pmap
                          { map = (fun _ [ x ] -> [ readback_nf ctx x; readback_val ctx x.ty ]) }
                          [ arg ] (Cons (Cons Nil)) in
                      (* Now we evaluate them in degenv to increase the dimension.  *)
                      let etms = eval_args degenv rn (D.plus_out r rn) tms in
                      let etys = eval_args degenv rn (D.plus_out r rn) tys in
                      (* Now we have to reassociate the terms with the types to make a new cube of normals.  This is like norm_of_vals_cube, except that the types are already instantiated to dimension n, and we have only to instantiate them the rest of the way at dimension r. *)
                      let new_tm_tbl = Hashtbl.create 10 in
                      let newarg =
                        CubeOf.mmap
                          {
                            map =
                              (fun fab [ tm; ty ] ->
                                let (SFace_of_plus (ml, fa, fb)) = sface_of_plus rn fab in
                                let instargs =
                                  TubeOf.build D.zero
                                    (D.zero_plus (dom_sface fa))
                                    {
                                      build =
                                        (fun fc ->
                                          let (Plus kl) = D.plus (D.plus_right ml) in
                                          Hashtbl.find new_tm_tbl
                                            (SFace_of
                                               (sface_plus_sface
                                                  (comp_sface fa (sface_of_tface fc))
                                                  rn kl fb)));
                                    } in
                                let ty = inst ty instargs in
                                let newtm = { tm; ty } in
                                Hashtbl.add new_tm_tbl (SFace_of fab) newtm;
                                newtm);
                          }
                          [ etms; etys ] in
                      Value.App (Arg newarg, newins))
                args in
            let (Plus ni) = D.plus intrinsic in
            (* We add the current field projection to the args, with an insertion obtained by incorporating the remaining dimensions into the evaluation. *)
            let (Plus rm) = D.plus m in
            let newins = ins_plus_of_pbij fldins fldshuf rm in
            let args = Snoc (args, Value.App (Field (fld, ni), newins)) in
            (* To hypothesize a value for the current term, we insert the supposed value as the value of this field.  Note the context rb of the supposed value is the degenerated rb instead of the original b, but this is exactly right for the value that's supposed to go in at this pbij.  *)
            let hyp (tm : (rb, potential) term) : (aa, potential) term =
              let hsf =
                Term.Structfield.Higher (PlusPbijmap.set pbij (PlusFam (Some (plusmap, tm))) cvals)
              in
              let ctms = Snoc (ctms, Entry (fld, hsf)) in
              hyp (Term.Struct (Noeta, m, ctms, energy status)) in
            Potential (head, args, hyp) in
      (* Get the user's supplied term for this partial bijection *)
      let key = Some (Field.to_string fld, strings_of_pbij pbij) in
      let tm, tms =
        match Abwd.find_opt_and_update key key (fun x -> locate_opt x.loc None) tms with
        | Some ({ value = Some tm; loc }, tms) -> ({ value = tm; loc }, tms)
        | Some ({ value = None; _ }, _) -> fatal (Anomaly "accessing same method twice")
        (* Higher fields cannot be positional *)
        | None -> fatal (Missing_method_in_comatch (fld, Some pbij)) in
      let evals, cvals, errs =
        (* Go into the location of the field right away, so that errors in dimension calculations will be labeled by the right field. *)
        with_loc tm.loc @@ fun () ->
        (* We trap any errors produced by 'tyof_field' or 'check', adding them instead to the list of accumulated errors and going on.  Note that if any previous fields that have already failed, then prev_etm will be bound to an error value, and so if the type of this field depends on the value of any previous one, tyof_field will raise that error, which we catch and add to the list; but it will be (Accumulated Emp) so it won't be displayed to the user. *)
        Reporter.try_with ~fatal:(fun e -> (evals, cvals, Snoc (errs, e))) @@ fun () ->
        let shuf : (r, h, i, c) Norm.shuffleable =
          Nontrivial
            {
              dbwd = length_env env;
              shuffle = fldshuf;
              deg_env = (fun _sh r_sh e -> eval_env degenv r_sh (readback_env ctx e termctx));
              deg_nf =
                (fun nf ->
                  let ctm = readback_nf ctx nf in
                  let tm = eval_term degenv ctm in
                  let cty = readback_val ctx nf.ty in
                  let ity = eval_term degenv cty in
                  let argstbl = Hashtbl.create 10 in
                  let tyargs =
                    TubeOf.build D.zero (D.zero_plus r)
                      {
                        build =
                          (fun fa ->
                            let faenv = act_env degenv (op_of_sface (sface_of_tface fa)) in
                            let fatm = eval_term faenv ctm in
                            let faty =
                              inst (eval_term faenv cty)
                                (TubeOf.build D.zero
                                   (D.zero_plus (dom_tface fa))
                                   {
                                     build =
                                       (fun fb ->
                                         Hashtbl.find argstbl
                                           (SFace_of
                                              (comp_sface (sface_of_tface fa) (sface_of_tface fb))));
                                   }) in
                            let nf = { tm = fatm; ty = faty } in
                            Hashtbl.add argstbl (SFace_of (sface_of_tface fa)) nf;
                            nf);
                      } in
                  { tm; ty = inst ity tyargs });
            } in
        (* Evaluate the type for this instance of the field, and check the user's type against it. *)
        let ety = tyof_higher_codatafield prev_etm fld env tyargs fldins ic0 fldty ~shuf in
        let ctm = check newstatus degctx tm ety in
        (* Add the typechecked term to the list *)
        let cvals = PlusPbijmap.set pbij (PlusFam (Some (plusmap, ctm))) cvals in
        (* If there are no remaining dimensions, we can evaluate the term and add it to the list of evaluated fields. *)
        let evals =
          match D.compare_zero r with
          | Pos _ -> evals
          | Zero ->
              let Eq = eq_of_zero_shuffle fldshuf in
              InsmapOf.set fldins (Some (lazy_eval (Ctx.env degctx) ctm)) evals in
        (evals, cvals, errs) in
      check_higher_field status ctx ty m intrinsic codata_args fields termctx tyargs tms ctms etms
        errs fld cvals evals pbijs prev_etm ic0 fldty
  | None ->
      let plusdim = D.zero_plus m in
      let env = Ctx.env ctx in
      let deg = id_deg (D.plus_out (dim_env env) plusdim) in
      let etms =
        Snoc
          (etms, Entry (fld, Higher { vals = evals; intrinsic; plusdim; env; deg; terms = cvals }))
      in
      let ctms = Snoc (ctms, Entry (fld, Higher cvals)) in
      check_fields status Noeta ctx ty m (D.plus_zero m) codata_args fields tyargs tms ctms etms
        errs

and synth : type a b s.
    (b, s) status -> (a, b) Ctx.t -> a synth located -> (b, s) term * kinetic value =
 fun status ctx tm ->
  let go () =
    match (tm.value, status) with
    | Var i, _ -> (
        match Ctx.lookup ctx i with
        | `Var (_, x, v) -> (realize status (Term.Var v), x.ty)
        | `Field (lvl, x, fld) -> (
            match Ctx.find_level ctx lvl with
            | Some v ->
                (* TODO: Double-check that this zero is correct *)
                let ins = ins_zero D.zero in
                ( realize status (Term.Field (Var v, fld, ins)),
                  tyof_field (Ok x.tm) x.ty fld ~shuf:Trivial ins )
            | None -> fatal (Anomaly "level not found in field view")))
    | Const name, _ -> (
        let ty, tm = Global.find name in
        match (tm, Ctx.locked ctx) with
        | Axiom `Nonparametric, true -> fatal (Locked_axiom (PConstant name))
        | _ -> (realize status (Const name), eval_term (Emp D.zero) ty))
    | Field (tm, fld), _ ->
        let stm, sty = synth (Kinetic `Nolet) ctx tm in
        (* To take a field of something, the type of the something must be a record-type that contains such a field, possibly substituted to a higher dimension and instantiated. *)
        let etm = eval_term (Ctx.env ctx) stm in
        let WithIns (fld, ins), newty = tyof_field_withname ctx (Ok etm) sty fld in
        (realize status (Field (stm, fld, ins)), newty)
    | UU, _ -> (realize status (Term.UU D.zero), universe D.zero)
    | Pi (x, dom, cod), _ ->
        (* User-level pi-types are always dimension zero, so the domain must be a zero-dimensional type. *)
        let cdom = check (Kinetic `Nolet) ctx dom (universe D.zero) in
        let edom = eval_term (Ctx.env ctx) cdom in
        let ccod = check (Kinetic `Nolet) (Ctx.ext ctx x edom) cod (universe D.zero) in
        (realize status (pi x cdom ccod), universe D.zero)
    | App _, _ ->
        (* If there's at least one application, we slurp up all the applications, synthesize a type for the function, and then pass off to synth_apps to iterate through all the arguments. *)
        let fn, args = spine tm in
        let sfn, sty = synth (Kinetic `Nolet) ctx fn in
        let stm, sty = synth_apps (Kinetic `Nolet) ctx { value = sfn; loc = fn.loc } sty fn args in
        (realize status stm, sty)
    | Act (str, fa, { value = Synth x; loc }), _ ->
        let x = { value = x; loc } in
        let ctx = if locking fa then Ctx.lock ctx else ctx in
        let sx, ety = synth (Kinetic `Nolet) ctx x in
        let ex = eval_term (Ctx.env ctx) sx in
        ( realize status (Term.Act (sx, fa)),
          with_loc x.loc @@ fun () ->
          act_ty ex ety fa ~err:(Low_dimensional_argument_of_degeneracy (str, cod_deg fa)) )
    | Act _, _ -> fatal (Nonsynthesizing "argument of degeneracy")
    | Asc (tm, ty), _ ->
        let cty =
          Reporter.try_with ~fatal:(fun d1 ->
              (* If the ascribed type doesn't typecheck, *and* if the term itself happens to already be synthesizing, we can proceed to try to synthesize it, accumulating errors from multiple sources.  This will rarely happen in normal use, since there is no need to ascribe a term that's already synthesizing, but with some alternative frontends it may. *)
              match tm.value with
              | Synth stm ->
                  Reporter.try_with ~fatal:(fun d2 ->
                      fatal (Accumulated ("ascribing synth", Snoc (Snoc (Emp, d1), d2))))
                  @@ fun () ->
                  let _ = synth status ctx (locate_opt tm.loc stm) in
                  fatal_diagnostic d1
              | _ -> fatal_diagnostic d1)
          @@ fun () -> check (Kinetic `Nolet) ctx ty (universe D.zero) in
        let ety = eval_term (Ctx.env ctx) cty in
        let ctm = check status ctx tm ety in
        (ctm, ety)
    | Let (x, v, body), _ ->
        let ctm, Not_none ety = synth_or_check_let status ctx x v body None in
        (* The synthesized type of the body is also correct for the whole let-expression, because it was synthesized in a context where the variable is bound not just to its type but to its value, so it doesn't include any extra level variables (i.e. it can be silently "strengthened"). *)
        (ctm, ety)
    | Letrec (vtys, vs, body), _ ->
        let ctm, Not_none ety = synth_or_check_letrec status ctx vtys vs body None in
        (* The synthesized type of the body is also correct for the whole let-expression, because it was synthesized in a context where the variable is bound not just to its type but to its value, so it doesn't include any extra level variables (i.e. it can be silently "strengthened"). *)
        (ctm, ety)
    | Match _, Kinetic l -> (
        match l with
        | `Let -> raise Case_tree_construct_in_let
        | `Nolet ->
            emit (Bare_case_tree_construct "match");
            (* A match in a kinetic synthesizing position, we can treat like a let-binding that returns the bound (metavariable) value.  Of course we can shortcut the binding by just inserting the metavariable as the result.  This code is copied and modified from synth_or_check_let.  Note that in this case there is no evident way to give the metavariable a type before defining it, which means that with_meta_definition won't be able to set it to anything; but this shouldn't be a problem since there is also no name for this metavariable and hence no way for the user to refer to it in the body, so it doesn't need to have a type or a value. *)
            let meta = Meta.make_def "match" None (Ctx.raw_length ctx) (Ctx.dbwd ctx) Potential in
            let tmstatus = Potential (Meta (meta, Ctx.env ctx), Emp, fun x -> x) in
            let sv, svty = synth tmstatus ctx tm in
            let vty = readback_val ctx svty in
            let termctx = readback_ctx ctx in
            Global.add_meta meta ~termctx ~tm:(`Defined sv) ~ty:vty ~energy:Potential;
            (Term.Meta (meta, Kinetic), svty))
    | Match { tm; sort = `Explicit motive; branches; refutables = _ }, Potential _ ->
        synth_dep_match status ctx tm branches motive
    | Match { tm; sort = `Implicit; branches; refutables = _ }, Potential _ ->
        emit (Matching_wont_refine ("match in synthesizing position", None));
        synth_nondep_match status ctx tm branches None
    | Match { tm; sort = `Nondep i; branches; refutables = _ }, Potential _ ->
        synth_nondep_match status ctx tm branches (Some i)
    | Fail e, _ -> fatal e
    (* If we're using the synthesized type of an argument as an implicit first argument: *)
    | ImplicitSApp (fn, apploc, arg), _ -> (
        (* We synthesize both function and argument *)
        let sfn, sfnty = synth (Kinetic `Nolet) ctx fn in
        let _, sargty = synth (Kinetic `Nolet) ctx arg in
        (* We read back the synthesized type, so we can put it as the first argument in the generated term. *)
        let cargty = readback_val ctx sargty in
        match view_type sfnty "ImplicitSApp" with
        | Pi (_, doms, cods, tyargs) -> (
            (* Only 0-dimensional applications are allowed, and the first argument must be a type. *)
            match
              ( D.compare (CubeOf.dim doms) D.zero,
                view_type (CubeOf.find_top doms) "ImplicitSApp argument" )
            with
            | Eq, UU _ ->
                (* We build the implicit application term and its type. *)
                let new_sfn = locate_opt fn.loc (Term.App (sfn, CubeOf.singleton cargty)) in
                let new_sty = tyof_app cods tyargs (CubeOf.singleton sargty) in
                (* And then apply to the argument. *)
                let stm, sty =
                  synth_apps (Kinetic `Nolet) ctx new_sfn new_sty fn
                    [ (apploc, locate_opt arg.loc (Synth arg.value), locate_opt None `Explicit) ]
                in
                (realize status stm, sty)
            | Eq, _ ->
                fatal ?loc:fn.loc (Anomaly "first argument of an ImplicitSMap is not of type Type")
            | Neq, _ ->
                fatal ?loc:fn.loc (Dimension_mismatch ("ImplicitSApp", CubeOf.dim doms, D.zero)))
        | _ ->
            fatal ?loc:fn.loc (Applying_nonfunction_nontype (PTerm (ctx, sfn), PVal (ctx, sfnty))))
    | SFirst (alts, arg), _ ->
        let _, sty = synth status ctx (locate_opt tm.loc arg) in
        let vsty = view_type sty "synth_first" in
        let rec go errs = function
          | [] ->
              if Bwd.is_empty errs then fatal (Choice_mismatch (PVal (ctx, sty)))
              else fatal (Accumulated ("SFirst", errs))
          | (test, alt, passthru) :: alts -> (
              match (vsty, test) with
              | Canonical (_, Data { constrs = data_constrs; _ }, _), `Data constrs ->
                  if
                    List.for_all
                      (fun constr ->
                        Bwd.exists (fun (data_constr, _) -> constr = data_constr) data_constrs)
                      constrs
                  then
                    Reporter.try_with ~fatal:(fun d ->
                        if passthru then go (Snoc (errs, d)) alts else fatal_diagnostic d)
                    @@ fun () -> synth status ctx (locate_opt tm.loc alt)
                  else go errs alts
              | Canonical (_, Codata { fields = codata_fields; _ }, _), `Codata fields ->
                  if
                    List.for_all
                      (fun field ->
                        Bwd.exists
                          (fun (CodatafieldAbwd.Entry (codata_field, _)) ->
                            field = Field.to_string codata_field)
                          codata_fields)
                      fields
                  then
                    Reporter.try_with ~fatal:(fun d ->
                        if passthru then go (Snoc (errs, d)) alts else fatal_diagnostic d)
                    @@ fun () -> synth status ctx (locate_opt tm.loc alt)
                  else go errs alts
              | _, `Any ->
                  Reporter.try_with ~fatal:(fun d ->
                      if passthru then go (Snoc (errs, d)) alts else fatal_diagnostic d)
                  @@ fun () -> synth status ctx (locate_opt tm.loc alt)
              | _ -> go errs alts) in
        go Emp alts in
  with_loc tm.loc @@ fun () ->
  Annotate.ctx status ctx (locate_opt tm.loc (Synth tm.value));
  let restm, resty = go () in
  Annotate.ty ctx resty;
  Annotate.tm ctx restm;
  (restm, resty)

(* Given something that can be applied, its type, and a list of arguments, check the arguments in appropriately-sized groups. *)
and synth_apps : type a b.
    (b, kinetic) status ->
    (a, b) Ctx.t ->
    (b, kinetic) term located ->
    kinetic value ->
    a synth located ->
    (Asai.Range.t option * a check located * [ `Implicit | `Explicit ] located) list ->
    (b, kinetic) term * kinetic value =
 fun status ctx sfn sty fn args ->
  (* To determine what to do, we inspect the (fully instantiated) *type* of the function being applied.  Failure of view_type here is really a bug, not a user error: the user can try to check something against an abstraction as if it were a type, but our synthesis functions should never synthesize (say) a lambda-abstraction as if it were a type. *)
  let asfn, aty, afn, aargs =
    match view_type sty "synthesizing application spine" with
    (* The obvious thing we can "apply" is an element of a pi-type. *)
    | Pi (_, doms, cods, tyargs) -> synth_app ctx sfn doms cods tyargs fn args
    (* We can also "apply" a higher-dimensional *type*, leading to a (further) instantiation of it.  Here the number of arguments must exactly match *some* integral instantiation. *)
    | UU tyargs -> synth_inst ctx sfn tyargs fn args
    (* Something that synthesizes a type that isn't a pi-type or a universe cannot be applied to anything, but this is a user error, not a bug. *)
    | _ ->
        fatal ?loc:sfn.loc (Applying_nonfunction_nontype (PTerm (ctx, sfn.value), PVal (ctx, sty)))
  in
  (* synth_app and synth_inst fail if there aren't enough arguments.  If they used up all the arguments, we're done; otherwise we continue with the rest of the arguments. *)
  match aargs with
  | [] -> (asfn.value, aty)
  | _ :: _ ->
      with_loc asfn.loc (fun () ->
          Annotate.ctx status ctx (locate_opt afn.loc (Synth afn.value));
          Annotate.ty ctx aty;
          Annotate.tm ctx asfn.value);
      synth_apps status ctx asfn aty afn aargs

(* This is a common subroutine for synth_app and synth_inst that picks up a whole cube of arguments and checks their types.  Since in one case we need a cube of values and the other case a cube of normals, we let the caller choose. *)
and synth_arg_cube : type a b n c.
    not_enough:Reporter.Code.t ->
    implicit:[ `Implicit | `Explicit ] ->
    which:string ->
    (a, b) Ctx.t ->
    (kinetic value -> normal -> c) ->
    (n, kinetic value) CubeOf.t ->
    Asai.Range.t option
    * a synth located
    * (Asai.Range.t option * a check located * [ `Implicit | `Explicit ] located) list ->
    ((n, (b, kinetic) term) CubeOf.t * (n, c) CubeOf.t)
    * (Asai.Range.t option
      * a synth located
      * (Asai.Range.t option * a check located * [ `Implicit | `Explicit ] located) list) =
 fun ~not_enough ~implicit ~which ctx choose doms (sfnloc, fn, args) ->
  (* Based on the global implicit-function-boundaries setting, the dimension of the application, and whether the first argument is implicit, decide whether we are taking a whole cube of arguments or only one argument with the boundary synthesized from it. *)
  let module TakenArgs = struct
    type t =
      | Take
      | Given : Asai.Range.t option * (n, 'k, 'nk) D.plus * (D.zero, 'nk, 'nk, normal) TubeOf.t -> t
  end in
  let taken_args : TakenArgs.t =
    match (args, implicit, D.compare_zero (CubeOf.dim doms)) with
    | [], _, _ -> fatal not_enough
    (* If the application if zero-dimensional, or if the global setting is explicit, or if the global setting is implicit and the first argument is implicit, take a whole cube. *)
    | _, _, Zero | _, `Explicit, Pos _ | (_, _, { value = `Implicit; _ }) :: _, `Implicit, Pos _ ->
        Take
    (* Otherwise, the first argument must be explicit and synthesizing. *)
    | (_, { value = Synth toptm; loc }, { value = `Explicit; _ }) :: _, `Implicit, Pos _ -> (
        (* We synthesize its type, extract the instantiation arguments, and store them to fill in the boundary arguments. *)
        let _, argty = synth (Kinetic `Nolet) ctx (locate_opt loc toptm) in
        let (Full_tube argtyargs) = get_tyargs argty "primary argument" in
        (* A function of one dimension can be applied to a primary argument of a *higher* dimension, since a cube is also a square.  So we require only that the dimension of argtyargs factors through the application dimension. *)
        match factor (TubeOf.inst argtyargs) (CubeOf.dim doms) with
        | Some (Factor nk) -> Given (loc, nk, argtyargs)
        | None ->
            fatal ~severity:Asai.Diagnostic.Error ?loc
              (Insufficient_dimension
                 { needed = CubeOf.dim doms; got = TubeOf.inst argtyargs; which }))
    | (_, _, { value = `Explicit; _ }) :: _, `Implicit, Pos _ ->
        fatal (Nonsynthesizing ("primary argument with implicit " ^ which ^ " boundaries")) in
  let module M = Monad.State (struct
    type t =
      Asai.Range.t option
      * a synth located
      * (Asai.Range.t option * a check located * [ `Implicit | `Explicit ] located) list
  end) in
  (* Pick up the right number of arguments for the dimension, leaving the others for a later call to synth_app.  Then check each argument against the corresponding type in "doms", instantiated at the appropriate evaluated previous arguments, and evaluate it, producing Cubes of checked terms and values.  Since each argument has to be checked against a type instantiated at the *values* of the previous ones, we also store those in a hashtable as we go. *)
  let eargtbl = Hashtbl.create 10 in
  let [ cargs; eargs ], (newloc, newfn, rest) =
    let open CubeOf.Monadic (M) in
    let open CubeOf.Infix in
    let first = ref true in
    pmapM
      {
        map =
          (fun fa [ dom ] ->
            let open Monad.Ops (M) in
            let* loc, f, ts = M.get in
            (* The type of this argument is obtained by instantiating the domain higher-dimensional type at the previous arguments. *)
            let ty =
              inst dom
                (TubeOf.build D.zero
                   (D.zero_plus (dom_sface fa))
                   {
                     build =
                       (fun fc ->
                         Hashtbl.find eargtbl (SFace_of (comp_sface fa (sface_of_tface fc))));
                   }) in
            let* ctm, tm =
              match (pface_of_sface fa, taken_args) with
              (* If we are synthesizing the implicit boundary and this is a proper face, we look up the corresponding normal value, check that it has the correct type, and read it back to get the required checked term. *)
              | `Proper pfa, Given (toploc, nk, argtyargs) ->
                  let (Plus ml) = D.plus (D.plus_right nk) in
                  let { tm = etm; ty = ety } = TubeOf.find argtyargs (pface_plus pfa nk ml) in
                  with_loc toploc (fun () ->
                      equal_val (Ctx.length ctx) ety ty
                      <|> Unequal_synthesized_boundary
                            { face = fa; got = PVal (ctx, ety); expected = PVal (ctx, ty) });
                  let ctm = readback_at ctx etm ety in
                  return (ctm, etm)
              (* Otherwise, we pull an argument of the appropriate implicitness, check it against the correct type. *)
              | _ ->
                  let* tm =
                    match ts with
                    | [] -> with_loc loc @@ fun () -> fatal not_enough
                    | (l, t, ({ value = i; loc } as impl)) :: ts ->
                        (match (is_id_sface fa, i, implicit) with
                        | Some _, `Implicit, _ ->
                            fatal ?loc
                              (Unexpected_implicitness
                                 (`Implicit, "expecting primary " ^ which ^ " argument"))
                        | None, `Implicit, `Explicit ->
                            fatal ?loc
                              (Unexpected_implicitness
                                 (`Implicit, which ^ " boundaries are explicit"))
                        | None, `Explicit, `Implicit ->
                            fatal ?loc
                              (Unexpected_implicitness
                                 (`Explicit, which ^ " boundaries are implicit"))
                        | _ -> ());
                        let* () = M.put (l, locate_opt l (App (f, t, impl)), ts) in
                        return t in
                  (* If the application is explicit AND we are checking the first argument AND the argument synthesizes something of a high enough dimension to be the primary argument in an implicit application AND it fails to check against the needed type, we hint to the user that arguments are explicit, since they may be expecting them to be implicit. *)
                  let ctm =
                    if !first && implicit = `Explicit then
                      Reporter.try_with ~fatal:(fun d ->
                          match d.message with
                          | Unequal_synthesized_type
                              { got = PVal (_, gotty) as got; expected; which = _ } -> (
                              match
                                Reporter.try_with ~fatal:(fun _ -> None) @@ fun () ->
                                Some (get_tyargs gotty "primary argument")
                              with
                              | None -> fatal_diagnostic d
                              | Some (Full_tube argtyargs) -> (
                                  match factor (TubeOf.inst argtyargs) (CubeOf.dim doms) with
                                  | Some (Factor _) ->
                                      fatal ?loc:d.explanation.loc
                                        (Unequal_synthesized_type
                                           { got; expected; which = Some which })
                                  | None -> fatal_diagnostic d))
                          | _ -> fatal_diagnostic d)
                      @@ fun () -> check (Kinetic `Nolet) ctx tm ty
                    else check (Kinetic `Nolet) ctx tm ty in
                  let etm = eval_term (Ctx.env ctx) ctm in
                  return (ctm, etm) in
            (* In both cases, we store the resulting value term as a normal in the hashtable of previous values, to use in instantiating later types. *)
            let ntm = { tm; ty } in
            Hashtbl.add eargtbl (SFace_of fa) ntm;
            first := false;
            return (ctm @: [ choose tm ntm ]));
      }
      [ doms ] (Cons (Cons Nil)) (sfnloc, fn, args) in
  ((cargs, eargs), (newloc, newfn, rest))

and synth_app : type a b n.
    (a, b) Ctx.t ->
    (b, kinetic) term located ->
    (n, kinetic value) CubeOf.t ->
    (n, unit) BindCube.t ->
    (D.zero, n, n, normal) TubeOf.t ->
    a synth located ->
    (Asai.Range.t option * a check located * [ `Implicit | `Explicit ] located) list ->
    (b, kinetic) term located
    * kinetic value
    * a synth located
    * (Asai.Range.t option * a check located * [ `Implicit | `Explicit ] located) list =
 fun ctx sfn doms cods tyargs fn args ->
  let implicit = Implicitboundaries.functions () in
  let (cargs, eargs), (newloc, newfn, rest) =
    synth_arg_cube ~not_enough:Not_enough_arguments_to_function ~implicit ~which:"function" ctx
      (fun tm _ -> tm)
      doms (sfn.loc, fn, args) in
  (* Evaluate cod at these evaluated arguments and instantiate it at the appropriate values of tyargs. *)
  let output = tyof_app cods tyargs eargs in
  ({ value = Term.App (sfn.value, cargs); loc = newloc }, output, newfn, rest)

and synth_inst : type a b n.
    (a, b) Ctx.t ->
    (b, kinetic) term located ->
    (D.zero, n, n, normal) TubeOf.t ->
    a synth located ->
    (Asai.Range.t option * a check located * [ `Implicit | `Explicit ] located) list ->
    (b, kinetic) term located
    * kinetic value
    * a synth located
    * (Asai.Range.t option * a check located * [ `Implicit | `Explicit ] located) list =
 fun ctx sfn tyargs fn args ->
  let n = TubeOf.inst tyargs in
  match D.compare_zero n with
  | Zero -> fatal (Instantiating_zero_dimensional_type (PTerm (ctx, sfn.value)))
  | Pos pn ->
      let implicit = Implicitboundaries.types () in
      (* We take enough arguments to instatiate a type of dimension n by one. *)
      let (Is_suc (m, msuc, k)) = suc_pos pn in
      let tyargs1 =
        TubeOf.mmap
          { map = (fun _ [ { tm; ty = _ } ] -> tm) }
          [ TubeOf.pboundary (D.zero_plus m) msuc tyargs ] in
      let (Wrap l) = Endpoints.wrapped () in
      let doms = TubeOf.to_cube_bwv k msuc l tyargs1 in
      let module M = Monad.State (struct
        type t =
          Asai.Range.t option
          * a synth located
          * (Asai.Range.t option * a check located * [ `Implicit | `Explicit ] located) list
      end) in
      let open Bwv.Monadic (M) in
      let (cargs, nargs), (newloc, newfn, rest) =
        mapM1_2
          (synth_arg_cube ~not_enough:Not_enough_arguments_to_instantiation ~implicit ~which:"type"
             ctx (fun _ ntm -> ntm))
          doms (sfn.loc, fn, args) in
      (* The synthesized type *of* the instantiation is itself a full instantiation of a universe, at the instantiations of the type arguments at the evaluated term arguments.  This is computed by tyof_inst. *)
      let cargs = TubeOf.of_cube_bwv m k msuc l cargs in
      let nargs = TubeOf.of_cube_bwv m k msuc l nargs in
      ({ value = Term.Inst (sfn.value, cargs); loc = newloc }, tyof_inst tyargs nargs, newfn, rest)

(* Check a list of terms against the types specified in a telescope, evaluating the latter in a supplied environment and in the context of the previously checked terms, and instantiating them at values given in a tube.  See description in context of the call to it above during typechecking of a constructor. *)
and check_at_tel : type n a b c bc e.
    Constr.t ->
    (a, e) Ctx.t ->
    (n, b) env ->
    (* This list of terms to check must have the same length *)
    a check located list ->
    (* as this telescope (namely, the Fwn 'c') *)
    (b, c, bc) Telescope.t ->
    (* and as all the lists in this tube. *)
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
                        (eval_term (act_env env (op_of_sface fa)) ty)
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
      let ctm = check (Kinetic `Nolet) ctx tm ity in
      let ctms = TubeOf.mmap { map = (fun _ [ t ] -> readback_nf ctx t) } [ tyarg ] in
      let etm = eval_term (Ctx.env ctx) ctm in
      let newenv, newargs =
        check_at_tel c ctx
          (Ext
             ( env,
               D.plus_zero (TubeOf.inst tyarg),
               Ok (TubeOf.plus_cube (val_of_norm_tube tyarg) (CubeOf.singleton etm)) ))
          tms tys tyargs in
      (newenv, TubeOf.plus_cube ctms (CubeOf.singleton ctm) :: newargs)
  | _ ->
      fatal
        (Wrong_number_of_arguments_to_constructor
           (c, List.length tms - Fwn.to_int (Telescope.length tys)))

(* Given a context and a raw telescope, we can check it to produce a checked telescope, a new context extended by that telescope, and a function for extending other contexts by that telescope.  The returned boolean indicates whether this could be the telescope of arguments of a constructor of a *discrete* datatype.  This requires knowing the collection of currently-being-defined mutual constants, since discrete types can appear recursively in the arguments of their constructors. *)
and check_tel : type a b c ac.
    ?discrete:unit Constant.Map.t ->
    (a, b) Ctx.t ->
    (a, c, ac) Raw.tel ->
    (a, b, c, ac) checked_tel * bool =
 fun ?discrete ctx tel ->
  match tel with
  | Emp -> (Checked_tel (Emp, ctx), Option.is_some discrete)
  | Ext (x, ty, tys) ->
      let cty = check (Kinetic `Nolet) ctx ty (universe D.zero) in
      let ety = eval_term (Ctx.env ctx) cty in
      let _, newnfs = dom_vars (Ctx.length ctx) (CubeOf.singleton ety) in
      let ctx = Ctx.cube_vis ctx x newnfs in
      let Checked_tel (ctys, ctx), disc = check_tel ?discrete ctx tys in
      let tydisc = is_discrete ?discrete ety in
      (Checked_tel (Ext (x, cty, ctys), ctx), disc && tydisc)
