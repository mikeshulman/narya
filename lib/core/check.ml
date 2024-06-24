open Bwd
open Util
open Perhaps
open Tbwd
open Reporter
open Syntax
open Term
open Value
open Domvars
open Raw
open Dim
open Act
open Norm
open Equal
open Readback
open Printable
open Asai.Range
include Status

let discard : type a. a -> unit = fun _ -> ()

(* Check that a given value is a zero-dimensional type family (something where an indexed datatype could live) and return the length of its domain telescope (the number of indices).  Unfortunately I don't see an easy way to do this without essentially going through all the same steps of extending the context that we would do to check something at that type family. *)
let rec typefam : type a b. (a, b) Ctx.t -> kinetic value -> int =
 fun ctx ty ->
  match view_type ~severity:Asai.Diagnostic.Error ty "typefam" with
  | UU tyargs -> (
      match D.compare (TubeOf.inst tyargs) D.zero with
      | Eq -> 0
      | Neq -> fatal (Unimplemented "higher-dimensional datatypes"))
  | Pi (x, doms, cods, tyargs) -> (
      (* In practice, these dimensions will always be zero also if the function succeeds, otherwise the eventual output would have to be higher-dimensional too.  But it doesn't hurt to be more general, and will require less change if we eventually implement higher-dimensional datatypes. *)
      match D.compare (TubeOf.inst tyargs) (CubeOf.dim doms) with
      | Eq ->
          let newargs, newnfs = dom_vars (Ctx.length ctx) doms in
          let output = tyof_app cods tyargs newargs in
          1 + typefam (Ctx.cube_vis ctx x newnfs) output
      | Neq -> fatal (Dimension_mismatch ("typefam", TubeOf.inst tyargs, CubeOf.dim doms)))
  | _ -> fatal (Checking_canonical_at_nonuniverse ("datatype", PVal (ctx, ty)))

let rec motive_of_family :
    type a b. (a, b) Ctx.t -> kinetic value -> kinetic value -> (b, kinetic) term =
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
  let folder :
      type left m any right.
      (left, m, any, right) F.t -> right T.t -> left T.t * (left, m, any, right) F.t =
   fun (Rbtm dom) cod -> (Pi (None, CubeOf.singleton dom, CodCube.singleton cod), Rbtm dom) in
  let builder :
      type left n m.
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

type (_, _, _) vars_of_vec =
  | Vars :
      ('a, 'b, 'abc) N.plus * (N.zero, 'n, string option, 'b) NICubeOf.t
      -> ('a, 'abc, 'n) vars_of_vec

let vars_of_vec :
    type a c abc n.
    Asai.Range.t option ->
    n D.t ->
    (a, c, abc) Fwn.bplus ->
    (string option, c) Vec.t ->
    (a, abc, n) vars_of_vec =
 fun loc dim abc xs ->
  let module S = struct
    type 'b t =
      | Ok : (a, 'b, 'ab) N.plus * ('ab, 'c, abc) Fwn.bplus * (string option, 'c) Vec.t -> 'b t
      | Missing of int
  end in
  let module Build = NICubeOf.Traverse (S) in
  match
    Build.build_left dim
      {
        build =
          (fun _ -> function
            | Ok (ab, Suc abc, x :: xs) -> Fwrap (NFamOf x, Ok (Suc ab, abc, xs))
            | Ok _ -> Fwrap (NFamOf None, Missing (-1))
            | Missing j -> Fwrap (NFamOf None, Missing (j - 1)));
      }
      (Ok (Zero, abc, xs))
  with
  | Wrap (names, Ok (ab, Zero, [])) -> Vars (ab, names)
  | Wrap (_, Ok (_, abc, _)) ->
      fatal ?loc (Wrong_boundary_of_record (Fwn.to_int (Fwn.bplus_right abc)))
  | Wrap (_, Missing j) -> fatal ?loc (Wrong_boundary_of_record j)

(* Slurp up an entire application spine.  Returns the function, the locations of all the applications (e.g. in "f x y" returns the locations of "f x" and "f x y") and all the arguments. *)
let spine :
    type a. a synth located -> a synth located * Asai.Range.t option list * a check located list =
 fun tm ->
  let rec spine tm locs args =
    match tm.value with
    | Raw.App (fn, arg) -> spine fn (tm.loc :: locs) (arg :: args)
    | _ -> (tm, locs, args) in
  spine tm [] []

let run_with_definition : type a s c. a potential_head -> (a, potential) term -> (unit -> c) -> c =
 fun head tm f ->
  match head with
  | Constant c -> Global.run_with_definition c (Global.Defined tm) f
  | Meta (m, _) -> Global.run_with_meta_definition m tm f

(* A "checkable branch" stores all the information about a branch in a match, both that coming from what the user wrote in the match and what is stored as properties of the datatype.  *)
type (_, _, _) checkable_branch =
  | Checkable_branch : {
      xs : (string option, 'c) Vec.t;
      plus_args : ('a, 'c, 'ac) Fwn.bplus;
      (* If the body is None, that means the user omitted this branch.  (That might be ok, if it can be refuted by a pattern variable belonging to an empty type.) *)
      body : 'ac check located option;
      env : ('m, 'b) env;
      argtys : ('b, 'c, 'bc) Telescope.t;
      index_terms : (('bc, kinetic) term, 'ij) Vec.t;
    }
      -> ('a, 'm, 'ij) checkable_branch

(* This preprocesssing step pairs each user-provided branch with the corresponding constructor information from the datatype. *)
let merge_branches head user_branches data_constrs =
  let user_branches, leftovers =
    Bwd.fold_left
      (fun (userbrs, databrs) (constr, Branch (xs, { value = plus_args; loc }, body)) ->
        (* We check at the preprocessing stage that there are no duplicate constructors in the match. *)
        if Abwd.mem constr userbrs then fatal ?loc (Duplicate_constructor_in_match constr);
        let databrs, databr = Abwd.extract constr databrs in
        let (Value.Dataconstr { env; args = argtys; indices = index_terms }) =
          Reporter.with_loc loc @@ fun () ->
          databr <|> No_such_constructor_in_match (phead head, constr) in
        (* We also check during preprocessing that the user has supplied the right number of pattern variable arguments to the constructor.  The positive result of this check is then recorded in the common existential types bound by Checkable_branch. *)
        match Fwn.compare (Fwn.bplus_right plus_args) (Telescope.length argtys) with
        | Neq ->
            fatal ?loc
              (Wrong_number_of_arguments_to_pattern
                 ( constr,
                   Fwn.to_int (Fwn.bplus_right plus_args) - Fwn.to_int (Telescope.length argtys) ))
        | Eq ->
            let br =
              Checkable_branch { xs; plus_args; body = Some body; env; argtys; index_terms } in
            (Snoc (userbrs, (constr, br)), databrs))
      (Bwd.Emp, data_constrs) user_branches in
  (* If there are any constructors in the datatype left over that the user didn't supply branches for, we add them to the list at the end.  They will be tested for refutability. *)
  Bwd_extra.append user_branches
    (Bwd.map
       (fun (c, Value.Dataconstr { env; args = argtys; indices = index_terms }) ->
         let b = Telescope.length argtys in
         let (Bplus plus_args) = Fwn.bplus b in
         let xs = Vec.init (fun () -> (None, ())) b () in
         (c, Checkable_branch { xs; body = None; plus_args; env; argtys; index_terms }))
       leftovers)

exception Case_tree_construct_in_let

(* The output of checking a telescope includes an extended context. *)
type (_, _) checked_tel =
  | Checked_tel : ('b, 'd, 'bd) Telescope.t * ('ac, 'bd) Ctx.t -> ('ac, 'b) checked_tel

(* Check a term or case tree (depending on the energy: terms are kinetic, case trees are potential). *)
let rec check :
    type a b s. (b, s) status -> (a, b) Ctx.t -> a check located -> kinetic value -> (b, s) term =
 fun status ctx tm ty ->
  with_loc tm.loc @@ fun () : (b, s) term ->
  (* If the "type" is not a type here, or not fully instantiated, that's a user error, not a bug. *)
  let severity = Asai.Diagnostic.Error in
  match (tm.value, status) with
  (* A Let is a "synthesizing" term so that it *can* synthesize, but in checking position it checks instead. *)
  | Synth (Let (x, v, body)), _ ->
      let clet, Not_some = synth_or_check_let status ctx x v body (Some ty) in
      clet
  (* An action can always synthesize, but can also check if its degeneracy is a pure permutation, since then the type of the argument can be inferred by applying the inverse permutation to the ambient type. *)
  | Synth (Act (str, fa, x) as stm), _ -> (
      (* TODO: Once we have multiple directions, this will need to be more sophisticated. *)
      match D.compare (dom_deg fa) (cod_deg fa) with
      | Neq -> check_of_synth status ctx stm tm.loc ty
      | Eq ->
          let fainv = perm_inv fa in
          let ty_fainv =
            gact_ty None ty fainv ~err:(Low_dimensional_argument_of_degeneracy (str, cod_deg fa))
          in
          let cx =
            (* A pure permutation shouldn't ever be locking, but we may as well keep this here for consistency.  *)
            if locking fa then
              Global.run_locked (fun () -> check (Kinetic `Nolet) (Ctx.lock ctx) x ty_fainv)
            else check (Kinetic `Nolet) ctx x ty_fainv in
          realize status (Term.Act (cx, fa)))
  | Lam ({ value = x; _ }, cube, body), _ -> (
      match view_type ~severity ty "typechecking lambda" with
      | Pi (_, doms, cods, tyargs) -> (
          (* TODO: Move this into a helper function, it's too long to go in here. *)
          let m = CubeOf.dim doms in
          let Eq = D.plus_uniq (TubeOf.plus tyargs) (D.zero_plus m) in
          (* Extend the context by one variable for each type in doms, instantiated at the appropriate previous ones. *)
          let newargs, newnfs = dom_vars (Ctx.length ctx) doms in
          (* A helper function to update the status *)
          let mkstatus (type n) (xs : n variables) : (b, s) status -> ((b, n) snoc, s) status =
            function
            | Kinetic l -> Kinetic l
            | Potential (c, args, hyp) ->
                let arg =
                  Arg (CubeOf.mmap { map = (fun _ [ x ] -> Ctx.Binding.value x) } [ newnfs ]) in
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
                  Lam (xs, check (mkstatus xs status) ctx body output)
              | Wrap (_, Missing (loc, j)) -> fatal ?loc (Not_enough_lambdas j))
          | `Cube ->
              (* Here we don't need to slurp up lots of lambdas, but can make do with one. *)
              let xs = singleton_variables m x in
              let ctx = Ctx.cube_vis ctx x newnfs in
              Lam (xs, check (mkstatus xs status) ctx body output))
      | _ -> fatal (Checking_lambda_at_nonfunction (PVal (ctx, ty))))
  | Struct (Noeta, tms), Potential _ -> (
      match view_type ~severity ty "typechecking comatch" with
      (* We don't need to name the arguments here because tyof_field, called below from check_field, uses them. *)
      | Canonical (name, Codata { eta = Noeta; ins; fields; _ }, _) ->
          let () = is_id_ins ins <|> Comatching_at_degenerated_codata (phead name) in
          check_struct status Noeta ctx tms ty (cod_left_ins ins) fields
      | _ -> fatal (Comatching_at_noncodata (PVal (ctx, ty))))
  | Struct (Eta, tms), _ -> (
      match view_type ~severity ty "typechecking tuple" with
      | Canonical (name, Codata { eta = Eta; ins; fields; _ }, _) ->
          is_id_ins ins <|> Checking_tuple_at_degenerated_record (phead name);
          check_struct status Eta ctx tms ty (cod_left_ins ins) fields
      | _ -> fatal (Checking_tuple_at_nonrecord (PVal (ctx, ty))))
  | Constr ({ value = constr; loc = constr_loc }, args), _ -> (
      (* TODO: Move this into a helper function, it's too long to go in here. *)
      match view_type ~severity ty "typechecking constr" with
      | Canonical
          (name, Data { dim; indices = Filled ty_indices; constrs; discrete = _; tyfam = _ }, tyargs)
        -> (
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
                              | None -> fatal (Anomaly "mismatching lower-dimensional constructors")
                              ));
                    }
                    [ t1s; t2s ])
                [ constr_indices; ty_indices ];
              realize status (Term.Constr (constr, dim, newargs)))
      | _ -> fatal (No_such_constructor (`Other (PVal (ctx, ty)), constr)))
  | Synth (Match { tm; sort = `Implicit; branches; refutables }), Potential _ ->
      check_implicit_match status ctx tm branches refutables ty
  | Synth (Match { tm; sort = `Nondep i; branches; refutables = _ }), Potential _ ->
      let stm, sty = synth (Kinetic `Nolet) ctx tm in
      check_nondep_match status ctx stm sty branches (Some i) ty
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
      | UU tyargs -> check_codata status ctx tyargs Emp (Bwd.to_list fields)
      | _ -> fatal (Checking_canonical_at_nonuniverse ("codatatype", PVal (ctx, ty))))
  | Record (abc, xs, fields, opacity), Potential _ -> (
      match view_type ~severity ty "typechecking record" with
      | UU tyargs ->
          let dim = TubeOf.inst tyargs in
          let (Vars (af, vars)) = vars_of_vec abc.loc dim abc.value xs in
          check_record status dim ctx opacity tyargs vars Emp Zero af Emp fields
      | _ -> fatal (Checking_canonical_at_nonuniverse ("record type", PVal (ctx, ty))))
  | Data constrs, Potential (_, args, _) ->
      (* For a datatype, the type to check against might not be a universe, it could include indices. *)
      let (Wrap num_indices) = Fwn.of_int (typefam ctx ty) in
      (* If discreteness is on, then a datatype with no parameters or indices can be discrete.  (This is just a starting point; the arguments of all the constructors are also required to be either discrete or simply recursive.) *)
      let discrete =
        Discreteness.read ()
        &&
        match (num_indices, args) with
        | Zero, Emp -> true
        | _ -> false in
      check_data status ctx ty num_indices Abwd.empty (Bwd.to_list constrs) ~discrete
  (* If we have a term that's not valid outside a case tree, we bind it to a global metavariable. *)
  | Struct (Noeta, _), Kinetic l -> kinetic_of_potential l ctx tm ty "comatch"
  | Synth (Match _), Kinetic l -> kinetic_of_potential l ctx tm ty "match"
  | Refute _, Kinetic l -> kinetic_of_potential l ctx tm ty "match"
  | Codata _, Kinetic l -> kinetic_of_potential l ctx tm ty "codata"
  | Record _, Kinetic l -> kinetic_of_potential l ctx tm ty "sig"
  | Data _, Kinetic l -> kinetic_of_potential l ctx tm ty "data"
  (* If the user left a hole, we create an eternal metavariable. *)
  | Hole vars, _ ->
      (* Holes aren't numbered by the file they appear in. *)
      let meta = Meta.make_hole (Ctx.dbwd ctx) (energy status) in
      let ty, termctx =
        Readback.Display.run ~env:true @@ fun () -> (readback_val ctx ty, readback_ctx ctx) in
      Global.add_eternal_meta meta ~vars ~termctx ~ty ~status;
      emit (Hole_generated (meta, Termctx.PHole (vars, termctx, ty)));
      Meta (meta, energy status)
  (* And lastly, if we have a synthesizing term, we synthesize it. *)
  | Synth stm, _ -> check_of_synth status ctx stm tm.loc ty

(* Deal with a synthesizing term in checking position. *)
and check_of_synth :
    type a b s.
    (b, s) status -> (a, b) Ctx.t -> a synth -> Asai.Range.t option -> kinetic value -> (b, s) term
    =
 fun status ctx stm loc ty ->
  let sval, sty = synth status ctx { value = stm; loc } in
  equal_val (Ctx.length ctx) sty ty <|> Unequal_synthesized_type (PVal (ctx, sty), PVal (ctx, ty));
  sval

(* Deal with a potential term in kinetic position *)
and kinetic_of_potential :
    type a b.
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
      let meta = Meta.make_def sort None (Ctx.dbwd ctx) Potential in
      let tmstatus = Potential (Meta (meta, Ctx.env ctx), Emp, fun x -> x) in
      let cv = check tmstatus ctx tm ty in
      let vty = readback_val ctx ty in
      let termctx = readback_ctx ctx in
      Global.add_meta meta ~termctx ~tm:cv ~ty:vty ~energy:Potential;
      Term.Meta (meta, Kinetic)

and synth_or_check_let :
    type a b s p.
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
      (* We try checking the bound term first as an ordinary kinetic term. *)
      let sv, svty = synth (Kinetic `Let) ctx v in
      let ev = eval_term (Ctx.env ctx) sv in
      (sv, { tm = ev; ty = svty })
    with
    (* If that fails, the bound term is also allowed to be a case tree, i.e. a potential term.  But in a checked "let" expression, the term being bound is a kinetic one, and must be so that its value can be put into the environment when the term is evaluated.  We deal with this by binding a *metavariable* to the bound term and then taking the value of that metavariable as the kinetic term to actually be bound.  *)
    | Case_tree_construct_in_let ->
      (* First we make the metavariable. *)
      let meta = Meta.make_def "let" name (Ctx.dbwd ctx) Potential in
      (* A new status in which to check the value of that metavariable; now it is the "current constant" being defined. *)
      let tmstatus = Potential (Meta (meta, Ctx.env ctx), Emp, fun x -> x) in
      let sv, svty = synth tmstatus ctx v in
      (* Now we define the global value of that metavariable to be the term and type just synthesized. *)
      let vty = readback_val ctx svty in
      let termctx = readback_ctx ctx in
      Global.add_meta meta ~termctx ~tm:sv ~ty:vty ~energy:Potential;
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
  match (ty, body) with
  | Some ty, _ ->
      let sbody = check status newctx body ty in
      (Term.Let (name, v, sbody), Not_some)
  | None, { value = Synth body; loc } ->
      let sbody, sbodyty = synth status newctx { value = body; loc } in
      (Term.Let (name, v, sbody), Not_none sbodyty)
  | None, _ -> fatal (Nonsynthesizing "let-expression without synthesizing body")

(* Check a match statement without an explicit motive supplied by the user.  This means if the discriminee is a well-behaved variable, it can be a variable match; otherwise it reverts back to a non-dependent match. *)
and check_implicit_match :
    type a b t.
    (b, potential) status ->
    (a, b) Ctx.t ->
    a synth located ->
    (Constr.t, a branch) Abwd.t ->
    a refutables ->
    kinetic value ->
    (b, potential) term =
 fun status ctx tm brs refutables motive ->
  match tm with
  (* For a variable match, the variable must not be let-bound to a value or be a field access variable.  Checking that it isn't also gives us its De Bruijn level, its type, and its checked-index.  If it's not a free variable, or if we're not in a case tree or if the motive was supplied explicitly, we obtain its value and type; then we pass on to the appropriate checking function. *)
  | { value = Var ix; loc } -> (
      match Ctx.lookup ctx ix with
      | `Field (_, _, fld) ->
          emit ?loc (Matching_wont_refine ("discriminee is record field", PField fld));
          let tm, varty = synth (Kinetic `Nolet) ctx tm in
          check_nondep_match status ctx tm varty brs None motive
      | `Var (None, _, ix) ->
          emit ?loc (Matching_wont_refine ("discriminee is let-bound", PTerm (ctx, Var ix)));
          let tm, varty = synth (Kinetic `Nolet) ctx tm in
          check_nondep_match status ctx tm varty brs None motive
      | `Var (Some level, { tm = _; ty = varty }, index) ->
          check_var_match status ctx level index varty brs refutables motive)
  | _ ->
      let tm, varty = synth (Kinetic `Nolet) ctx tm in
      check_nondep_match status ctx tm varty brs None motive

(* Either check a non-dependent match against a specified type, or synthesize a type for it from the first branch and then check the others against that type.  Which to do is determined by whether the motive passed is Some or None, and the return includes a type under the opposite conditions. *)
and synth_or_check_nondep_match :
    type a b p.
    (b, potential) status ->
    (a, b) Ctx.t ->
    (b, kinetic) term ->
    kinetic value ->
    (Constr.t, a branch) Abwd.t ->
    int located option ->
    (kinetic value, p) Perhaps.t ->
    (b, potential) term * (kinetic value, p) Perhaps.not =
 fun status ctx tm varty brs i motive ->
  (* We look up the type of the discriminee, which must be a datatype, without any degeneracy applied outside, and at the same dimension as its instantiation. *)
  match view_type varty "synth_or_check_nondep_match" with
  | Canonical (type m)
      (( name,
         Data (type j ij)
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
      (* We save the supplied type, if any. *)
      let ty : kinetic value option ref =
        ref
          (match motive with
          | Some ty -> Some ty
          | None -> None) in
      (* We start with a preprocesssing step that pairs each user-provided branch with the corresponding constructor information from the datatype. *)
      let user_branches = merge_branches name brs data_constrs in
      (* We now iterate through the constructors, typechecking the corresponding branches and inserting them in the match tree. *)
      let branches =
        Bwd.fold_left
          (fun branches
               ( constr,
                 (Checkable_branch { xs; body; plus_args; env; argtys; index_terms = _ } :
                   (a, m, ij) checkable_branch) ) ->
            let (Snocs efc) = Tbwd.snocs (Telescope.length argtys) in
            (* Create new level variables for the pattern variables to which the constructor is applied, and add corresponding index variables to the context.  The types of those variables are specified in the telescope argtys, and have to be evaluated at the closure environment 'env' and the previous new variables (this is what ext_tel does).  For a higher-dimensional match, the new variables come with their boundaries in n-dimensional cubes. *)
            let newctx, _, _, newnfs = ext_tel ctx env xs argtys plus_args efc in
            let perm = Tbwd.id_perm in
            let status = make_match_status status tm dim branches efc None perm constr in
            (* Finally, we recurse into the "body" of the branch. *)
            match !ty with
            | Some motive -> (
                (* If we have a type, check against it. *)
                match body with
                | Some body ->
                    branches
                    |> Constr.Map.add constr
                         (Term.Branch (efc, perm, check status newctx body motive))
                | None ->
                    if any_empty newnfs then branches |> Constr.Map.add constr Term.Refute
                    else fatal (Missing_constructor_in_match constr))
            | None -> (
                (* If we don't have a type yet, try to synthesize a type from this branch. *)
                match body with
                | Some { value = Synth value; loc } ->
                    let sbr, sty = synth status newctx { value; loc } in
                    (* The type synthesized is only valid for the whole match if it doesn't depend on the pattern variables.  We check that by reading it back into the original context. *)
                    Reporter.try_with ~fatal:(fun d ->
                        match d.message with
                        | No_such_level _ ->
                            fatal
                              (Invalid_synthesized_type ("first branch of match", PVal (newctx, sty)))
                        | _ -> fatal_diagnostic d)
                    @@ fun () ->
                    discard (readback_val ctx sty);
                    ty := Some sty;
                    branches |> Constr.Map.add constr (Term.Branch (efc, perm, sbr))
                | None -> fatal (Nonsynthesizing "match with zero branches")
                | _ ->
                    fatal
                      (Nonsynthesizing
                         "first branch in synthesizing match without return annotation")))
          Constr.Map.empty user_branches in
      match (motive, !ty) with
      | Some _, _ -> (Match { tm; dim; branches }, Not_some)
      | None, Some ty -> (Match { tm; dim; branches }, Not_none ty)
      | None, None -> fatal (Nonsynthesizing "empty match"))
  | _ -> fatal (Matching_on_nondatatype (PVal (ctx, varty)))

and check_nondep_match :
    type a b.
    (b, potential) status ->
    (a, b) Ctx.t ->
    (b, kinetic) term ->
    kinetic value ->
    (Constr.t, a branch) Abwd.t ->
    int located option ->
    kinetic value ->
    (b, potential) term =
 fun status ctx tm varty brs i motive ->
  let ctm, Not_some = synth_or_check_nondep_match status ctx tm varty brs i (Some motive) in
  ctm

and synth_nondep_match :
    type a b.
    (b, potential) status ->
    (a, b) Ctx.t ->
    a synth located ->
    (Constr.t, a branch) Abwd.t ->
    int located option ->
    (b, potential) term * kinetic value =
 fun status ctx tm brs i ->
  let sv, varty = synth (Kinetic `Nolet) ctx tm in
  let stm, Not_none sty = synth_or_check_nondep_match status ctx sv varty brs i None in
  (stm, sty)

(* Check a dependently typed match, with motive supplied by the user.  (Thus we have to typecheck the motive as well.) *)
and synth_dep_match :
    type a b.
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
  | Canonical (type m)
      (( name,
         Data (type j ij)
           ({ dim; indices = Filled var_indices; constrs = data_constrs; discrete = _; tyfam } :
             (_, j, ij) data_args),
         inst_args ) :
        _ * m canonical * _) ->
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
      let branches =
        Bwd.fold_left
          (fun branches
               ( constr,
                 (Checkable_branch { xs; body; plus_args; env; argtys; index_terms } :
                   (a, m, ij) checkable_branch) ) ->
            let (Snocs efc) = Tbwd.snocs (Telescope.length argtys) in
            (* Create new level variables for the pattern variables to which the constructor is applied, and add corresponding index variables to the context.  The types of those variables are specified in the telescope argtys, and have to be evaluated at the closure environment 'env' and the previous new variables (this is what ext_tel does).  For a higher-dimensional match, the new variables come with their boundaries in n-dimensional cubes. *)
            let newctx, newenv, newvars, newnfs = ext_tel ctx env xs argtys plus_args efc in
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
                branches
                |> Constr.Map.add constr (Term.Branch (efc, perm, check status newctx body bmotive))
            | None ->
                if any_empty newnfs then branches |> Constr.Map.add constr Term.Refute
                else fatal (Missing_constructor_in_match constr))
          Constr.Map.empty user_branches in
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
      (Match { tm = ctm; dim; branches }, result)
  | _ -> fatal (Matching_on_nondatatype (PVal (ctx, varty)))

(* Check a match against a well-behaved variable, which can only appear in a case tree and refines not only the goal but the context (possibly with permutation). *)
and check_var_match :
    type a b.
    (b, potential) status ->
    (a, b) Ctx.t ->
    level ->
    b Term.index ->
    kinetic value ->
    (Constr.t, a branch) Abwd.t ->
    a refutables ->
    kinetic value ->
    (b, potential) term =
 fun status ctx level index varty brs refutables motive ->
  (* We look up the type of the discriminee, which must be a datatype, without any degeneracy applied outside, and at the same dimension as its instantiation. *)
  match view_type varty "check_var_match" with
  | Canonical (type m)
      (( name,
         Data (type j ij)
           ({ dim; indices = Filled var_indices; constrs = data_constrs; discrete = _; tyfam } :
             (_, j, ij) data_args),
         inst_args ) :
        _ * m canonical * _) ->
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
                  fatal (Matching_wont_refine ("index variable has degeneracy", PNormal (ctx, x)));
                if Hashtbl.mem seen level then
                  fatal (Matching_wont_refine ("duplicate variable in indices", PNormal (ctx, x)));
                Hashtbl.add seen level ();
                level
            | _ -> fatal (Anomaly "local variable bound to a potential term"))
        | _ -> fatal (Matching_wont_refine ("index is not a free variable", PNormal (ctx, x))) in
      Reporter.try_with ~fatal:(fun d ->
          match d.message with
          | Matching_wont_refine (str, x) ->
              emit (Matching_wont_refine (str, x));
              check_nondep_match status ctx (Term.Var index) varty brs None motive
          | No_such_level x ->
              emit (Matching_wont_refine ("index variable occurs in parameter", x));
              check_nondep_match status ctx (Term.Var index) varty brs None motive
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
      let branches =
        Bwd.fold_left
          (fun branches
               ( constr,
                 (Checkable_branch { xs; body; plus_args; env; argtys; index_terms } :
                   (a, m, ij) checkable_branch) ) ->
            let (Snocs efc) = Tbwd.snocs (Telescope.length argtys) in
            (* Create new level variables for the pattern variables to which the constructor is applied, and add corresponding index variables to the context.  The types of those variables are specified in the telescope argtys, and have to be evaluated at the closure environment 'env' and the previous new variables (this is what ext_tel does).  For a higher-dimensional match, the new variables come with their boundaries in n-dimensional cubes. *)
            let newctx, newenv, newvars, newnfs = ext_tel ctx env xs argtys plus_args efc in
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
                        fatal (Matching_wont_refine ("no consistent permutation of context", PUnit))
                    | Bind_some { checked_perm; oldctx; newctx } -> (
                        (* We readback the index and instantiation values into this new context and discard the result, catching No_such_level to turn it into a user Error.  This has the effect of doing an occurs-check that none of the index variables occur in any of the index values.  This is a bit less general than the CDP Solution rule, which (when applied one variable at a time) prohibits only cycles of occurrence.  Note that this exception is still caught by go_check_match, above, causing a fallback to term matching. *)
                        ( Reporter.try_with ~fatal:(fun d ->
                              match d.message with
                              | No_such_level x ->
                                  fatal
                                    (Matching_wont_refine
                                       ("free index variable occurs in inferred index value", x))
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
                            let branch = check status newctx body newty in
                            branches |> Constr.Map.add constr (Term.Branch (efc, perm, branch))
                        (* If not, then we look for something to refute. *)
                        | None ->
                            (* First we check whether any of the new pattern variables created by this match belong to an empty datatype. *)
                            if
                              any_empty newnfs
                              || (* Otherwise, we check the stored "refutables", which include all the previous and succeeding pattern variables. *)
                              List.fold_left
                                (fun s x ->
                                  if s then true
                                  else
                                    let _, sty = synth (Kinetic `Nolet) newctx x in
                                    is_empty sty)
                                false (refutables.refutables plus_args)
                              (* If we found something to refute, we mark this branch as refuted in the compiled match. *)
                            then branches |> Constr.Map.add constr Term.Refute
                            else fatal (Missing_constructor_in_match constr))))
            | _ -> fatal (Anomaly "created datatype is not canonical?"))
          Constr.Map.empty user_branches in
      Match { tm = Term.Var index; dim; branches }
  | _ -> fatal (Matching_on_nondatatype (PVal (ctx, varty)))

and make_match_status :
    type a b ab c n.
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
and check_refute :
    type a b.
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
        (fun () -> check_nondep_match status ctx stm sty Emp None ty)
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
        (fun () -> check_nondep_match status ctx stm sty Emp None ty)
        ~fatal:(fun d ->
          match d.message with
          | Missing_constructor_in_match c ->
              check_refute status ctx tms ty i (Some (Option.value missing ~default:c))
          | _ -> fatal_diagnostic d)

(* Try empty-matching against each successive domain in an iterated pi-type. *)
and check_empty_match_lam :
    type a b. (a, b) Ctx.t -> kinetic value -> [ `First | `Notfirst ] -> (b, potential) term =
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
                      match view_type (Option.get firstty) "is_empty" with
                      | Canonical (_, Data { constrs; _ }, _) ->
                          fatal (Missing_constructor_in_match (fst (Bwd_extra.head constrs)))
                      | _ -> fatal (Matching_on_nondatatype (PVal (ctx, Option.get firstty))))
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

and check_data :
    type a b i bi.
    (b, potential) status ->
    (a, b) Ctx.t ->
    kinetic value ->
    i Fwn.t ->
    (Constr.t, (b, i) Term.dataconstr) Abwd.t ->
    (Constr.t * a Raw.dataconstr located) list ->
    discrete:bool ->
    (b, potential) term =
 fun status ctx ty num_indices checked_constrs raw_constrs ~discrete ->
  match (raw_constrs, status) with
  | [], Potential (head, _, _) ->
      (match head with
      | Constant c -> Discrete.modify (Constant.Map.add c discrete)
      | _ -> ());
      Canonical (Data { indices = num_indices; constrs = checked_constrs; discrete })
  | ( (c, { value = Dataconstr (args, output); loc }) :: raw_constrs,
      Potential (head, current_apps, hyp) ) -> (
      with_loc loc @@ fun () ->
      (* Temporarily bind the current constant to the up-until-now value. *)
      run_with_definition head
        (hyp
           (Term.Canonical
              (Data { indices = num_indices; constrs = checked_constrs; discrete = false })))
      @@ fun () ->
      match (Abwd.find_opt c checked_constrs, output) with
      | Some _, _ -> fatal (Duplicate_constructor_in_data c)
      | None, Some output -> (
          let Checked_tel (args, newctx), argsdisc = check_tel ctx args in
          let discrete = discrete && argsdisc in
          let coutput = check (Kinetic `Nolet) newctx output (universe D.zero) in
          match eval_term (Ctx.env newctx) coutput with
          | Uninst (Neu { head = Const { name = out_head; ins }; args = out_apps; value = _ }, _)
            -> (
              match head with
              | Constant cc when cc = out_head && Option.is_some (is_id_ins ins) -> (
                  let (Wrap indices) =
                    get_indices newctx c (Bwd.to_list current_apps) (Bwd.to_list out_apps)
                      output.loc in
                  match Fwn.compare (Vec.length indices) num_indices with
                  | Eq ->
                      check_data status ctx ty num_indices
                        (checked_constrs |> Abwd.add c (Term.Dataconstr { args; indices }))
                        raw_constrs ~discrete
                  | _ ->
                      (* I think this shouldn't ever happen, no matter what the user writes, since we know at this point that the output is a full application of the correct constant, so it must have the right number of arguments. *)
                      fatal (Anomaly "length of indices mismatch"))
              | _ -> fatal ?loc:output.loc (Invalid_constructor_type c))
          | _ -> fatal ?loc:output.loc (Invalid_constructor_type c))
      | None, None -> (
          match num_indices with
          | Zero ->
              let Checked_tel (args, _), argsdisc = check_tel ctx args in
              let discrete = discrete && argsdisc in
              check_data status ctx ty Fwn.zero
                (checked_constrs |> Abwd.add c (Term.Dataconstr { args; indices = [] }))
                raw_constrs ~discrete
          | Suc _ -> fatal (Missing_constructor_type c)))

and get_indices :
    type a b.
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
              | Some () -> (
                  match D.compare (CubeOf.dim arg) D.zero with
                  | Eq -> readback_nf ctx (CubeOf.find_top arg)
                  | Neq -> fatal (Invalid_constructor_type c))
              | None -> fatal (Invalid_constructor_type c))
          | Value.App (Field _, _) -> fatal (Anomaly "field is not an index"))
        output
  | _ -> fatal (Invalid_constructor_type c)

(* The common prefix of checking a codatatype or record type, which dynamically binds the current constant to the up-until-now value.  Since this binding has to scope over the rest of the functions that are specific to codata or records, it uses CPS. *)
and with_codata_so_far :
    type a b n c.
    (b, potential) status ->
    potential eta ->
    (a, b) Ctx.t ->
    opacity ->
    n D.t ->
    (D.zero, n, n, normal) TubeOf.t ->
    (Field.t, ((b, n) snoc, kinetic) term) Abwd.t ->
    ((n, Ctx.Binding.t) CubeOf.t -> c) ->
    c =
 fun (Potential (h, args, hyp)) eta ctx opacity dim tyargs checked_fields cont ->
  (* We can always create a constant with the (0,0,0) insertion, even if its dimension is actually higher. *)
  let head = head_of_potential h in
  let value =
    Value.Canonical
      (Codata { eta; opacity; env = Ctx.env ctx; ins = zero_ins dim; fields = checked_fields })
  in
  let prev_ety =
    Uninst (Neu { head; args; value = ready value }, Lazy.from_val (inst (universe dim) tyargs))
  in
  let _, domvars =
    dom_vars (Ctx.length ctx)
      (TubeOf.plus_cube
         (TubeOf.mmap { map = (fun _ [ nf ] -> nf.tm) } [ tyargs ])
         (CubeOf.singleton prev_ety)) in
  run_with_definition h
    (hyp (Term.Canonical (Codata { eta; opacity; dim; fields = checked_fields })))
  @@ fun () -> cont domvars

and check_codata :
    type a b n.
    (b, potential) status ->
    (a, b) Ctx.t ->
    (D.zero, n, n, normal) TubeOf.t ->
    (Field.t, ((b, n) snoc, kinetic) term) Abwd.t ->
    (Field.t * (string option * a N.suc check located)) list ->
    (b, potential) term =
 fun status ctx tyargs checked_fields raw_fields ->
  let dim = TubeOf.inst tyargs in
  match raw_fields with
  | [] -> Canonical (Codata { eta = Noeta; opacity = `Opaque; dim; fields = checked_fields })
  | (fld, (x, rty)) :: raw_fields ->
      with_codata_so_far status Noeta ctx `Opaque dim tyargs checked_fields @@ fun domvars ->
      let newctx = Ctx.cube_vis ctx x domvars in
      let cty = check (Kinetic `Nolet) newctx rty (universe D.zero) in
      let checked_fields = Snoc (checked_fields, (fld, cty)) in
      check_codata status ctx tyargs checked_fields raw_fields

and check_record :
    type a f1 f2 f af d acd b n.
    (b, potential) status ->
    n D.t ->
    (a, b) Ctx.t ->
    opacity ->
    (D.zero, n, n, normal) TubeOf.t ->
    (N.zero, n, string option, f1) NICubeOf.t ->
    (Field.t * string, f2) Bwv.t ->
    (f1, f2, f) N.plus ->
    (a, f, af) N.plus ->
    (Field.t, ((b, n) snoc, kinetic) term) Abwd.t ->
    (af, d, acd) Raw.tel ->
    (b, potential) term =
 fun status dim ctx opacity tyargs vars ctx_fields fplus af checked_fields raw_fields ->
  match raw_fields with
  | Emp -> Term.Canonical (Codata { eta = Eta; opacity; dim; fields = checked_fields })
  | Ext (None, _, _) -> fatal (Anomaly "unnamed field in check_record")
  | Ext (Some name, rty, raw_fields) ->
      with_codata_so_far status Eta ctx opacity dim tyargs checked_fields @@ fun domvars ->
      let newctx = Ctx.vis_fields ctx vars domvars ctx_fields fplus af in
      let cty = check (Kinetic `Nolet) newctx rty (universe D.zero) in
      let fld = Field.intern name in
      let checked_fields = Snoc (checked_fields, (fld, cty)) in
      let ctx_fields = Bwv.Snoc (ctx_fields, (fld, name)) in
      check_record status dim ctx opacity tyargs vars ctx_fields (Suc fplus) (Suc af) checked_fields
        raw_fields

and check_struct :
    type a b c s m n.
    (b, s) status ->
    s eta ->
    (a, b) Ctx.t ->
    (Field.t option, a check located) Abwd.t ->
    kinetic value ->
    m D.t ->
    (Field.t, ((c, n) snoc, kinetic) term) Abwd.t ->
    (b, s) term =
 fun status eta ctx tms ty dim fields ->
  (* The type of each record field, at which we check the corresponding field supplied in the struct, is the type associated to that field name in general, evaluated at the supplied parameters and at "the term itself".  We don't have the whole term available while typechecking, of course, but we can build a version of it that contains all the previously typechecked fields, which is all we need for a well-typed record.  So we iterate through the fields (in the order specified in the *type*, since that determines the dependencies) while also accumulating the previously typechecked and evaluated fields.  At the end, we throw away the evaluated fields (although as usual, that seems wasteful). *)
  let tms, ctms =
    check_fields status eta ctx ty dim
      (* We convert the backwards alist of fields and values into a forwards list of field names only. *)
      (Bwd.fold_right (fun (fld, _) flds -> fld :: flds) fields [])
      tms Emp Emp in
  (* We had to typecheck the fields in the order given in the record type, since later ones might depend on earlier ones.  But then we re-order them back to the order given in the struct, to match what the user wrote. *)
  let fields =
    Bwd.map
      (function
        | Some fld, _ -> (
            match Abwd.find_opt fld ctms with
            | Some x -> (fld, x)
            | None -> fatal (Anomaly "missing field in check"))
        | None, _ -> fatal (Extra_field_in_tuple None))
      tms in
  Term.Struct (eta, dim, fields, energy status)

and check_fields :
    type a b s n.
    (b, s) status ->
    s eta ->
    (a, b) Ctx.t ->
    kinetic value ->
    n D.t ->
    Field.t list ->
    (Field.t option, a check located) Abwd.t ->
    (Field.t, s lazy_eval * [ `Labeled | `Unlabeled ]) Abwd.t ->
    (Field.t, (b, s) term * [ `Labeled | `Unlabeled ]) Abwd.t ->
    (Field.t option, a check located) Abwd.t
    * (Field.t, (b, s) term * [ `Labeled | `Unlabeled ]) Abwd.t =
 fun status eta ctx ty dim fields tms etms ctms ->
  (* The insertion on a struct being checked is the identity, but it stores the substitution dimension of the type being checked against.  If this is a higher-dimensional record (e.g. Gel), there could be a nontrivial right dimension being trivially inserted, but that will get added automatically by an appropriate symmetry action if it happens. *)
  let str = Value.Struct (etms, ins_zero dim, energy status) in
  match (fields, status) with
  | [], _ -> (tms, ctms)
  | fld :: fields, Potential (name, args, hyp) ->
      (* Temporarily bind the current constant to the up-until-now value. *)
      run_with_definition name (hyp (Term.Struct (eta, dim, ctms, energy status))) @@ fun () ->
      (* The insertion on the *constant* being checked, by contrast, is always zero, since the constant is not nontrivially substituted at all yet. *)
      let head = head_of_potential name in
      let prev_etm = Uninst (Neu { head; args; value = ready (Val str) }, Lazy.from_val ty) in
      check_field status eta ctx ty dim fld fields prev_etm tms etms ctms
  | fld :: fields, Kinetic _ -> check_field status eta ctx ty dim fld fields str tms etms ctms

and check_field :
    type a b s n.
    (b, s) status ->
    s eta ->
    (a, b) Ctx.t ->
    kinetic value ->
    n D.t ->
    Field.t ->
    Field.t list ->
    kinetic value ->
    (Field.t option, a check located) Abwd.t ->
    (Field.t, s lazy_eval * [ `Labeled | `Unlabeled ]) Abwd.t ->
    (Field.t, (b, s) term * [ `Labeled | `Unlabeled ]) Abwd.t ->
    (Field.t option, a check located) Abwd.t
    * (Field.t, (b, s) term * [ `Labeled | `Unlabeled ]) Abwd.t =
 fun status eta ctx ty dim fld fields prev_etm tms etms ctms ->
  let mkstatus lbl : (b, s) status -> (b, s) status = function
    | Kinetic l -> Kinetic l
    | Potential (c, args, hyp) ->
        let args = Snoc (args, App (Field fld, ins_zero D.zero)) in
        let hyp tm = hyp (Term.Struct (eta, dim, Snoc (ctms, (fld, (tm, lbl))), energy status)) in
        Potential (c, args, hyp) in
  let ety = tyof_field prev_etm ty fld in
  match Abwd.find_opt (Some fld) tms with
  | Some tm ->
      let ctm = check (mkstatus `Labeled status) ctx tm ety in
      let etms = Abwd.add fld (lazy_eval (Ctx.env ctx) ctm, `Labeled) etms in
      let ctms = Snoc (ctms, (fld, (ctm, `Labeled))) in
      check_fields status eta ctx ty dim fields tms etms ctms
  | None -> (
      match Abwd.find_opt_and_update_key None (Some fld) tms with
      | Some (tm, tms) ->
          let ctm = check (mkstatus `Unlabeled status) ctx tm ety in
          let etms = Abwd.add fld (lazy_eval (Ctx.env ctx) ctm, `Unlabeled) etms in
          let ctms = Snoc (ctms, (fld, (ctm, `Unlabeled))) in
          check_fields status eta ctx ty dim fields tms etms ctms
      | None -> fatal (Missing_field_in_tuple fld))

and synth :
    type a b s. (b, s) status -> (a, b) Ctx.t -> a synth located -> (b, s) term * kinetic value =
 fun status ctx tm ->
  with_loc tm.loc @@ fun () ->
  match (tm.value, status) with
  | Var i, _ -> (
      match Ctx.lookup ctx i with
      | `Var (_, x, v) -> (realize status (Term.Var v), x.ty)
      | `Field (lvl, x, fld) -> (
          match Ctx.find_level ctx lvl with
          | Some v -> (realize status (Term.Field (Var v, fld)), tyof_field x.tm x.ty fld)
          | None -> fatal (Anomaly "level not found in field view")))
  | Const name, _ ->
      let ty, _ = Global.find name in
      (realize status (Const name), eval_term (Emp D.zero) ty)
  | Field (tm, fld), _ ->
      let stm, sty = synth (Kinetic `Nolet) ctx tm in
      (* To take a field of something, the type of the something must be a record-type that contains such a field, possibly substituted to a higher dimension and instantiated. *)
      let etm = eval_term (Ctx.env ctx) stm in
      let fld, _, newty = tyof_field_withname ~severity:Asai.Diagnostic.Error etm sty fld in
      (realize status (Field (stm, fld)), newty)
  | UU, _ -> (realize status (Term.UU D.zero), universe D.zero)
  | Pi (x, dom, cod), _ ->
      (* User-level pi-types are always dimension zero, so the domain must be a zero-dimensional type. *)
      let cdom = check (Kinetic `Nolet) ctx dom (universe D.zero) in
      let edom = eval_term (Ctx.env ctx) cdom in
      let ccod = check (Kinetic `Nolet) (Ctx.ext ctx x edom) cod (universe D.zero) in
      (realize status (pi x cdom ccod), universe D.zero)
  | App _, _ ->
      (* If there's at least one application, we slurp up all the applications, synthesize a type for the function, and then pass off to synth_apps to iterate through all the arguments. *)
      let fn, locs, args = spine tm in
      let sfn, sty = synth (Kinetic `Nolet) ctx fn in
      let stm, sty = synth_apps ctx { value = sfn; loc = fn.loc } sty locs args in
      (realize status stm, sty)
  | Act (str, fa, { value = Synth x; loc }), _ ->
      let x = { value = x; loc } in
      let sx, ety =
        if locking fa then Global.run_locked (fun () -> synth (Kinetic `Nolet) (Ctx.lock ctx) x)
        else synth (Kinetic `Nolet) ctx x in
      let ex = eval_term (Ctx.env ctx) sx in
      ( realize status (Term.Act (sx, fa)),
        with_loc x.loc @@ fun () ->
        act_ty ex ety fa ~err:(Low_dimensional_argument_of_degeneracy (str, cod_deg fa)) )
  | Act _, _ -> fatal (Nonsynthesizing "argument of degeneracy")
  | Asc (tm, ty), _ ->
      let cty = check (Kinetic `Nolet) ctx ty (universe D.zero) in
      let ety = eval_term (Ctx.env ctx) cty in
      let ctm = check status ctx tm ety in
      (ctm, ety)
  | Let (x, v, body), _ ->
      let ctm, Not_none ety = synth_or_check_let status ctx x v body None in
      (* The synthesized type of the body is also correct for the whole let-expression, because it was synthesized in a context where the variable is bound not just to its type but to its value, so it doesn't include any extra level variables (i.e. it can be silently "strengthened"). *)
      (ctm, ety)
  | Match _, Kinetic l -> (
      match l with
      | `Let -> raise Case_tree_construct_in_let
      | `Nolet ->
          emit (Bare_case_tree_construct "match");
          (* A match in a kinetic synthesizing position, we can treat like a let-binding that returns the bound (metavariable) value.  Of course we can shortcut the binding by just inserting the metavariable as the result.  This code is copied and slightly modified from synth_or_check_let.  *)
          let meta = Meta.make_def "match" None (Ctx.dbwd ctx) Potential in
          let tmstatus = Potential (Meta (meta, Ctx.env ctx), Emp, fun x -> x) in
          let sv, svty = synth tmstatus ctx tm in
          let vty = readback_val ctx svty in
          let termctx = readback_ctx ctx in
          Global.add_meta meta ~termctx ~tm:sv ~ty:vty ~energy:Potential;
          (Term.Meta (meta, Kinetic), svty))
  | Match { tm; sort = `Explicit motive; branches; refutables = _ }, Potential _ ->
      synth_dep_match status ctx tm branches motive
  | Match { tm; sort = `Implicit; branches; refutables = _ }, Potential _ ->
      emit (Matching_wont_refine ("match in synthesizing position", PUnit));
      synth_nondep_match status ctx tm branches None
  | Match { tm; sort = `Nondep i; branches; refutables = _ }, Potential _ ->
      synth_nondep_match status ctx tm branches (Some i)

(* Given something that can be applied, its type, and a list of arguments, check the arguments in appropriately-sized groups. *)
and synth_apps :
    type a b.
    (a, b) Ctx.t ->
    (b, kinetic) term located ->
    kinetic value ->
    Asai.Range.t option list ->
    a check located list ->
    (b, kinetic) term * kinetic value =
 fun ctx sfn sty locs args ->
  (* To determine what to do, we inspect the (fully instantiated) *type* of the function being applied.  Failure of view_type here is really a bug, not a user error: the user can try to check something against an abstraction as if it were a type, but our synthesis functions should never synthesize (say) a lambda-abstraction as if it were a type. *)
  let afn, aty, alocs, aargs =
    match view_type sty "synth_apps" with
    (* The obvious thing we can "apply" is an element of a pi-type. *)
    | Pi (_, doms, cods, tyargs) -> synth_app ctx sfn doms cods tyargs locs args
    (* We can also "apply" a higher-dimensional *type*, leading to a (further) instantiation of it.  Here the number of arguments must exactly match *some* integral instantiation. *)
    | UU tyargs -> synth_inst ctx sfn tyargs locs args
    (* Something that synthesizes a type that isn't a pi-type or a universe cannot be applied to anything, but this is a user error, not a bug. *)
    | _ ->
        fatal ?loc:sfn.loc (Applying_nonfunction_nontype (PTerm (ctx, sfn.value), PVal (ctx, sty)))
  in
  (* synth_app and synth_inst fail if there aren't enough arguments.  If they used up all the arguments, we're done; otherwise we continue with the rest of the arguments. *)
  match aargs with
  | [] -> (afn.value, aty)
  | _ :: _ -> synth_apps ctx afn aty alocs aargs

and synth_app :
    type a b n.
    (a, b) Ctx.t ->
    (b, kinetic) term located ->
    (n, kinetic value) CubeOf.t ->
    (n, unit) BindCube.t ->
    (D.zero, n, n, normal) TubeOf.t ->
    Asai.Range.t option list ->
    a check located list ->
    (b, kinetic) term located * kinetic value * Asai.Range.t option list * a check located list =
 fun ctx sfn doms cods tyargs locs args ->
  let module M = Monad.State (struct
    type t = Asai.Range.t option * Asai.Range.t option list * a check located list
  end) in
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
              | _, [] | [], _ -> with_loc loc @@ fun () -> fatal Not_enough_arguments_to_function
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
            let ctm = check (Kinetic `Nolet) ctx tm ty in
            let tm = eval_term (Ctx.env ctx) ctm in
            Hashtbl.add eargtbl (SFace_of fa) { tm; ty };
            return (ctm @: [ tm ]));
      }
      [ doms ] (Cons (Cons Nil)) (sfn.loc, locs, args) in
  (* Evaluate cod at these evaluated arguments and instantiate it at the appropriate values of tyargs. *)
  let output = tyof_app cods tyargs eargs in
  ({ value = Term.App (sfn.value, cargs); loc = newloc }, output, rlocs, rest)

and synth_inst :
    type a b n.
    (a, b) Ctx.t ->
    (b, kinetic) term located ->
    (D.zero, n, n, normal) TubeOf.t ->
    Asai.Range.t option list ->
    a check located list ->
    (b, kinetic) term located * kinetic value * Asai.Range.t option list * a check located list =
 fun ctx sfn tyargs locs args ->
  let module M = Monad.State (struct
    type t = Asai.Range.t option * Asai.Range.t option list * a check located list
  end) in
  let n = TubeOf.inst tyargs in
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
                          Hashtbl.find eargtbl (SFace_of (comp_sface fa (sface_of_tface fb))));
                    } in
                let ty = inst tyarg.tm kargs in
                let ctm = check (Kinetic `Nolet) ctx tm ty in
                (* Then we evaluate it and assemble a normal version to store in the hashtbl, before returning the checked and evaluated versions. *)
                let tm = eval_term (Ctx.env ctx) ctm in
                let ntm = { tm; ty } in
                Hashtbl.add eargtbl (SFace_of fa) ntm;
                return (ctm @: [ ntm ]));
          }
          [ tyargs1 ] (Cons (Cons Nil)) (sfn.loc, locs, args) in
      (* The synthesized type *of* the instantiation is itself a full instantiation of a universe, at the instantiations of the type arguments at the evaluated term arguments.  This is computed by tyof_inst. *)
      ({ value = Term.Inst (sfn.value, cargs); loc = newloc }, tyof_inst tyargs eargs, rlocs, rest)

(* Check a list of terms against the types specified in a telescope, evaluating the latter in a supplied environment and in the context of the previously checked terms, and instantiating them at values given in a tube.  See description in context of the call to it above during typechecking of a constructor. *)
and check_at_tel :
    type n a b c bc e.
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
               CubeOf.singleton (TubeOf.plus_cube (val_of_norm_tube tyarg) (CubeOf.singleton etm))
             ))
          tms tys tyargs in
      (newenv, TubeOf.plus_cube ctms (CubeOf.singleton ctm) :: newargs)
  | _ ->
      fatal
        (Wrong_number_of_arguments_to_constructor
           (c, List.length tms - Fwn.to_int (Telescope.length tys)))

(* Given a context and a raw telescope, we can check it to produce a checked telescope and also a new context extended by that telescope.  The returned boolean indicates whether this could be the telescope of arguments of a constructor of a *discrete* datatype. *)
and check_tel : type a b c ac. (a, b) Ctx.t -> (a, c, ac) Raw.tel -> (ac, b) checked_tel * bool =
 fun ctx tel ->
  match tel with
  | Emp -> (Checked_tel (Emp, ctx), true)
  | Ext (x, ty, tys) ->
      let cty = check (Kinetic `Nolet) ctx ty (universe D.zero) in
      let ety = eval_term (Ctx.env ctx) cty in
      let _, newnfs = dom_vars (Ctx.length ctx) (CubeOf.singleton ety) in
      let ctx = Ctx.cube_vis ctx x newnfs in
      let Checked_tel (ctys, ctx), discrete = check_tel ctx tys in
      let discrete = discrete && is_discrete ety in
      (Checked_tel (Ext (x, cty, ctys), ctx), discrete)
