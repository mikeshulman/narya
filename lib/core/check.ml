open Bwd
open Util
open Perhaps
open Tbwd
open Reporter
open Syntax
open Term
open Value
open Inst
open Domvars
open Raw
open Dim
open Act
open Norm
open Equal
open Readback
open Printable
open Asai.Range

let discard : type a. a -> unit = fun _ -> ()

(* Check that a given value is a zero-dimensional type family (something where an indexed datatype could live) and return the length of its domain telescope (the number of indices).  Unfortunately I don't see an easy way to do this without essentially going through all the same steps of extending the context that we would do to check something at that type family. *)
let rec typefam : type a b. (a, b) Ctx.t -> kinetic value -> int =
 fun ctx ty ->
  let (Fullinst (uty, tyargs)) = full_inst ~severity:Asai.Diagnostic.Error ty "typefam" in
  match uty with
  | UU m -> (
      match D.compare m D.zero with
      | Eq -> 0
      | Neq -> fatal (Unimplemented "higher-dimensional datatypes"))
  | Pi (x, doms, cods) -> (
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
  let (Fullinst (uty, tyargs)) = full_inst ty "motive_of_family" in
  match uty with
  | Pi (x, doms, cods) -> (
      match D.compare (TubeOf.inst tyargs) (CubeOf.dim doms) with
      | Eq ->
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
      | Neq -> fatal (Dimension_mismatch ("motive_of_family", TubeOf.inst tyargs, CubeOf.dim doms)))
  | UU dim -> (
      match D.compare (TubeOf.inst tyargs) dim with
      | Eq ->
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
      | Neq -> fatal (Dimension_mismatch ("motive_of_family", TubeOf.inst tyargs, dim)))
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

(* When checking a case tree (a "potential" term), we have to retain some information about the definition being checked.  Specifically, we remember:
   1. The name of the top-level constant being defined.
   2. The arguments that it has been applied to so far at this point in the case tree.  These all start out as variables, but after checking matches some of them get substituted by constructor expressions.
   3. A "hypothesizing" callback that allows us to say "if I were to return such-and-such a term from my current typechecking problem, what would the resulting definition of the top-level constant be?"  This is used when typechecking comatches and codata (and, potentially one day, matches and data as well, such as for HITs) whose later branches depend on the *values* of previous ones.  So as we typecheck the branches of such a thing, we collect a partial definition including all the branches that have been typechecked so far, and temporarily bind the constant to that value while typechecking later branches.  And in order that this is correct, whenever we pass *inside* a case tree construct (lambda, match, or comatch) we wrap the outer callback in an inner one that inserts the correct construct to the hypothesized term.  (It's tempting to think of implementing this with algebraic effects rather than an explicit callback, but I found the purely functional version easier to get correct, even if it does involve passing around more arguments.)

   We parametrize this "status" datatype over the energy of the term (kinetic, chemical, or potential), since only potential terms have any status to remember.  This implies that status also serves the purpose of recording which kind of term we are checking, so we don't need to pass that around separately. *)
type (_, _) status =
  | Kinetic : ('b, kinetic) status
  | Chemical : ('b, chemical) status
  | Potential :
      Constant.t * app Bwd.t * (('b, potential) term -> (emp, potential) term)
      -> ('b, potential) status

let energy : type b s. (b, s) status -> s energy = function
  | Kinetic -> Kinetic
  | Chemical -> Chemical
  | Potential _ -> Potential

let realize : type b s. (b, s) status -> (b, kinetic) term -> (b, s) term =
 fun status tm ->
  match status with
  | Potential _ -> Realize (tm, Potential)
  | Chemical -> Realize (tm, Chemical)
  | Kinetic -> tm

(* The output of checking a telescope includes an extended context. *)
type (_, _) checked_tel =
  | Checked_tel : ('b, 'd, 'bd) Telescope.t * ('ac, 'bd) Ctx.t -> ('ac, 'b) checked_tel

(* Check a term or case tree (depending on the energy: terms are kinetic, case trees are potential). *)
let rec check :
    type a b s. (b, s) status -> (a, b) Ctx.t -> a check located -> kinetic value -> (b, s) term =
 fun status ctx tm ty ->
  with_loc tm.loc @@ fun () : (b, s) term ->
  (* If the "type" is not a type here, or not fully instantiated, that's a user error, not a bug. *)
  let (Fullinst (uty, tyargs)) = full_inst ~severity:Asai.Diagnostic.Error ty "typechecking" in
  match (tm.value, uty, status) with
  (* A Let is a "synthesizing" term so that it *can* synthesize, but in checking position it checks instead (hence why its body is, in general, a "checking" term). *)
  | Synth (Let (x, v, body)), _, Kinetic ->
      let sv, sty = synth Kinetic ctx v in
      let ev = Ctx.eval_term ctx sv in
      Let (x, Kinetic, sv, check Kinetic (Ctx.ext_let ctx x { tm = ev; ty = sty }) body ty)
  | Synth (Let (x, v, body)), _, Potential (c, args, hyp) -> (
      (* The term bound in a potential let can itself be chemical. *)
      let sv, sty = synth Chemical ctx v in
      let status = Potential (c, args, fun body -> hyp (Let (x, Potential, sv, body))) in
      (* However, if it doesn't evaluate completely right now, then we don't have a value to bind the variable to when typechecking the body, so the body must typecheck with a free variable. *)
      match Ctx.eval ctx sv with
      | Val (_, _) -> .
      | Realize (ev, Chemical) ->
          Let (x, Potential, sv, check status (Ctx.ext_let ctx x { tm = ev; ty = sty }) body ty)
      | Unrealized Chemical -> Let (x, Potential, sv, check status (Ctx.ext ctx x sty) body ty))
  | Synth (Let (x, v, body)), _, Chemical -> (
      (* A chemical let is just like a potential one. *)
      let sv, sty = synth Chemical ctx v in
      match Ctx.eval ctx sv with
      | Val (_, _) -> .
      | Realize (ev, Chemical) ->
          Let (x, Chemical, sv, check Chemical (Ctx.ext_let ctx x { tm = ev; ty = sty }) body ty)
      | Unrealized Chemical -> Let (x, Chemical, sv, check Chemical (Ctx.ext ctx x sty) body ty))
  (* An action can always synthesize, but can also check if its degeneracy is a pure permutation, since then the type of the argument can be inferred by applying the inverse permutation to the ambient type. *)
  | Synth (Act (str, fa, x) as stm), _, _ -> (
      match D.compare (dom_deg fa) (cod_deg fa) with
      | Neq -> check_of_synth status ctx stm tm.loc ty
      | Eq ->
          let fainv = perm_inv fa in
          let ty_fainv =
            act_ty
              (Lazy (lazy (fatal (Anomaly "term used in action by inverse symmetry"))))
              ty fainv
              ~err:(Low_dimensional_argument_of_degeneracy (str, cod_deg fa)) in
          let cx =
            (* A pure permutation shouldn't ever be locking, but we may as well keep this here for consistency.  *)
            if locking fa then Global.run_locked (fun () -> check Kinetic (Ctx.lock ctx) x ty_fainv)
            else check Kinetic ctx x ty_fainv in
          realize status (Term.Act (cx, fa)))
  | Lam ({ value = x; _ }, cube, body), Pi (_, doms, cods), _ -> (
      (* TODO: Move this into a helper function, it's too long to go in here. *)
      (* An abstraction can check with any energy, but at chemical energy it forces realization to kinetic from here on. *)
      let m = CubeOf.dim doms in
      match D.compare (TubeOf.inst tyargs) m with
      | Neq -> fatal (Dimension_mismatch ("checking lambda", TubeOf.inst tyargs, m))
      | Eq -> (
          let Eq = D.plus_uniq (TubeOf.plus tyargs) (D.zero_plus m) in
          (* Extend the context by one variable for each type in doms, instantiated at the appropriate previous ones. *)
          let newargs, newnfs = dom_vars (Ctx.length ctx) doms in
          (* A helper function to update the potential status *)
          let mkstatus xs (Potential (c, args, hyp)) =
            let arg = Arg (CubeOf.mmap { map = (fun _ [ x ] -> Ctx.Binding.value x) } [ newnfs ]) in
            Potential
              (c, Snoc (args, App (arg, ins_zero m)), fun tm -> hyp (Lam (xs, Potential, tm))) in
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
              | Wrap (names, Ok (_, af, body)) -> (
                  let xs = Variables (D.zero, D.zero_plus m, names) in
                  let ctx = Ctx.vis ctx D.zero (D.zero_plus m) names newnfs af in
                  match status with
                  | Potential _ -> Lam (xs, Potential, check (mkstatus xs status) ctx body output)
                  | Kinetic -> Lam (xs, Kinetic, check Kinetic ctx body output)
                  | Chemical -> Realize (Lam (xs, Kinetic, check Kinetic ctx body output), Chemical)
                  )
              | Wrap (_, Missing (loc, j)) -> fatal ?loc (Not_enough_lambdas j))
          | `Cube -> (
              (* Here we don't need to slurp up lots of lambdas, but can make do with one. *)
              let xs = singleton_variables m x in
              let ctx = Ctx.cube_vis ctx x newnfs in
              match status with
              | Potential _ ->
                  let status = mkstatus xs status in
                  Lam (xs, Potential, check status ctx body output)
              | Kinetic -> Lam (xs, Kinetic, check Kinetic ctx body output)
              | Chemical -> Realize (Lam (xs, Kinetic, check Kinetic ctx body output), Chemical))))
  | Lam _, _, _ -> fatal (Checking_lambda_at_nonfunction (PUninst (ctx, uty)))
  | Struct (Noeta, _), _, Kinetic -> fatal (Invalid_outside_case_tree "comatch")
  | ( Struct (Noeta, tms),
      (* We don't need to name the arguments here because tyof_field, called below from check_field, uses them. *)
      Neu
        { head = Const { name; _ }; alignment = Lawful (Codata { eta = Noeta; ins; fields; _ }); _ },
      Potential _ ) ->
      is_id_ins ins <|> Comatching_at_degenerated_codata (PConstant name);
      check_struct status Potential Noeta ctx tms ty (cod_left_ins ins) fields
  | ( Struct (Eta, tms),
      Neu { head = Const { name; _ }; alignment = Lawful (Codata { eta = Eta; ins; fields; _ }); _ },
      Potential _ ) ->
      is_id_ins ins <|> Checking_tuple_at_degenerated_record (PConstant name);
      check_struct status Potential Eta ctx tms ty (cod_left_ins ins) fields
  | ( Struct (Eta, tms),
      Neu { head = Const { name; _ }; alignment = Lawful (Codata { eta = Eta; ins; fields; _ }); _ },
      Kinetic ) ->
      is_id_ins ins <|> Checking_tuple_at_degenerated_record (PConstant name);
      check_struct Kinetic Kinetic Eta ctx tms ty (cod_left_ins ins) fields
  | ( Struct (Eta, tms),
      Neu { head = Const { name; _ }; alignment = Lawful (Codata { eta = Eta; ins; fields; _ }); _ },
      Chemical ) ->
      is_id_ins ins <|> Checking_tuple_at_degenerated_record (PConstant name);
      realize Chemical (check_struct Kinetic Kinetic Eta ctx tms ty (cod_left_ins ins) fields)
  | Struct (Noeta, _), _, _ -> fatal (Comatching_at_noncodata (PUninst (ctx, uty)))
  | Struct (Eta, _), _, _ -> fatal (Checking_tuple_at_nonrecord (PUninst (ctx, uty)))
  | ( Constr ({ value = constr; loc = constr_loc }, args),
      Neu
        {
          (* The insertion should always be trivial, since datatypes are always 0-dimensional. *)
          head = Const { name; _ };
          alignment = Lawful (Data { dim; indices = Filled ty_indices; constrs });
          _;
        },
      _ ) -> (
      (* TODO: Move this into a helper function, it's too long to go in here. *)
      (* We don't need the *types* of the parameters or indices, which are stored in the type of the constant name.  The variable ty_indices (defined above) contains the *values* of the indices of this instance of the datatype, while tyargs (defined by full_inst, way above) contains the instantiation arguments of this instance of the datatype.  We check that the dimensions agree, and find our current constructor in the datatype definition. *)
      match (D.compare (TubeOf.inst tyargs) dim, Constr.Map.find_opt constr constrs) with
      | _, None -> fatal ?loc:constr_loc (No_such_constructor (`Data (PConstant name), constr))
      | Neq, _ -> fatal (Dimension_mismatch ("checking constr", TubeOf.inst tyargs, dim))
      | Eq, Some (Dataconstr { env; args = constr_arg_tys; indices = constr_indices }) ->
          (* To typecheck a higher-dimensional instance of our constructor constr at the datatype, all the instantiation arguments must also be applications of lower-dimensional versions of that same constructor.  We check this, and extract the arguments of those lower-dimensional constructors as a tube of lists in the variable "tyarg_args". *)
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
                          let _ = D.compare n (dom_tface fa) in
                          List.fold_right (fun a args -> CubeOf.find_top a :: args) tmargs []
                    | _ ->
                        fatal
                          (Missing_instantiation_constructor (constr, `Nonconstr (PNormal (ctx, tm)))));
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
                CubeOf.build dim { build = (fun fa -> eval_term (Act (env, op_of_sface fa)) ix) })
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
                          | Some () ->
                              fatal
                                (Unequal_indices
                                   (PNormal (ctx, { tm = t1; ty = t2.ty }), PNormal (ctx, t2)))
                          | None -> fatal (Anomaly "mismatching lower-dimensional constructors")));
                }
                [ t1s; t2s ])
            [ constr_indices; ty_indices ];
          realize status (Term.Constr (constr, dim, newargs)))
  | Constr ({ value; loc }, _), _, _ ->
      fatal ?loc (No_such_constructor (`Other (PUninst (ctx, uty)), value))
  | Synth (Match _), _, Kinetic -> fatal (Invalid_outside_case_tree "match")
  | Synth (Match (tm, `Implicit, brs)), _, Potential _ ->
      check_implicit_match status ctx tm brs ty Potential
  | Synth (Match (tm, `Implicit, brs)), _, Chemical ->
      check_implicit_match status ctx tm brs ty Chemical
  | Synth (Match (tm, `Nondep i, brs)), _, Potential _ ->
      let stm, sty = synth Kinetic ctx tm in
      check_nondep_match status ctx stm sty brs (Some i) ty Potential
  | Synth (Match (tm, `Nondep i, brs)), _, Chemical ->
      let stm, sty = synth Kinetic ctx tm in
      check_nondep_match status ctx stm sty brs (Some i) ty Chemical
  (* We don't need to deal with `Explicit matches here, since they can always synthesize a type and hence be caught by the catch-all for checking synthesizing terms, below. *)
  | Empty_co_match, Pi _, _ ->
      (* Checking [] at a pi-type interprets it as a pattern-matching lambda over an empty datatype. *)
      let x = { value = None; loc = None } in
      let body =
        {
          value = Synth (Match ({ value = Var (Top, None); loc = None }, `Implicit, []));
          loc = tm.loc;
        } in
      check status ctx { value = Raw.Lam (x, `Normal, body); loc = tm.loc } ty
  (* Otherwise, we interpret it as a comatch into an empty codatatype. *)
  | Empty_co_match, _, _ -> check status ctx { value = Struct (Noeta, Abwd.empty); loc = tm.loc } ty
  (* Now we go through the canonical types. *)
  | Codata fields, UU m, Potential _ -> (
      match D.compare (TubeOf.inst tyargs) m with
      | Neq -> fatal (Dimension_mismatch ("checking codata", TubeOf.inst tyargs, m))
      | Eq -> check_codata status ctx tyargs Emp (Bwd.to_list fields))
  | Record (abc, xs, fields), UU m, Potential _ -> (
      match D.compare (TubeOf.inst tyargs) m with
      | Neq -> fatal (Dimension_mismatch ("checking record", TubeOf.inst tyargs, m))
      | Eq ->
          let dim = TubeOf.inst tyargs in
          let (Vars (af, vars)) = vars_of_vec abc.loc dim abc.value xs in
          check_record status dim ctx tyargs vars Emp Zero af Emp fields)
  | Data constrs, _, Potential _ ->
      (* For a datatype, the type to check against might not be a universe, it could include indices. *)
      let (Wrap num_indices) = Fwn.of_int (typefam ctx ty) in
      check_data status ctx ty num_indices Constr.Map.empty (Bwd.to_list constrs)
  | Codata _, _, Potential _ ->
      fatal (Checking_canonical_at_nonuniverse ("codatatype", PVal (ctx, ty)))
  | Record _, _, Potential _ ->
      fatal (Checking_canonical_at_nonuniverse ("record type", PVal (ctx, ty)))
  | Codata _, _, Kinetic | Codata _, _, Chemical -> fatal (Invalid_outside_case_tree "codatatype")
  | Record _, _, Kinetic | Record _, _, Chemical -> fatal (Invalid_outside_case_tree "record type")
  | Data _, _, Kinetic | Data _, _, Chemical -> fatal (Invalid_outside_case_tree "datatype")
  (* Penultimately, we could have a hole. *)
  | Hole vars, _, _ ->
      let energy = energy status in
      let meta = Meta.make `Hole (Ctx.dbwd ctx) energy in
      let ty = readback_val ctx ty in
      let termctx = readback_ctx ctx in
      Galaxy.add meta vars termctx ty energy;
      emit (Hole_generated (meta, Termctx.PHole (vars, termctx, ty)));
      Meta meta
  (* And lastly, if we have a synthesizing term, we synthesize it. *)
  | Synth stm, _, _ -> check_of_synth status ctx stm tm.loc ty

(* Deal with a synthesizing term in checking position. *)
and check_of_synth :
    type a b s.
    (b, s) status -> (a, b) Ctx.t -> a synth -> Asai.Range.t option -> kinetic value -> (b, s) term
    =
 fun status ctx stm loc ty ->
  let sval, sty = synth status ctx { value = stm; loc } in
  equal_val (Ctx.length ctx) sty ty <|> Unequal_synthesized_type (PVal (ctx, sty), PVal (ctx, ty));
  sval

(* Check a match statement without an explicit motive supplied by the user.  This means if the discriminee is a well-behaved variable, it can be a variable match; otherwise it reverts back to a non-dependent match. *)
and check_implicit_match :
    type a b s.
    (b, s) status ->
    (a, b) Ctx.t ->
    a synth located ->
    a branch list ->
    kinetic value ->
    s nonkinetic ->
    (b, s) term =
 fun status ctx tm brs motive energy ->
  match tm with
  (* For a variable match, the variable must not be let-bound to a value or be a field access variable.  Checking that it isn't also gives us its De Bruijn level, its type, and its checked-index.  If it's not a free variable, or if we're not in a case tree or if the motive was supplied explicitly, we obtain its value and type; then we pass on to the appropriate checking function. *)
  | { value = Var ix; loc } -> (
      match Ctx.lookup ctx ix with
      | `Field (_, _, fld) ->
          emit ?loc (Matching_wont_refine ("discriminee is record field", PField fld));
          let tm, varty = synth Kinetic ctx tm in
          check_nondep_match status ctx tm varty brs None motive energy
      | `Var (None, _, ix) ->
          emit ?loc (Matching_wont_refine ("discriminee is let-bound", PTerm (ctx, Var ix)));
          let tm, varty = synth Kinetic ctx tm in
          check_nondep_match status ctx tm varty brs None motive energy
      | `Var (Some level, { tm = _; ty = varty }, index) ->
          check_var_match status ctx level index varty brs motive energy)
  | _ ->
      let tm, varty = synth Kinetic ctx tm in
      check_nondep_match status ctx tm varty brs None motive energy

(* Either check a non-dependent match against a specified type, or synthesize a type for it from the first branch and then check the others against that type.  Which to do is determined by whether the motive passed is Some or None, and the return includes a type under the opposite conditions. *)
and synth_or_check_nondep_match :
    type a b s p.
    (b, s) status ->
    (a, b) Ctx.t ->
    (b, kinetic) term ->
    kinetic value ->
    a branch list ->
    int located option ->
    (kinetic value, p) Perhaps.t ->
    s nonkinetic ->
    (b, s) term * (kinetic value, p) Perhaps.not =
 fun status ctx tm varty brs i motive energy ->
  (* We look up the type of the discriminee, which must be a datatype, without any degeneracy applied outside, and at the same dimension as its instantiation. *)
  let (Fullinst (uvarty, inst_args)) = full_inst varty "synth_or_check_nondep_match" in
  match uvarty with
  | Neu
      {
        head = Const { name; _ };
        args = _;
        alignment = Lawful (Data { dim; indices = Filled indices; constrs });
      } -> (
      (match i with
      | Some { value; loc } ->
          let needed = Fwn.to_int (Vec.length indices) + 1 in
          if value <> needed then fatal ?loc (Wrong_number_of_arguments_to_motive needed)
      | None -> ());
      match D.compare dim (TubeOf.inst inst_args) with
      | Neq -> fatal (Dimension_mismatch ("var match", dim, TubeOf.inst inst_args))
      | Eq -> (
          (* We save the supplied type, if any. *)
          let ty : kinetic value option ref =
            ref
              (match motive with
              | Some ty -> Some ty
              | None -> None) in
          (* We now iterate through the branches supplied by the user, typechecking them and inserting them in the match tree. *)
          let branches =
            List.fold_left
              (fun branches (Branch (constr, xs, user_args, body)) ->
                if Constr.Map.mem constr.value branches then
                  fatal ?loc:constr.loc (Duplicate_constructor_in_match constr.value);
                (* Get the argument types and index terms for the constructor of this branch. *)
                let (Dataconstr { env; args = argtys; indices = _ }) =
                  Reporter.with_loc constr.loc @@ fun () ->
                  Constr.Map.find_opt constr.value constrs
                  <|> No_such_constructor_in_match (PConstant name, constr.value) in
                let (Snocs efc) = Tbwd.snocs (Telescope.length argtys) in
                (* The user needs to have supplied the right number of pattern variable arguments to the constructor. *)
                match Fwn.compare (Fwn.bplus_right user_args.value) (Telescope.length argtys) with
                | Neq ->
                    fatal ?loc:user_args.loc
                      (Wrong_number_of_arguments_to_pattern
                         ( constr.value,
                           Fwn.to_int (Fwn.bplus_right user_args.value)
                           - Fwn.to_int (Telescope.length argtys) ))
                | Eq -> (
                    (* Create new level variables for the pattern variables to which the constructor is applied, and add corresponding index variables to the context.  The types of those variables are specified in the telescope argtys, and have to be evaluated at the closure environment 'env' and the previous new variables (this is what ext_tel does).  For a higher-dimensional match, the new variables come with their boundaries in n-dimensional cubes. *)
                    let newctx, _, _ = ext_tel ctx env xs argtys user_args.value efc in
                    let perm = Tbwd.id_perm in
                    let status =
                      make_match_status status tm dim branches efc None perm constr.value in
                    (* Finally, we recurse into the "body" of the branch. *)
                    match !ty with
                    | Some motive ->
                        (* If we have a type, check against it. *)
                        branches
                        |> Constr.Map.add constr.value
                             (Term.Branch (efc, perm, check status newctx body motive))
                    | None -> (
                        (* If we don't have a type yet, try to synthesize a type from this branch. *)
                        match body with
                        | { value = Synth value; loc } ->
                            let sbr, sty = synth status newctx { value; loc } in
                            (* The type synthesized is only valid for the whole match if it doesn't depend on the pattern variables.  We check that by reading it back into the original context. *)
                            Reporter.try_with ~fatal:(fun d ->
                                match d.message with
                                | No_such_level _ ->
                                    fatal
                                      (Invalid_synthesized_type
                                         ("first branch of match", PVal (newctx, sty)))
                                | _ -> fatal_diagnostic d)
                            @@ fun () ->
                            discard (readback_val ctx sty);
                            ty := Some sty;
                            branches |> Constr.Map.add constr.value (Term.Branch (efc, perm, sbr))
                        | _ ->
                            fatal
                              (Nonsynthesizing
                                 "first branch in synthesizing match without return annotation"))))
              Constr.Map.empty brs in
          (* Coverage check *)
          Constr.Map.iter
            (fun c _ ->
              if not (Constr.Map.mem c branches) then fatal (Missing_constructor_in_match c))
            constrs;
          match (motive, !ty) with
          | Some _, _ -> (Match { tm; dim; branches; energy }, Not_some)
          | None, Some ty -> (Match { tm; dim; branches; energy }, Not_none ty)
          | None, None -> fatal (Nonsynthesizing "empty match")))
  | _ -> fatal (Matching_on_nondatatype (PUninst (ctx, uvarty)))

and check_nondep_match :
    type a b s.
    (b, s) status ->
    (a, b) Ctx.t ->
    (b, kinetic) term ->
    kinetic value ->
    a branch list ->
    int located option ->
    kinetic value ->
    s nonkinetic ->
    (b, s) term =
 fun status ctx tm varty brs i motive energy ->
  let ctm, Not_some = synth_or_check_nondep_match status ctx tm varty brs i (Some motive) energy in
  ctm

and synth_nondep_match :
    type a b s.
    (b, s) status ->
    (a, b) Ctx.t ->
    a synth located ->
    a branch list ->
    int located option ->
    s nonkinetic ->
    (b, s) term * kinetic value =
 fun status ctx tm brs i energy ->
  let sv, varty = synth Kinetic ctx tm in
  let stm, Not_none sty = synth_or_check_nondep_match status ctx sv varty brs i None energy in
  (stm, sty)

(* Check a dependently typed match, with motive supplied by the user.  (Thus we have to typecheck the motive as well.) *)
and synth_dep_match :
    type a b s.
    (b, s) status ->
    (a, b) Ctx.t ->
    a synth located ->
    a branch list ->
    a check located ->
    s nonkinetic ->
    (b, s) term * kinetic value =
 fun status ctx tm brs motive energy ->
  let module S = Monad.State (struct
    type t = kinetic value
  end) in
  let module MC = CubeOf.Monadic (S) in
  let module MT = TubeOf.Monadic (S) in
  (* We look up the type of the discriminee, which must be a datatype, without any degeneracy applied outside, and at the same dimension as its instantiation. *)
  let ctm, varty = synth Kinetic ctx tm in
  let (Fullinst (uvarty, inst_args)) = full_inst varty "synth_dep_match" in
  match uvarty with
  | Neu
      {
        head = Const { name; ins };
        args = varty_args;
        alignment = Lawful (Data { dim; indices = Filled var_indices; constrs });
      } -> (
      match (is_id_ins ins, D.compare dim (TubeOf.inst inst_args)) with
      | _, Neq -> fatal (Dimension_mismatch ("var match", dim, TubeOf.inst inst_args))
      | None, _ -> fatal (Anomaly "match variable has nonidentity degeneracy")
      | Some (), Eq -> (
          let tmparams, tmindices = Vec.take_bwd (Vec.length var_indices) varty_args in
          (* To compute the type at which to check the motive, we re-apply the datatype constant to its parameters only, and then extract its type. *)
          let uvarty_params =
            Bwd.fold_left
              (fun fn arg ->
                match arg with
                | Value.App (Arg args, _) -> apply_term fn (val_of_norm_cube args)
                | Value.App (Field fld, _) -> field fn fld)
              (eval_term (Emp dim) (Const name))
              tmparams in
          match uvarty_params with
          | Uninst (_, (lazy uvarty_params_ty)) ->
              let motivety = motive_of_family ctx uvarty_params uvarty_params_ty in
              let emotivety = Ctx.eval_term ctx motivety in
              let cmotive = check Kinetic ctx motive emotivety in
              let emotive = Ctx.eval_term ctx cmotive in
              (* We now iterate through the branches supplied by the user, typechecking them and inserting them in the match tree. *)
              let branches =
                List.fold_left
                  (fun branches (Branch (constr, xs, user_args, body)) ->
                    if Constr.Map.mem constr.value branches then
                      fatal ?loc:constr.loc (Duplicate_constructor_in_match constr.value);
                    (* Get the argument types and index terms for the constructor of this branch. *)
                    let (Dataconstr { env; args = argtys; indices = index_terms }) =
                      Reporter.with_loc constr.loc @@ fun () ->
                      Constr.Map.find_opt constr.value constrs
                      <|> No_such_constructor_in_match (PConstant name, constr.value) in
                    let (Snocs efc) = Tbwd.snocs (Telescope.length argtys) in
                    (* The user needs to have supplied the right number of pattern variable arguments to the constructor. *)
                    match
                      Fwn.compare (Fwn.bplus_right user_args.value) (Telescope.length argtys)
                    with
                    | Neq ->
                        fatal ?loc:user_args.loc
                          (Wrong_number_of_arguments_to_pattern
                             ( constr.value,
                               Fwn.to_int (Fwn.bplus_right user_args.value)
                               - Fwn.to_int (Telescope.length argtys) ))
                    | Eq ->
                        (* Create new level variables for the pattern variables to which the constructor is applied, and add corresponding index variables to the context.  The types of those variables are specified in the telescope argtys, and have to be evaluated at the closure environment 'env' and the previous new variables (this is what ext_tel does).  For a higher-dimensional match, the new variables come with their boundaries in n-dimensional cubes. *)
                        let newctx, newenv, newvars =
                          ext_tel ctx env xs argtys user_args.value efc in
                        let perm = Tbwd.id_perm in
                        let status =
                          make_match_status status ctm dim branches efc None perm constr.value in
                        (* To get the type at which to typecheck the body of the branch, we have to evaluate the general dependent motive at the indices of this constructor, its boundaries, and itself.  First we compute the indices. *)
                        let index_vals =
                          Vec.mmap (fun [ ixtm ] -> eval_with_boundary newenv ixtm) [ index_terms ]
                        in
                        let bmotive = Vec.fold_left apply_singletons emotive index_vals in
                        (* Now we compute the constructor and its boundaries. *)
                        let constr_vals =
                          CubeOf.build dim
                            {
                              build =
                                (fun fa ->
                                  Value.Constr
                                    ( constr.value,
                                      dom_sface fa,
                                      List.map (CubeOf.subcube fa) newvars ));
                            } in
                        let bmotive = apply_singletons bmotive constr_vals in
                        (* Finally, we recurse into the "body" of the branch. *)
                        branches
                        |> Constr.Map.add constr.value
                             (Term.Branch (efc, perm, check status newctx body bmotive)))
                  Constr.Map.empty brs in
              (* Coverage check *)
              Constr.Map.iter
                (fun c _ ->
                  if not (Constr.Map.mem c branches) then fatal (Missing_constructor_in_match c))
                constrs;
              (* Now we compute the output type by evaluating the dependent motive at the match term's indices, boundary, and itself. *)
              let result =
                Vec.fold_left
                  (fun fn xs ->
                    match xs with
                    | Value.App (Arg xs, _) ->
                        snd
                          (MC.miterM
                             {
                               it = (fun _ [ x ] fn -> ((), apply_term fn (CubeOf.singleton x.tm)));
                             }
                             [ xs ] fn)
                    | App (Field _, _) -> fatal (Anomaly "field is not an index"))
                  emotive tmindices in
              let result =
                snd
                  (MT.miterM
                     { it = (fun _ [ x ] fn -> ((), apply_term fn (CubeOf.singleton x.tm))) }
                     [ inst_args ] result) in
              let result = apply_term result (CubeOf.singleton (Ctx.eval_term ctx ctm)) in
              (Match { tm = ctm; dim; branches; energy }, result)
          | _ -> fatal (Anomaly "uvarty_params not uninst")))
  | _ -> fatal (Matching_on_nondatatype (PUninst (ctx, uvarty)))

(* Check a match against a well-behaved variable, which can only appear in a case tree and refines not only the goal but the context (possibly with permutation). *)
and check_var_match :
    type a b s.
    (b, s) status ->
    (a, b) Ctx.t ->
    level ->
    b Term.index ->
    kinetic value ->
    a branch list ->
    kinetic value ->
    s nonkinetic ->
    (b, s) term =
 fun status ctx level index varty brs motive energy ->
  (* We look up the type of the discriminee, which must be a datatype, without any degeneracy applied outside, and at the same dimension as its instantiation. *)
  let (Fullinst (uvarty, inst_args)) = full_inst varty "check_var_match" in
  match uvarty with
  | Neu
      {
        head = Const { name; _ };
        args = varty_args;
        alignment = Lawful (Data { dim; indices = Filled var_indices; constrs });
      } -> (
      match D.compare dim (TubeOf.inst inst_args) with
      | Neq -> fatal (Dimension_mismatch ("var match", dim, TubeOf.inst inst_args))
      | Eq ->
          let params, _ = Vec.take_bwd (Vec.length var_indices) varty_args in
          (* In our simple version of pattern-matching against a variable, the "indices" and all their boundaries must be distinct free variables with no degeneracies, so that in the branch for each constructor they can be set equal to the computed value of that index for that constructor (and in which they cannot occur).  This is a special case of the unification algorithm described in CDP "Pattern-matching without K" where the only allowed rule is "Solution".  Later we can try to enhance it with their full unification algorithm, at least for non-higher datatypes.  In addition, for a higher-dimensional match, the instantiation arguments must also all be distinct variables, distinct from the indices.  If any of these conditions fail, we raise an exception, catch it, emit a hint, and revert to doing a non-dependent match. *)
          let seen = Hashtbl.create 10 in
          let is_fresh x =
            match x.tm with
            | Uninst (Neu { head = Var { level; deg }; args = Emp; alignment = True }, _) ->
                if Option.is_none (is_id_deg deg) then
                  fatal (Matching_wont_refine ("index variable has degeneracy", PNormal (ctx, x)));
                if Hashtbl.mem seen level then
                  fatal (Matching_wont_refine ("duplicate variable in indices", PNormal (ctx, x)));
                Hashtbl.add seen level ();
                level
            | _ -> fatal (Matching_wont_refine ("index is not a free variable", PNormal (ctx, x)))
          in
          Reporter.try_with ~fatal:(fun d ->
              match d.message with
              | Matching_wont_refine (str, x) ->
                  emit (Matching_wont_refine (str, x));
                  check_nondep_match status ctx (Term.Var index) varty brs None motive energy
              | No_such_level x ->
                  emit (Matching_wont_refine ("index variable occurs in parameter", x));
                  check_nondep_match status ctx (Term.Var index) varty brs None motive energy
              | _ -> fatal_diagnostic d)
          @@ fun () ->
          let index_vars =
            Vec.mmap
              (fun [ tm ] -> CubeOf.mmap { map = (fun _ [ x ] -> is_fresh x) } [ tm ])
              [ var_indices ] in
          let inst_vars = TubeOf.mmap { map = (fun _ [ x ] -> is_fresh x) } [ inst_args ] in
          let constr_vars = TubeOf.plus_cube inst_vars (CubeOf.singleton level) in
          (* Now we also check that none of these free variables occur in the parameters.  We do this by altering the context to replace all these level variables with unknowns and doing a readback of the parameters into that context.  If the readback encounters one of the missing level variables, it fails with No_such_level; above we catch that, emit a hint, and fall back to matching against a term. *)
          (* TODO: This doesn't seem to be catching things it should, like attempted proofs of Axiom K; they go on and get caught by No_permutation instead. *)
          let ctx_noindices = Ctx.forget_levels ctx (Hashtbl.mem seen) in
          Bwd.iter
            (function
              | Value.App (Field _, _) -> ()
              | App (Arg args, _) ->
                  CubeOf.miter
                    { it = (fun _ [ x ] -> discard (readback_nf ctx_noindices x)) }
                    [ args ])
            params;
          (* If all of those checks succeed, we continue on the path of a variable match.  But note that this call is still inside the try_with, so it can still fail and revert back to a non-dependent term match. *)
          (* We now iterate through the branches supplied by the user, typechecking them and inserting them in the match tree. *)
          let branches =
            List.fold_left
              (fun branches (Branch (constr, xs, user_args, body)) ->
                if Constr.Map.mem constr.value branches then
                  fatal ?loc:constr.loc (Duplicate_constructor_in_match constr.value);
                (* Get the argument types and index terms for the constructor of this branch. *)
                let (Dataconstr { env; args = argtys; indices = index_terms }) =
                  Reporter.with_loc constr.loc @@ fun () ->
                  Constr.Map.find_opt constr.value constrs
                  <|> No_such_constructor_in_match (PConstant name, constr.value) in
                let (Snocs efc) = Tbwd.snocs (Telescope.length argtys) in
                (* The user needs to have supplied the right number of pattern variable arguments to the constructor. *)
                match Fwn.compare (Fwn.bplus_right user_args.value) (Telescope.length argtys) with
                | Neq ->
                    fatal ?loc:user_args.loc
                      (Wrong_number_of_arguments_to_pattern
                         ( constr.value,
                           Fwn.to_int (Fwn.bplus_right user_args.value)
                           - Fwn.to_int (Telescope.length argtys) ))
                | Eq -> (
                    (* Create new level variables for the pattern variables to which the constructor is applied, and add corresponding index variables to the context.  The types of those variables are specified in the telescope argtys, and have to be evaluated at the closure environment 'env' and the previous new variables (this is what ext_tel does).  For a higher-dimensional match, the new variables come with their boundaries in n-dimensional cubes. *)
                    let newctx, newenv, newvars = ext_tel ctx env xs argtys user_args.value efc in
                    (* Evaluate the "index_terms" at the new pattern variables, obtaining what the indices should be for the new term that replaces the match variable in the match body. *)
                    let index_vals =
                      Vec.mmap
                        (fun [ ixtm ] ->
                          CubeOf.build dim
                            { build = (fun fa -> eval_term (Act (newenv, op_of_sface fa)) ixtm) })
                        [ index_terms ] in
                    (* Assemble a term consisting of the constructor applied to the new variables, along with its boundary, and their types.  To compute their types, we have to extract the datatype applied to its parameters only, pass to boundaries if necessary, and then re-apply it to the new indices. *)
                    let argtbl = Hashtbl.create 10 in
                    let constr_nfs =
                      CubeOf.build dim
                        {
                          build =
                            (fun fa ->
                              let k = dom_sface fa in
                              let tm =
                                Value.Constr
                                  (constr.value, dom_sface fa, List.map (CubeOf.subcube fa) newvars)
                              in
                              let ty =
                                inst
                                  (Vec.fold_left
                                     (fun f a -> apply_term f (CubeOf.subcube fa a))
                                     (Bwd.fold_left
                                        (fun f -> function
                                          | Value.App (Arg arg, _) -> (
                                              match D.compare (CubeOf.dim arg) dim with
                                              | Eq ->
                                                  apply_term f
                                                    (val_of_norm_cube (CubeOf.subcube fa arg))
                                              | Neq ->
                                                  fatal
                                                    (Dimension_mismatch
                                                       ("check match", CubeOf.dim arg, dim)))
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
                    let (Fullinst (ucty, _)) = full_inst constr_nf.ty "check_var_match (inner)" in
                    match ucty with
                    | Neu
                        {
                          alignment = Lawful (Data { dim = constrdim; indices = Filled indices; _ });
                          _;
                        } -> (
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
                                fatal
                                  (Matching_wont_refine
                                     ("no consistent permutation of context", PUnit))
                            | Bind_some { checked_perm; oldctx; newctx } ->
                                (* We readback the index and instantiation values into this new context and discard the result, catching No_such_level to turn it into a user Error.  This has the effect of doing an occurs-check that none of the index variables occur in any of the index values.  This is a bit less general than the CDP Solution rule, which (when applied one variable at a time) prohibits only cycles of occurrence.  Note that this exception is still caught by go_check_match, above, causing a fallback to term matching. *)
                                ( Reporter.try_with ~fatal:(fun d ->
                                      match d.message with
                                      | No_such_level x ->
                                          fatal
                                            (Matching_wont_refine
                                               ( "free index variable occurs in inferred index value",
                                                 x ))
                                      | _ -> fatal_diagnostic d)
                                @@ fun () ->
                                  Hashtbl.iter (fun _ v -> discard (readback_nf oldctx v)) new_vals
                                );
                                (* The type of the match must be specialized in the branches by substituting different constructors for the match variable, as well as the index values for the index variables, and lower-dimensional versions of each constructor for the instantiation variables.  Thus, we readback-eval this type into the new context, to obtain the type at which the branch body will be checked. *)
                                let newty = Ctx.eval_term newctx (readback_val oldctx motive) in
                                (* Now we have to modify the "status" data by readback-eval on the arguments and adding a hypothesized current branch to the match.  *)
                                let eval_readback_args x =
                                  let tm = Ctx.eval_term newctx (readback_nf oldctx x) in
                                  let ty = Ctx.eval_term newctx (readback_val oldctx x.ty) in
                                  { tm; ty } in
                                let perm = checked_perm in
                                let status =
                                  make_match_status status (Term.Var index) dim branches efc
                                    (Some eval_readback_args) perm constr.value in
                                (* Finally, we typecheck the "body" of the branch. *)
                                branches
                                |> Constr.Map.add constr.value
                                     (Term.Branch (efc, perm, check status newctx body newty))))
                    | _ -> fatal (Anomaly "created datatype is not canonical?")))
              Constr.Map.empty brs in
          (* Coverage check *)
          Constr.Map.iter
            (fun c _ ->
              if not (Constr.Map.mem c branches) then fatal (Missing_constructor_in_match c))
            constrs;
          Match { tm = Term.Var index; dim; branches; energy })
  | _ -> fatal (Matching_on_nondatatype (PUninst (ctx, uvarty)))

and make_match_status :
    type a b ab c n s.
    (a, s) status ->
    (a, kinetic) term ->
    n D.t ->
    (a, n, s) Term.branch Constr.Map.t ->
    (a, b, n, ab) Tbwd.snocs ->
    (normal -> normal) option ->
    (c, ab) Tbwd.permute ->
    Constr.t ->
    (c, s) status =
 fun status newtm dim branches efc eval_readback perm constr ->
  match status with
  | Kinetic -> Kinetic
  | Chemical -> Chemical
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
        hyp (Term.Match { tm = newtm; dim; branches; energy = Potential }) in
      Potential (c, args, hyp)

and check_data :
    type a b i bi.
    (b, potential) status ->
    (a, b) Ctx.t ->
    kinetic value ->
    i Fwn.t ->
    (b, i) Term.dataconstr Constr.Map.t ->
    (Constr.t * a Raw.dataconstr located) list ->
    (b, potential) term =
 fun status ctx ty num_indices checked_constrs raw_constrs ->
  match (raw_constrs, status) with
  | [], _ -> Canonical (Data (num_indices, checked_constrs))
  | ( (c, { value = Dataconstr (args, output); loc }) :: raw_constrs,
      Potential (head, current_apps, hyp) ) -> (
      with_loc loc @@ fun () ->
      (* Temporarily bind the current constant to the up-until-now value. *)
      Global.run_with_definition head
        (Defined (hyp (Term.Canonical (Data (num_indices, checked_constrs)))))
      @@ fun () ->
      match (Constr.Map.find_opt c checked_constrs, output) with
      | Some _, _ -> fatal (Duplicate_constructor_in_data c)
      | None, Some output -> (
          let (Checked_tel (args, newctx)) = check_tel ctx args in
          let coutput = check Kinetic newctx output (universe D.zero) in
          match Ctx.eval_term newctx coutput with
          | Uninst (Neu { head = Const { name = out_head; ins }; args = out_apps; alignment = _ }, _)
            ->
              if head = out_head && Option.is_some (is_id_ins ins) then
                let (Wrap indices) =
                  get_indices newctx c (Bwd.to_list current_apps) (Bwd.to_list out_apps) output.loc
                in
                match Fwn.compare (Vec.length indices) num_indices with
                | Eq ->
                    check_data status ctx ty num_indices
                      (checked_constrs |> Constr.Map.add c (Term.Dataconstr { args; indices }))
                      raw_constrs
                | _ ->
                    (* I think this shouldn't ever happen, no matter what the user writes, since we know at this point that the output is a full application of the correct constant, so it must have the right number of arguments. *)
                    fatal (Anomaly "length of indices mismatch")
              else fatal ?loc:output.loc (Invalid_constructor_type c)
          | _ -> fatal ?loc:output.loc (Invalid_constructor_type c))
      | None, None -> (
          match num_indices with
          | Zero ->
              let (Checked_tel (args, _)) = check_tel ctx args in
              check_data status ctx ty Fwn.zero
                (checked_constrs |> Constr.Map.add c (Term.Dataconstr { args; indices = [] }))
                raw_constrs
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
    n D.t ->
    (D.zero, n, n, normal) TubeOf.t ->
    (Field.t, ((b, n) snoc, kinetic) term) Abwd.t ->
    ((n, Ctx.Binding.t) CubeOf.t -> c) ->
    c =
 fun (Potential (name, args, hyp)) eta ctx dim tyargs checked_fields cont ->
  (* We can always create a constant with the (0,0,0) insertion, even if its dimension is actually higher. *)
  let head = Value.Const { name; ins = zero_ins D.zero } in
  let alignment =
    Lawful (Codata { eta; env = Ctx.env ctx; ins = zero_ins dim; fields = checked_fields }) in
  let prev_ety =
    Uninst (Neu { head; args; alignment }, Lazy.from_val (inst (universe dim) tyargs)) in
  let _, domvars =
    dom_vars (Ctx.length ctx)
      (TubeOf.plus_cube
         (TubeOf.mmap { map = (fun _ [ nf ] -> nf.tm) } [ tyargs ])
         (CubeOf.singleton prev_ety)) in
  Global.run_with_definition name
    (Defined (hyp (Term.Canonical (Codata (eta, dim, checked_fields)))))
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
  | [] -> Canonical (Codata (Noeta, dim, checked_fields))
  | (fld, (x, rty)) :: raw_fields ->
      with_codata_so_far status Noeta ctx dim tyargs checked_fields @@ fun domvars ->
      let newctx = Ctx.cube_vis ctx x domvars in
      let cty = check Kinetic newctx rty (universe D.zero) in
      let checked_fields = Snoc (checked_fields, (fld, cty)) in
      check_codata status ctx tyargs checked_fields raw_fields

and check_record :
    type a f1 f2 f af d acd b n.
    (b, potential) status ->
    n D.t ->
    (a, b) Ctx.t ->
    (D.zero, n, n, normal) TubeOf.t ->
    (N.zero, n, string option, f1) NICubeOf.t ->
    (Field.t * string, f2) Bwv.t ->
    (f1, f2, f) N.plus ->
    (a, f, af) N.plus ->
    (Field.t, ((b, n) snoc, kinetic) term) Abwd.t ->
    (af, d, acd) Raw.tel ->
    (b, potential) term =
 fun status dim ctx tyargs vars ctx_fields fplus af checked_fields raw_fields ->
  match raw_fields with
  | Emp -> Term.Canonical (Codata (Eta, dim, checked_fields))
  | Ext (None, _, _) -> fatal (Anomaly "unnamed field in check_record")
  | Ext (Some name, rty, raw_fields) ->
      with_codata_so_far status Eta ctx dim tyargs checked_fields @@ fun domvars ->
      let newctx = Ctx.vis_fields ctx vars domvars ctx_fields fplus af in
      let cty = check Kinetic newctx rty (universe D.zero) in
      let fld = Field.intern name in
      let checked_fields = Snoc (checked_fields, (fld, cty)) in
      let ctx_fields = Bwv.Snoc (ctx_fields, (fld, name)) in
      check_record status dim ctx tyargs vars ctx_fields (Suc fplus) (Suc af) checked_fields
        raw_fields

and check_struct :
    type a b c s m n.
    (b, s) status ->
    s nonchemical ->
    s eta ->
    (a, b) Ctx.t ->
    (Field.t option, a check located) Abwd.t ->
    kinetic value ->
    m D.t ->
    (Field.t, ((c, n) snoc, kinetic) term) Abwd.t ->
    (b, s) term =
 fun status energy eta ctx tms ty dim fields ->
  (* The type of each record field, at which we check the corresponding field supplied in the struct, is the type associated to that field name in general, evaluated at the supplied parameters and at "the term itself".  We don't have the whole term available while typechecking, of course, but we can build a version of it that contains all the previously typechecked fields, which is all we need for a well-typed record.  So we iterate through the fields (in the order specified in the *type*, since that determines the dependencies) while also accumulating the previously typechecked and evaluated fields.  At the end, we throw away the evaluated fields (although as usual, that seems wasteful). *)
  let tms, ctms =
    check_fields status energy eta ctx ty dim
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
  Term.Struct { eta; dim; fields; energy }

and check_fields :
    type a b s n.
    (b, s) status ->
    s nonchemical ->
    s eta ->
    (a, b) Ctx.t ->
    kinetic value ->
    n D.t ->
    Field.t list ->
    (Field.t option, a check located) Abwd.t ->
    (Field.t, s evaluation Lazy.t * [ `Labeled | `Unlabeled ]) Abwd.t ->
    (Field.t, (b, s) term * [ `Labeled | `Unlabeled ]) Abwd.t ->
    (Field.t option, a check located) Abwd.t
    * (Field.t, (b, s) term * [ `Labeled | `Unlabeled ]) Abwd.t =
 fun status energy eta ctx ty dim fields tms etms ctms ->
  (* The insertion on a struct being checked is the identity, but it stores the substitution dimension of the type being checked against.  If this is a higher-dimensional record (e.g. Gel), there could be a nontrivial right dimension being trivially inserted, but that will get added automatically by an appropriate symmetry action if it happens. *)
  match (fields, energy, status) with
  | [], _, _ -> (tms, ctms)
  | fld :: fields, Potential, Potential (name, args, hyp) ->
      let str = Value.Struct (etms, ins_zero dim, Potential) in
      (* Temporarily bind the current constant to the up-until-now value. *)
      Global.run_with_definition name
        (Defined (hyp (Term.Struct { eta; dim; fields = ctms; energy = Potential })))
      @@ fun () ->
      (* The insertion on the *constant* being checked, by contrast, is always zero, since the constant is not nontrivially substituted at all yet. *)
      let head = Value.Const { name; ins = ins_zero D.zero } in
      let prev_etm = Uninst (Neu { head; args; alignment = Chaotic str }, Lazy.from_val ty) in
      check_field status energy eta ctx ty dim fld fields prev_etm tms etms ctms
  | fld :: fields, Kinetic, Kinetic ->
      let str = Value.Struct (etms, ins_zero dim, Kinetic) in
      check_field Kinetic Kinetic eta ctx ty dim fld fields str tms etms ctms

and check_field :
    type a b s t n.
    (b, s) status ->
    s nonchemical ->
    s eta ->
    (a, b) Ctx.t ->
    kinetic value ->
    n D.t ->
    Field.t ->
    Field.t list ->
    kinetic value ->
    (Field.t option, a check located) Abwd.t ->
    (Field.t, s evaluation Lazy.t * [ `Labeled | `Unlabeled ]) Abwd.t ->
    (Field.t, (b, s) term * [ `Labeled | `Unlabeled ]) Abwd.t ->
    (Field.t option, a check located) Abwd.t
    * (Field.t, (b, s) term * [ `Labeled | `Unlabeled ]) Abwd.t =
 fun status energy eta ctx ty dim fld fields prev_etm tms etms ctms ->
  (* Once again we need a helper function with a declared polymorphic type in order to munge the status.  *)
  let mkstatus :
      type b s.
      (b, s) status ->
      s eta ->
      (Field.t, (b, s) term * [ `Labeled | `Unlabeled ]) Abwd.t ->
      [ `Labeled | `Unlabeled ] ->
      (b, s) status =
   fun status eta ctms lbl ->
    match status with
    | Kinetic -> Kinetic
    | Chemical -> Chemical
    | Potential (c, args, hyp) ->
        let args = Snoc (args, App (Field fld, ins_zero D.zero)) in
        let hyp tm =
          hyp (Term.Struct { eta; dim; fields = Snoc (ctms, (fld, (tm, lbl))); energy = Potential })
        in
        Potential (c, args, hyp) in
  let ety = tyof_field prev_etm ty fld in
  match Abwd.find_opt (Some fld) tms with
  | Some tm ->
      let field_status = mkstatus status eta ctms `Labeled in
      let ctm = check field_status ctx tm ety in
      let etms = Abwd.add fld (lazy (Ctx.eval ctx ctm), `Labeled) etms in
      let ctms = Snoc (ctms, (fld, (ctm, `Labeled))) in
      check_fields status energy eta ctx ty dim fields tms etms ctms
  | None -> (
      let field_status = mkstatus status eta ctms `Unlabeled in
      match Abwd.find_opt_and_update_key None (Some fld) tms with
      | Some (tm, tms) ->
          let ctm = check field_status ctx tm ety in
          let etms = Abwd.add fld (lazy (Ctx.eval ctx ctm), `Unlabeled) etms in
          let ctms = Snoc (ctms, (fld, (ctm, `Unlabeled))) in
          check_fields status energy eta ctx ty dim fields tms etms ctms
      | None -> fatal (Missing_field_in_tuple fld))

and synth :
    type a b s. (b, s) status -> (a, b) Ctx.t -> a synth located -> (b, s) term * kinetic value =
 fun status ctx tm ->
  with_loc tm.loc @@ fun () ->
  match tm.value with
  | Var i -> (
      match Ctx.lookup ctx i with
      | `Var (_, x, v) -> (realize status (Term.Var v), x.ty)
      | `Field (lvl, x, fld) -> (
          match Ctx.find_level ctx lvl with
          | Some v -> (realize status (Term.Field (Var v, fld)), tyof_field x.tm x.ty fld)
          | None -> fatal (Anomaly "level not found in field view")))
  | Const name ->
      let ty, _ = Global.find_opt name <|> Undefined_constant (PConstant name) in
      (realize status (Const name), eval_term (Emp D.zero) ty)
  | Field (tm, fld) ->
      let stm, sty = synth Kinetic ctx tm in
      (* To take a field of something, the type of the something must be a record-type that contains such a field, possibly substituted to a higher dimension and instantiated. *)
      let etm = Ctx.eval_term ctx stm in
      let fld, newty = tyof_field_withname ~severity:Asai.Diagnostic.Error etm sty fld in
      (realize status (Field (stm, fld)), newty)
  | UU -> (realize status (Term.UU D.zero), universe D.zero)
  | Pi (x, dom, cod) ->
      (* User-level pi-types are always dimension zero, so the domain must be a zero-dimensional type. *)
      let cdom = check Kinetic ctx dom (universe D.zero) in
      let edom = Ctx.eval_term ctx cdom in
      let ccod = check Kinetic (Ctx.ext ctx x edom) cod (universe D.zero) in
      (realize status (pi x cdom ccod), universe D.zero)
  | App _ ->
      (* If there's at least one application, we slurp up all the applications, synthesize a type for the function, and then pass off to synth_apps to iterate through all the arguments. *)
      let fn, locs, args = spine tm in
      let sfn, sty = synth Kinetic ctx fn in
      let stm, sty = synth_apps ctx { value = sfn; loc = fn.loc } sty locs args in
      (realize status stm, sty)
  | Act (str, fa, { value = Synth x; loc }) ->
      let x = { value = x; loc } in
      let sx, ety =
        if locking fa then Global.run_locked (fun () -> synth Kinetic (Ctx.lock ctx) x)
        else synth Kinetic ctx x in
      let ex = Ctx.eval_term ctx sx in
      ( realize status (Term.Act (sx, fa)),
        with_loc x.loc @@ fun () ->
        act_ty ex ety fa ~err:(Low_dimensional_argument_of_degeneracy (str, cod_deg fa)) )
  | Act _ -> fatal (Nonsynthesizing "argument of degeneracy")
  | Asc (tm, ty) ->
      let cty = check Kinetic ctx ty (universe D.zero) in
      let ety = Ctx.eval_term ctx cty in
      let ctm = check status ctx tm ety in
      (ctm, ety)
  | Let (x, v, { value = Synth body; loc }) -> (
      match status with
      | Kinetic ->
          let sv, sty = synth Kinetic ctx v in
          let ev = Ctx.eval_term ctx sv in
          let sbody, bodyty =
            synth Kinetic (Ctx.ext_let ctx x { tm = ev; ty = sty }) { value = body; loc } in
          (* In this case, the synthesized type of the body is also correct for the whole let-expression, because it was synthesized in a context where the variable is bound not just to its type but to its value, so it doesn't include any extra level variables (i.e. it can be silently "strengthened"). *)
          (Let (x, Kinetic, sv, sbody), bodyty)
      | Potential (c, args, hyp) -> (
          let sv, sty = synth Chemical ctx v in
          let status = Potential (c, args, fun body -> hyp (Term.Let (x, Potential, sv, body))) in
          match Ctx.eval ctx sv with
          | Val (_, _) -> .
          | Realize (ev, Chemical) ->
              let sbody, bodyty =
                synth status (Ctx.ext_let ctx x { tm = ev; ty = sty }) { value = body; loc } in
              (* In this case, the synthesized type can again be silently strengthened. *)
              (Let (x, Potential, sv, sbody), bodyty)
          | Unrealized Chemical ->
              (* However, in this case, we don't have a value to bind the variable to, so the best we can do is make it a free variable.  But then the synthesized type of the body could involve that variable and thus not be valid for the entire let.  So we check that by reading it back in the *original* context and trapping No_such_level to give a more appropriate message. *)
              let newctx = Ctx.ext ctx x sty in
              let sbody, bodyty = synth status newctx { value = body; loc } in
              Reporter.try_with ~fatal:(fun d ->
                  match d.message with
                  | No_such_level _ ->
                      fatal
                        (Invalid_synthesized_type ("body of let-binding", PVal (newctx, bodyty)))
                  | _ -> fatal_diagnostic d)
              @@ fun () ->
              discard (readback_val ctx bodyty);
              (Term.Let (x, Potential, sv, sbody), bodyty))
      | Chemical -> (
          let sv, sty = synth Chemical ctx v in
          match Ctx.eval ctx sv with
          | Val (_, _) -> .
          | Realize (ev, Chemical) ->
              let sbody, bodyty =
                synth Chemical (Ctx.ext_let ctx x { tm = ev; ty = sty }) { value = body; loc } in
              (Let (x, Chemical, sv, sbody), bodyty)
          | Unrealized Chemical ->
              let newctx = Ctx.ext ctx x sty in
              let sbody, bodyty = synth Chemical newctx { value = body; loc } in
              Reporter.try_with ~fatal:(fun d ->
                  match d.message with
                  | No_such_level _ ->
                      fatal
                        (Invalid_synthesized_type ("body of let-binding", PVal (newctx, bodyty)))
                  | _ -> fatal_diagnostic d)
              @@ fun () ->
              discard (readback_val ctx bodyty);
              (Term.Let (x, Chemical, sv, sbody), bodyty)))
  | Let _ -> fatal (Nonsynthesizing "body of synthesizing let")
  | Match (tm, `Explicit motive, brs) -> (
      match status with
      | Potential _ -> synth_dep_match status ctx tm brs motive Potential
      | Chemical -> synth_dep_match status ctx tm brs motive Chemical
      | Kinetic -> fatal (Invalid_outside_case_tree "match"))
  | Match (tm, `Implicit, brs) -> (
      match status with
      | Potential _ ->
          emit (Matching_wont_refine ("match in synthesizing position", PUnit));
          synth_nondep_match status ctx tm brs None Potential
      | Chemical ->
          emit (Matching_wont_refine ("match in synthesizing position", PUnit));
          synth_nondep_match status ctx tm brs None Chemical
      | Kinetic -> fatal (Invalid_outside_case_tree "match"))
  | Match (tm, `Nondep i, brs) -> (
      match status with
      | Potential _ -> synth_nondep_match status ctx tm brs (Some i) Potential
      | Chemical -> synth_nondep_match status ctx tm brs (Some i) Chemical
      | Kinetic -> fatal (Invalid_outside_case_tree "match"))

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
      match D.compare (TubeOf.inst tyargs) (CubeOf.dim doms) with
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
              [ doms ] (Cons (Cons Nil)) (sfn.loc, locs, args) in
          (* Evaluate cod at these evaluated arguments and instantiate it at the appropriate values of tyargs. *)
          let output = tyof_app cods tyargs eargs in
          ({ value = Term.App (sfn.value, cargs); loc = newloc }, output, rlocs, rest))
  (* We can also "apply" a higher-dimensional *type*, leading to a (further) instantiation of it.  Here the number of arguments must exactly match *some* integral instantiation. *)
  | UU n -> (
      (* Ensure that the universe is (fully) instantiated at the right dimension. *)
      match D.compare (TubeOf.inst tyargs) n with
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
                        Hashtbl.add eargtbl (SFace_of fa) ntm;
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
           (c, List.length tms - Fwn.to_int (Telescope.length tys)))

(* Given a context and a raw telescope, we can check it to produce a checked telescope and also a new context extended by that telescope. *)
and check_tel : type a b c ac. (a, b) Ctx.t -> (a, c, ac) Raw.tel -> (ac, b) checked_tel =
 fun ctx tel ->
  match tel with
  | Emp -> Checked_tel (Emp, ctx)
  | Ext (x, ty, tys) ->
      let cty = check Kinetic ctx ty (universe D.zero) in
      let ety = Ctx.eval_term ctx cty in
      let _, newnfs = dom_vars (Ctx.length ctx) (CubeOf.singleton ety) in
      let ctx = Ctx.cube_vis ctx x newnfs in
      let (Checked_tel (ctys, ctx)) = check_tel ctx tys in
      Checked_tel (Ext (x, cty, ctys), ctx)
