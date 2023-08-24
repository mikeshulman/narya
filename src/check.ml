open Raw
open Value
open Term
open Dim
open Act
open Norm
open Equal
open Monad.Ops (Monad.Maybe)

(* Look through a specified number of lambdas to find an inner body. *)
let rec lambdas : type a b ab. (a, b, ab) N.plus -> a check -> ab check option =
 fun ab tm ->
  match (ab, tm) with
  | Zero, _ -> Some tm
  | Suc _, Lam body -> lambdas (N.suc_plus'' ab) body
  (* Not enough lambdas.  TODO: We could eta-expand in this case, as long as we've picked up at least one lambda. *)
  | _ ->
      Printf.printf "Not enough lambdas";
      None

(* Slurp up an entire application spine *)
let spine : type a. a synth -> a synth * a check list =
 fun tm ->
  let rec spine tm args =
    match tm with
    | Raw.App (fn, arg) -> spine fn (arg :: args)
    | _ -> (tm, args) in
  spine tm []

let rec check : type a. a Ctx.t -> a check -> value -> a term option =
 fun ctx tm ty ->
  match tm with
  | Synth stm ->
      let* sval, sty = synth ctx stm in
      let* () = equal_val ctx sty ty in
      return sval
  | Lam _ ->
      (* We don't pick up the body here, only the presence of at least one lambda.  We'll pick up an appropriate number of lambdas in check_lam.  If the "type" is not a type or not fully instantiated here, that's a user error, not a bug. *)
      let* (Fullinst (ty, args)) = full_inst_opt ty in
      check_lam ctx tm ty args

and check_lam :
    type a m n mn f. a Ctx.t -> a check -> uninst -> (m, n, mn, value) TubeOf.t -> a term option =
 fun ctx tm ty args ->
  match ty with
  | Pi (doms, cods) -> (
      let m = CubeOf.dim doms in
      match (compare (TubeOf.uninst args) D.zero, compare (TubeOf.inst args) m) with
      | Neq, _ | _, Neq ->
          Printf.printf "Dimension mismatch in checking lambda";
          None
      | Eq, Eq ->
          let Eq = D.plus_uniq (TubeOf.plus args) (D.zero_plus m) in
          (* Slurp up the right number of lambdas for the dimension of the pi-type, and pick up the body inside them. *)
          let (Faces dom_faces) = count_faces (CubeOf.dim doms) in
          let (Plus af) = N.plus (faces_out dom_faces) in
          let* body = lambdas af tm in
          (* Extend the context by one variable for each type in doms, instantiated at the appropriate previous ones. *)
          let ctx, newargs = Ctx.dom_vars ctx dom_faces af doms in
          (* Apply and instantiate the codomain to those arguments to get a type to check the body at. *)
          let out_args =
            TubeOf.mmap
              {
                map =
                  (fun fa [ afn ] ->
                    apply afn
                      (CubeOf.build (dom_tface fa)
                         {
                           build =
                             (fun fc -> CubeOf.find newargs (comp_sface (sface_of_tface fa) fc));
                         }));
              }
              [ args ] in
          let output = inst (apply_binder (BindCube.find cods (id_sface m)) newargs) out_args in
          let* cbody = check ctx body output in
          return (Term.Lam (dom_faces, af, cbody)))
  (* We can't check a lambda-abstraction against anything except a pi-type. *)
  | _ ->
      Printf.printf "Can't check lambda against non-pi-type";
      None

and synth : type a. a Ctx.t -> a synth -> (a term * value) option =
 fun ctx tm ->
  match tm with
  | Var v -> return (Term.Var v, Bwv.nth v ctx)
  | Const name -> return (Const name, eval (Emp D.zero) (Hashtbl.find Global.types name))
  | Field (tm, fld) ->
      let* stm, sty = synth ctx tm in
      (* To take a field of something, the type of the something must be a record-type that contains such a field, possibly substituted to a higher dimension and instantiated. *)
      let etm = Ctx.eval ctx stm in
      let* newty = tyof_field_opt etm sty fld in
      return (Field (stm, fld), newty)
  | UU -> return (Term.UU, Uninst (UU D.zero))
  | Pi (dom, cod) ->
      (* User-level pi-types are always dimension zero, so the domain must be a zero-dimensional type. *)
      let* cdom = check ctx dom (Uninst (UU D.zero)) in
      let edom = Ctx.eval ctx cdom in
      let* ccod = check (Snoc (ctx, edom)) cod (Uninst (UU D.zero)) in
      return (Term.Pi (cdom, ccod), Uninst (UU D.zero))
  | App _ ->
      (* If there's at least one application, we slurp up all the applications, synthesize a type for the function, and then pass off to synth_apps to iterate through all the arguments. *)
      let fn, args = spine tm in
      let* sfn, sty = synth ctx fn in
      synth_apps ctx sfn sty args
  | Id (a, x, y) ->
      (* This is just an abbreviation. *)
      synth ctx (App (App (Refl a, x), y))
  | Refl x ->
      let* sx, ety = synth ctx x in
      let ex = Ctx.eval ctx sx in
      return (Refl sx, act_ty ex ety refl)
  | Sym x -> (
      let* sx, ety = synth ctx x in
      let ex = Ctx.eval ctx sx in
      try
        let symty = act_ty ex ety sym in
        return (Sym sx, symty)
      with Invalid_uninst_action ->
        Printf.printf "Can't symmetrize something of too low dimension";
        None)
  | Asc (tm, ty) ->
      let* cty = check ctx ty (Uninst (UU D.zero)) in
      let ety = Ctx.eval ctx cty in
      let* ctm = check ctx tm ety in
      return (ctm, ety)

(* Given a synthesized function and its type, and a list of arguments, check the arguments in appropriately-sized groups. *)
and synth_apps : type a. a Ctx.t -> a term -> value -> a check list -> (a term * value) option =
 fun ctx sfn sty args ->
  (* Failure of full_inst here is really a bug, not a user error: the user can try to check something against an abstraction as if it were a type, but our synthesis functions should never synthesize (say) a lambda-abstraction as if it were a type. *)
  let (Fullinst (fnty, tyargs)) = full_inst sty "synth_apps" in
  let* afn, aty, aargs = synth_app ctx sfn fnty tyargs args in
  (* synth_app fails if there aren't enough arguments.  If it used up all the arguments, we're done; otherwise we continue with the rest of the arguments. *)
  match aargs with
  | [] -> return (afn, aty)
  | _ :: _ -> synth_apps ctx afn aty aargs

and synth_app :
    type a n f.
    a Ctx.t ->
    a term ->
    uninst ->
    (D.zero, n, n, value) TubeOf.t ->
    a check list ->
    (a term * value * a check list) option =
 fun ctx sfn fnty tyargs args ->
  let module M =
    Monad.StateT
      (Monad.Maybe)
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
      | Neq ->
          Printf.printf "Dimension mismatch when synthesizing applied function";
          None
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
                      | [] -> M.stateless None
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
                    Hashtbl.add eargtbl (SFace_of fa) tm;
                    return (ctm @: [ tm ]));
              }
              [ doms ] (Cons (Cons Nil)) args in
          (* Evaluate cod at these evaluated arguments, and instantiate it at the appropriate values of tyargs, as with similar code in other places. *)
          let out_args =
            TubeOf.mmap
              {
                map =
                  (fun fa [ afn ] ->
                    apply afn
                      (CubeOf.build (dom_tface fa)
                         {
                           build = (fun fc -> CubeOf.find eargs (comp_sface (sface_of_tface fa) fc));
                         }));
              }
              [ tyargs ] in
          let output =
            inst (apply_binder (BindCube.find cods (id_sface (CubeOf.dim doms))) eargs) out_args
          in
          return (Term.App (sfn, cargs), output, rest))
  (* We can also "apply" a higher-dimensional *type*, leading to a (further) instantiation of it.  Here the number of arguments must exactly match *some* integral instantiation. *)
  | UU n -> (
      (* Ensure that the universe is (fully) instantiated at the right dimension. *)
      match compare (TubeOf.inst tyargs) n with
      | Neq ->
          Printf.printf "Dimension mismatch when synthesizing instantiation";
          None
      | Eq -> (
          match D.compare_zero n with
          | Zero ->
              Printf.printf "Cannot further instantiate a zero-dimensional type";
              None
          | Pos pn ->
              (* We take enough arguments to instatiate a type of dimension n by one, and check each argument against the corresponding type instantiation argument, itself instantiated at the values of the appropriate previous arguments.  This requires random access to the previous evaluated arguments, so we store those in a hashtable, while also assembling them into a tube for later. *)
              let (Is_suc (m, msuc)) = suc_pos pn in
              let open TubeOf.Monadic (M) in
              let open TubeOf.Infix in
              let eargtbl = Hashtbl.create 10 in
              let tyargs1 = TubeOf.pboundary (D.zero_plus m) msuc tyargs in
              let* [ cargs; eargs ], rest =
                pmapM
                  {
                    map =
                      (fun fa [ tyarg ] ->
                        let open Monad.Ops (M) in
                        let* ts = M.get in
                        let* tm =
                          match ts with
                          | [] -> M.stateless None
                          | t :: ts ->
                              let* () = M.put ts in
                              return t in
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
                        let ty = inst tyarg kargs in
                        let* ctm = M.stateless (check ctx tm ty) in
                        let etm = Ctx.eval ctx ctm in
                        let () = Hashtbl.add eargtbl (SFace_of fa) etm in
                        return (ctm @: [ etm ]));
                  }
                  [ tyargs1 ] (Cons (Cons Nil)) args in
              (* Now we assemble the synthesized type, which is a full instantiation of the universe at a telescope consisting of instantiations of the type arguments at the evaluated term arguments. *)
              let margs =
                TubeOf.build D.zero (D.zero_plus m)
                  {
                    build =
                      (fun fe ->
                        let j = dom_tface fe in
                        let (Plus jsuc) = D.plus (D.plus_right msuc) in
                        inst
                          (TubeOf.find tyargs (tface_plus fe msuc msuc jsuc))
                          (TubeOf.build j jsuc
                             {
                               build =
                                 (fun fa ->
                                   let (PFace_of_plus (pq, fc, fd)) = pface_of_plus fa in
                                   TubeOf.find eargs
                                     (sface_plus_tface
                                        (comp_sface (sface_of_tface fe) fc)
                                        (D.plus_zero m) msuc pq fd));
                             }));
                  } in
              return (Term.Inst (sfn, cargs), inst (Uninst (UU m)) margs, rest)))
  (* Something that synthesizes a type that isn't a pi-type or a universe cannot be applied to anything, but this is a user error, not a bug. *)
  | _ ->
      Printf.printf "Attempt to apply non-function, non-type";
      None
