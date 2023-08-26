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
      msg "Not enough lambdas";
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
  (* If the "type" is not a type here, or not fully instantiated, that's a user error, not a bug. *)
  let* (Fullinst (uty, tyargs)) = full_inst_opt ty in
  match (tm, uty) with
  | Synth stm, _ ->
      let* sval, sty = synth ctx stm in
      let* () = equal_val ctx sty ty in
      return sval
  | Lam _, Pi (doms, cods) -> (
      let m = CubeOf.dim doms in
      match compare (TubeOf.inst tyargs) m with
      | Neq ->
          msg "Dimension mismatch in checking lambda";
          None
      | Eq ->
          let Eq = D.plus_uniq (TubeOf.plus tyargs) (D.zero_plus m) in
          (* Slurp up the right number of lambdas for the dimension of the pi-type, and pick up the body inside them. *)
          let (Faces dom_faces) = count_faces (CubeOf.dim doms) in
          let (Plus af) = N.plus (faces_out dom_faces) in
          let* body = lambdas af tm in
          (* Extend the context by one variable for each type in doms, instantiated at the appropriate previous ones. *)
          let ctx, newargs = Ctx.dom_vars ctx dom_faces af doms in
          (* Apply and instantiate the codomain to those arguments to get a type to check the body at. *)
          let output = tyof_app cods tyargs newargs in
          let* cbody = check ctx body output in
          return (Term.Lam (dom_faces, af, cbody)))
  | Struct tms, Neu (Const { name; dim }, _) ->
      let* (Record { fields; _ }) = Hashtbl.find_opt Global.records name in
      (* The type of each record field, at which we check the corresponding field supplied in the struct, is the type associated to that field name in general, evaluated at the supplied parameters and at "the term itself".  We don't have the whole term available while typechecking, of course, but we can build a version of it that contains all the previously typechecked fields, which is all we need for a well-typed record.  So we iterate through the fields (in order) using a state monad as well that accumulates the previously typechecked and evaluated fields. *)
      let module M =
        Monad.StateT
          (Monad.Maybe)
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
            let* tm = M.stateless (Field.Map.find_opt fld tms) in
            let* ctm = M.stateless (check ctx tm ety) in
            let etm = Ctx.eval ctx ctm in
            M.put (Field.Map.add fld ctm ctms, Field.Map.add fld etm etms))
          [ fields ]
          (Field.Map.empty, Field.Map.empty) in
      return (Struct ctms)
  | _ -> None

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
  | UU -> return (Term.UU, universe D.zero)
  | Pi (dom, cod) ->
      (* User-level pi-types are always dimension zero, so the domain must be a zero-dimensional type. *)
      let* cdom = check ctx dom (universe D.zero) in
      let edom = Ctx.eval ctx cdom in
      let* ccod = check (Snoc (ctx, edom)) cod (universe D.zero) in
      return (Term.Pi (cdom, ccod), universe D.zero)
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
        msg "Can't symmetrize something of too low dimension";
        None)
  | Asc (tm, ty) ->
      let* cty = check ctx ty (universe D.zero) in
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
    (D.zero, n, n, normal) TubeOf.t ->
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
          msg "Dimension mismatch when synthesizing applied function";
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
      | Neq ->
          msg "Dimension mismatch when synthesizing instantiation";
          None
      | Eq -> (
          match D.compare_zero n with
          | Zero ->
              msg "Cannot further instantiate a zero-dimensional type";
              None
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
                          | [] -> M.stateless None
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
  | _ ->
      msg "Attempt to apply non-function, non-type";
      None
