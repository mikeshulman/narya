open Raw
open Value
open Term
open Dim
open Act
open Norm
open Equal
open Monad.Ops (Monad.Maybe)
module CTCCubeMap1_2 = CubeMap1_2 (ConstFam) (TermFam) (ConstFam)
module CTCTubeMap1_2 = TubeMap1_2 (ConstFam) (TermFam) (ConstFam)

(* A context is a list of variables with types which are values.  The variables themselves, when represented by De Bruijn LEVELS, can appear in the types of later variables.  In particular, the LENGTH of this context, which is its type parameter as a type-level nat, is the current De Bruijn LEVEL for new variables to be added.  We can look up the INDEX of a TERM VARIABLE into this Bwv to get its type, but not of course the LEVEL of a VALUE VARIABLE. *)
type 'a ctx = (value, 'a) Bwv.t

let level_of : 'a ctx -> int = fun ctx -> N.to_int (Bwv.length ctx)

(* The empty context *)
let empty_ctx : N.zero ctx = Emp

(* Every context has an underlying environment that substitutes each (level) variable for itself (index).  This environment ALWAYS HAS DIMENSION ZERO, and therefore in particular the variables don't need to come with their boundaries. *)
let rec env_of_ctx : type a. a ctx -> (D.zero, a) env = function
  | Emp -> Emp D.zero
  | Snoc (ctx, ty) ->
      Ext (env_of_ctx ctx, ConstCube.build D.zero { build = (fun _ -> var (level_of ctx) ty) })

(* Evaluate a term in (the environment of) a context.  Thus, replace its De Bruijn indices with De Bruijn levels, and substitute the values of variables with definitions. *)
let eval_in_ctx : type a. a ctx -> a term -> value = fun ctx tm -> eval (env_of_ctx ctx) tm

(* Extend a context by a finite number of new variables, whose types are specified in a hashtable. *)
let rec ctx_exts :
    type a b ab c. a ctx -> (a, b, ab) N.plus -> (c, b) Bwv.t -> (c, value) Hashtbl.t -> ab ctx =
 fun ctx ab keys vals ->
  match (ab, keys) with
  | Zero, Emp -> ctx
  | Suc ab, Snoc (keys, key) -> Snoc (ctx_exts ctx ab keys vals, Hashtbl.find vals key)

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

let rec check : type a. a ctx -> a check -> value -> a term option =
 fun ctx tm ty ->
  match tm with
  | Synth stm ->
      let* sval, sty = synth ctx stm in
      let* () = equal_val (level_of ctx) sty ty in
      return sval
  | Lam _ -> (
      (* We don't pick up the body here, only the presence of at least one lambda.  We'll pick up an appropriate number of lambdas in check_lam. *)
      match ty with
      | Inst { tm = ty; dim = _; args } -> check_lam ctx tm ty args
      | Uninst ty -> check_lam ctx tm ty (ConstTube.empty D.zero)
      (* A lambda-abstraction is never a type, so we can't check against it.  But this is a user error, not a bug, since the user could write an abstraction on the RHS of an ascription. *)
      | Lam _ ->
          Printf.printf "Lambda is not a type";
          None)

and check_lam :
    type a m n mn f. a ctx -> a check -> uninst -> (m, n, mn, value) ConstTube.t -> a term option =
 fun ctx tm ty args ->
  match ty with
  | Pi (doms, cods) -> (
      let m = ConstCube.dim doms in
      match (compare (ConstTube.uninst args) D.zero, compare (ConstTube.inst args) m) with
      | Neq, _ | _, Neq ->
          Printf.printf "Dimension mismatch in checking lambda";
          None
      | Eq, Eq ->
          let Eq = D.plus_uniq (ConstTube.plus args) (D.zero_plus m) in
          (* Slurp up the right number of lambdas for the dimension of the pi-type, and pick up the body inside them. *)
          let (Faces dom_faces) = count_faces (ConstCube.dim doms) in
          let (Plus af) = N.plus (faces_out dom_faces) in
          let* body = lambdas af tm in
          (* Extend the context by one variable for each type in doms, instantiated at the appropriate previous ones.  We store them in a hashtable as we go, for easy access to the previous ones for this instantiation. *)
          let argtbl = Hashtbl.create 10 in
          let ctx =
            ConstCube.fold_left_append
              {
                fold =
                  (fun c fa dom ->
                    let ty =
                      inst dom
                        (ConstTube.build D.zero
                           (D.zero_plus (dom_sface fa))
                           {
                             build =
                               (fun fc ->
                                 Hashtbl.find argtbl (SFace_of (comp_sface fa (sface_of_tface fc))));
                           }) in
                    let v =
                      Uninst
                        (Neu
                           { fn = Var { level = level_of c; deg = id_deg D.zero }; args = Emp; ty })
                    in
                    let () = Hashtbl.add argtbl (SFace_of fa) v in
                    ty);
              }
              ctx dom_faces af doms in
          (* TODO: Can we combine this with the previous iteration? *)
          let newargs =
            ConstCube.build m { build = (fun fa -> Hashtbl.find argtbl (SFace_of fa)) } in
          (* Apply and instantiate the codomain to those arguments to get a type to check the body at. *)
          let out_args =
            ConstTube.mmap
              {
                map =
                  (fun fa [ afn ] ->
                    apply afn
                      (ConstCube.build (dom_tface fa)
                         {
                           build =
                             (fun fc -> ConstCube.find newargs (comp_sface (sface_of_tface fa) fc));
                         }));
              }
              [ args ] in
          let idf = id_sface m in
          let output = inst (apply_binder (BindCube.find cods idf) idf newargs) out_args in
          let* cbody = check ctx body output in
          return (Term.Lam (dom_faces, af, cbody)))
  (* We can't check a lambda-abstraction against anything except a pi-type. *)
  | _ ->
      Printf.printf "Can't check lambda against non-pi-type";
      None

and synth : type a. a ctx -> a synth -> (a term * value) option =
 fun ctx tm ->
  match tm with
  | Var v -> return (Term.Var v, Bwv.nth v ctx)
  | Const name -> return (Const name, eval (Emp D.zero) (Hashtbl.find Global.types name))
  | UU -> return (Term.UU, Uninst (UU D.zero))
  | Pi (dom, cod) ->
      (* User-level pi-types are always dimension zero, so the domain must be a zero-dimensional type. *)
      let* cdom = check ctx dom (Uninst (UU D.zero)) in
      let edom = eval_in_ctx ctx cdom in
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
      let ex = eval_in_ctx ctx sx in
      return (Refl sx, act_ty ex ety refl)
  | Sym x -> (
      let* sx, ety = synth ctx x in
      let ex = eval_in_ctx ctx sx in
      try
        let symty = act_ty ex ety sym in
        return (Sym sx, symty)
      with Invalid_uninst_action ->
        Printf.printf "Can't symmetrize something of too low dimension";
        None)
  | Asc (tm, ty) ->
      let* cty = check ctx ty (Uninst (UU D.zero)) in
      let ety = eval_in_ctx ctx cty in
      let* ctm = check ctx tm ety in
      return (ctm, ety)

(* Given a synthesized function and its type, and a list of arguments, check the arguments in appropriately-sized groups. *)
and synth_apps : type a. a ctx -> a term -> value -> a check list -> (a term * value) option =
 fun ctx sfn sty args ->
  (* First we check one group of arguments. *)
  let* afn, aty, aargs =
    match sty with
    | Inst { tm = fnty; dim = _; args = tyargs } -> synth_app ctx sfn fnty tyargs args
    | Uninst fnty -> synth_app ctx sfn fnty (ConstTube.empty D.zero) args
    (* A lambda-abstraction here would really be a bug, not a user error: the user can try to check something against an abstraction as if it were a type, but our synthesis functions should never synthesize an abstraction as if it were a type.  Thus, we raise an exception rather than returning None. *)
    | Lam _ -> raise (Failure "Synthesized type cannot be a lambda-abstraction") in
  (* If that used up all the arguments, we're done; otherwise we continue with the rest of the arguments. *)
  match aargs with
  | [] -> return (afn, aty)
  | _ :: _ -> synth_apps ctx afn aty aargs

and synth_app :
    type a m n mn f.
    a ctx ->
    a term ->
    uninst ->
    (m, n, mn, value) ConstTube.t ->
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
  match fnty with
  (* The obvious thing we can "apply" is an element of a pi-type. *)
  | Pi (doms, cods) -> (
      (* Ensure that the pi-type is fully instantiated and at the right dimension. *)
      let n = ConstCube.dim doms in
      match (compare (ConstTube.inst tyargs) n, compare (ConstTube.uninst tyargs) D.zero) with
      | Neq, _ | _, Neq ->
          Printf.printf "Dimension mismatch when synthesizing applied function";
          None
      | Eq, Eq ->
          let Eq = D.plus_uniq (ConstTube.plus tyargs) (D.zero_plus n) in
          (* Pick up the right number of arguments for the dimension, leaving the others for a later call to synth_app.  Then check each argument against the corresponding type in "doms", instantiated at the appropriate evaluated previous arguments, and evaluate it, producing Cubes of checked terms and values.  Since each argument has to be checked against a type instantiated at the *values* of the previous ones, we also store those in a hashtable as we go. *)
          let eargtbl = Hashtbl.create 10 in
          let* (cargs, eargs), rest =
            let open CTCCubeMap1_2 (M) in
            mapM1_2
              {
                map =
                  (fun fa dom ->
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
                        (ConstTube.build D.zero
                           (D.zero_plus (dom_sface fa))
                           {
                             build =
                               (fun fc ->
                                 Hashtbl.find eargtbl (SFace_of (comp_sface fa (sface_of_tface fc))));
                           }) in
                    let* ctm = M.stateless (check ctx tm ty) in
                    let etm = eval_in_ctx ctx ctm in
                    Hashtbl.add eargtbl (SFace_of fa) etm;
                    return (ctm, etm));
              }
              doms args in
          (* Evaluate cod at these evaluated arguments, and instantiate it at the appropriate values of tyargs, as with similar code in other places. *)
          let out_args =
            ConstTube.mmap
              {
                map =
                  (fun fa [ afn ] ->
                    apply afn
                      (ConstCube.build (dom_tface fa)
                         {
                           build =
                             (fun fc -> ConstCube.find eargs (comp_sface (sface_of_tface fa) fc));
                         }));
              }
              [ tyargs ] in
          let idf = id_sface n in
          let output = inst (apply_binder (BindCube.find cods idf) idf eargs) out_args in
          return (Term.App (sfn, cargs), output, rest))
  (* We can also "apply" a higher-dimensional *type*, leading to a (further) instantiation of it.  Here the number of arguments must exactly match *some* integral instantiation. *)
  | UU n -> (
      (* Ensure that the universe is fully instantiated and at the right dimension. *)
      match (compare (ConstTube.inst tyargs) n, compare (ConstTube.uninst tyargs) D.zero) with
      | Neq, _ | _, Neq ->
          Printf.printf "Dimension mismatch when synthesizing instantiation";
          None
      | Eq, Eq -> (
          let Eq = D.plus_uniq (ConstTube.plus tyargs) (D.zero_plus n) in
          match D.compare_zero n with
          | Zero ->
              Printf.printf "Cannot instatiate a zero-dimensional type";
              None
          | Pos pn ->
              (* We take enough arguments to instatiate a type of dimension n by one, and check each argument against the corresponding type instantiation argument, itself instantiated at the values of the appropriate previous arguments.  This requires random access to the previous evaluated arguments, so we store those in a hashtable, while also assembling them into a tube for later. *)
              let (Is_suc (m, msuc)) = suc_pos pn in
              let open ConstTube.Monadic (M) in
              let eargtbl = Hashtbl.create 10 in
              let tyargs1 = ConstTube.pboundary (D.zero_plus m) msuc tyargs in
              let* (cargs, eargs), rest =
                let open CTCTubeMap1_2 (M) in
                mapM1_2
                  {
                    map =
                      (fun fa tyarg ->
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
                          ConstTube.build D.zero (D.zero_plus k)
                            {
                              build =
                                (fun fb ->
                                  Hashtbl.find eargtbl
                                    (SFace_of (comp_sface fa (sface_of_tface fb))));
                            } in
                        let ty = inst tyarg kargs in
                        let* ctm = M.stateless (check ctx tm ty) in
                        let etm = eval_in_ctx ctx ctm in
                        let () = Hashtbl.add eargtbl (SFace_of fa) etm in
                        return (ctm, etm));
                  }
                  tyargs1 args in
              (* Now we assemble the synthesized type, which is a full instantiation of the universe at a telescope consisting of instantiations of the type arguments at the evaluated term arguments. *)
              let margs =
                ConstTube.build D.zero (D.zero_plus m)
                  {
                    build =
                      (fun fe ->
                        let j = dom_tface fe in
                        let (Plus jsuc) = D.plus (D.plus_right msuc) in
                        inst
                          (ConstTube.find tyargs (tface_plus fe msuc msuc jsuc))
                          (ConstTube.build j jsuc
                             {
                               build =
                                 (fun fa ->
                                   let (PFace_of_plus (pq, fc, fd)) = pface_of_plus fa in
                                   ConstTube.find eargs
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
