open Dim
open Value
open Act
open Term
open Bwd
open Monad.Ops (Monad.Maybe)

let rec eval : type m b. (m, b) env -> b term -> value =
 fun env tm ->
  match tm with
  | Var v -> lookup act_any env v
  | Const name ->
      let dim = dim_env env in
      Uninst
        (Neu
           {
             fn = Const { name; dim };
             args = Emp;
             ty =
               inst
                 (eval (Emp dim) (Hashtbl.find Global.types name))
                 (TubeOf.build D.zero (D.zero_plus dim)
                    {
                      build =
                        (fun fa -> eval (Act (env, op_of_sface (sface_of_tface fa))) (Const name));
                    });
           })
  | UU -> Uninst (UU (dim_env env))
  | Inst (tm, args) ->
      let nk = TubeOf.plus args in
      (* Add the environment dimension to the uninstantiated dimensions *)
      let m = dim_env env in
      let (Plus mn) = D.plus (TubeOf.uninst args) in
      (* Evaluate the inner term *)
      let newtm = eval env tm in
      (* Evaluate the arguments, rearranging and acting by faces and degeneracies *)
      let (Plus mn_k) = D.plus (D.plus_right nk) in
      let newargs =
        TubeOf.build (D.plus_out m mn) mn_k
          {
            build =
              (fun fa ->
                let (TFace_of_plus (_, fb, fcd)) = tface_of_plus mn fa in
                let Eq = D.plus_uniq (cod_plus_of_tface fcd) nk in
                eval (Act (env, op_of_sface fb)) (TubeOf.find args fcd));
          } in
      inst newtm newargs
  | Lam (n_faces, plus_n_faces, body) ->
      let (Plus mn) = D.plus (dim_faces n_faces) in
      Lam (eval_binder env n_faces mn plus_n_faces body)
  | App (fn, args) ->
      (* First we evaluate the function. *)
      let efn = eval env fn in
      (* The environment is m-dimensional and the original application is n-dimensional, so the *substituted* application is m+n dimensional.  Thus must therefore match the dimension of the function being applied. *)
      let m = dim_env env in
      let n = CubeOf.dim args in
      let (Plus m_n) = D.plus n in
      let mn = D.plus_out m m_n in
      (* Then we evaluate all the arguments, not just in the given environment (of dimension m), but in that environment acted on by all the strict faces of m.  Since the given arguments are indexed by strict faces of n, the result is a collection of values indexed by strict faces of m+n.  *)
      let eargs =
        CubeOf.build mn
          {
            build =
              (* Specifically, for each face of m+n... *)
              (fun fab ->
                (* ...we decompose it as a sum of a face "fa" of m and a face "fb" of n... *)
                let (SFace_of_plus (_, fa, fb)) = sface_of_plus m_n fab in
                (* ...and evaluate the supplied argument indexed by the face fb of n, in an environment acted on by the face fa of m. *)
                eval (Act (env, op_of_sface fa)) (CubeOf.find args fb));
          } in
      (* Having evaluated the function and its arguments, we now pass the job off to a helper function. *)
      apply efn eargs
  | Pi (dom, cod) ->
      (* A user-space pi-type always has dimension zero, so this is simpler than the general case. *)
      let m = dim_env env in
      let doms = CubeOf.build m { build = (fun fa -> eval (Act (env, op_of_sface fa)) dom) } in
      let cods =
        BindCube.build m
          {
            build =
              (fun fa ->
                eval_binder
                  (Act (env, op_of_sface fa))
                  faces_zero
                  (D.plus_zero (dom_sface fa))
                  (Suc Zero) cod);
          } in
      Uninst (Pi (doms, cods))
  | Refl x ->
      (* It's tempting to write just "act_value (eval env x) refl" here, and similarly below for sym, but that is WRONG!  Pushing a substitution through an operator action requires whiskering the operator by the dimension of the substitution. *)
      let k = dim_env env in
      let (Plus km) = D.plus (dom_deg refl) in
      let (Plus kn) = D.plus (cod_deg refl) in
      let krefl = plus_deg k kn km refl in
      act_value (eval env x) krefl
  | Sym x ->
      let k = dim_env env in
      let (Plus km) = D.plus (dom_deg sym) in
      let (Plus kn) = D.plus (cod_deg sym) in
      let ksym = plus_deg k kn km sym in
      act_value (eval env x) ksym

(* Apply a function value to an argument (with its boundaries). *)
and apply : type n. value -> (n, value) CubeOf.t -> value =
 fun fn arg ->
  match fn with
  (* If the function is a lambda-abstraction, we check that it has the correct dimension and then beta-reduce, adding the arguments to the environment. *)
  | Lam body -> (
      let m = CubeOf.dim arg in
      match compare (dim_binder body) m with
      | Neq -> raise (Failure "Dimension mismatch applying a lambda")
      | Eq -> apply_binder body (id_sface m) arg)
  (* If it is a neutral application... *)
  | Uninst (Neu { fn; args; ty }) -> (
      match ty with
      | Inst { tm = Pi (doms, cods); dim = _; args = tyargs } ->
          (* We annotate the new argument by its type, extracted from the domain type of the function being applied, and compute the new output type. *)
          let newarg, ty = annote_arg doms cods tyargs arg in
          (* Then we add the new argument to the existing application spine, and possibly evaluate further with a case tree. *)
          apply_spine fn (Snoc (args, newarg)) ty
      | Uninst (Pi (doms, cods)) ->
          let newarg, ty = annote_arg doms cods (TubeOf.empty (CubeOf.dim arg)) arg in
          apply_spine fn (Snoc (args, newarg)) ty
      | _ -> raise (Failure "Invalid annotation by non-function type"))
  | _ -> raise (Failure "Invalid application of non-function")

(* Compute the application of a head to a spine of arguments, using a case tree for a head constant if possible, otherwise just constructing a neutral application.  We have to be given the overall type of the application to annotate the latter case. *)
and apply_spine : head -> app Bwd.t -> value -> value =
 fun fn args ty ->
  (* Check whether the head is a constant with an associated case tree. *)
  Option.value
    (match fn with
    | Const { name; dim } ->
        let* tree = Hashtbl.find_opt Global.trees name in
        apply_tree (Emp dim) tree (Any (id_deg dim)) (Bwd.prepend args [])
    | _ -> None)
    (* If it has no case tree, or is not a constant, we just add the argument to the neutral application spine and return. *)
    ~default:(Uninst (Neu { fn; args; ty }))

(* Evaluate a case tree, in an environment of variables for which we have already found values, with possible additional arguments.  The degeneracy is one to be applied to the value of the case tree *before* applying it to any additional arguments; thus if it is nonidentity we cannot pick up additional arguments.  Return None if the case tree doesn't apply for any reason (e.g. not enough arguments, or a dispatching argument doesn't match any branch, or there is a nonidentity degeneracy in the way of picking up extra arguments). *)
and apply_tree : type n a. (n, a) env -> a Case.tree -> any_deg -> app list -> value option =
 fun env tree ins args ->
  match tree with
  | Lam (plus, body) ->
      (* Pick up more arguments *)
      let* newenv, newins, newargs = take_lam_args env plus ins args in
      apply_tree newenv body newins newargs
  | Leaf body ->
      (* We've found a term to evaluate *)
      let res = act_any (eval env body) ins in
      (* Now apply this to any remaining arguments. *)
      Some
        (List.fold_left
           (fun f (Value.App (a, i)) -> act_value (apply f (val_of_norm a)) (perm_of_ins i))
           res args)
  | Branch (ix, branches) -> (
      (* Get the argument being inspected *)
      match lookup act_any env ix with
      (* It must be an application of a constant *)
      | Uninst (Neu { fn = Const { name; dim }; args = dargs; ty = _ }) -> (
          (* A case tree can only include 0-dimensional applications, so the dimension here must match the dimension we're using it at. *)
          match compare dim (dim_env env) with
          | Eq -> apply_branches env branches name dargs ins args
          | _ -> None)
      | _ -> None)

(* Attempt all the branches of a case tree associated to a particular argument, matching each of their constant labels against its constant. *)
and apply_branches :
    type n a.
    (n, a) env ->
    a Case.branch list ->
    (* The constant we're matching against *)
    Constant.t ->
    (* Its given arguments *)
    app Bwd.t ->
    (* A degeneracy to be applied after the computation *)
    any_deg ->
    (* The remaining arguments after the case tree computation *)
    app list ->
    value option =
 fun env branches dcst dargs ins args ->
  match branches with
  | [] -> None
  | Branch (name, sub, plus, body) :: rest ->
      if name = dcst then
        (* If we have a branch with a matching constant, then in the argument the constant must be applied to exactly the right number of elements (in dargs).  In that case, we pick out a possibly-smaller number of them (determined by a subset) and add them to the environment. *)
        let* env = take_branch_args env sub dargs plus in
        (* Then we proceed recursively with the body of that branch. *)
        apply_tree env body ins args
      else
        (* If the constant doesn't match, proceed with later branches. *)
        apply_branches env rest dcst dargs ins args

and take_branch_args :
    type n a b ab c.
    (n, a) env -> (b, c) N.subset -> app Bwd.t -> (a, b, ab) N.plus -> (n, ab) env option =
 fun env sub dargs plus ->
  match (sub, dargs, plus) with
  | Zero, Emp, Zero -> Some env
  | Omit sub, Snoc (dargs, _), _ -> take_branch_args env sub dargs plus
  | Take sub, Snoc (dargs, App (arg, ins)), Suc plus -> (
      (* We can only take arguments that have no degeneracy applied, since case trees are specified at dimension zero. *)
      let* () = is_id_deg (perm_of_ins ins) in
      (* Since dargs is a backwards list, we have to first take all the other arguments and then our current one.  *)
      let* env = take_branch_args env sub dargs plus in
      (* Again, since case trees are specified at dimension zero, all the applications must be the same dimension. *)
      match compare (CubeOf.dim arg) (dim_env env) with
      | Eq ->
          (* Why is this type annotation necessary? *)
          return (Ext (env, (val_of_norm arg : (n, value) CubeOf.t)))
      | Neq -> None)
  | _ -> None

and take_lam_args :
    type n a b ab.
    (n, a) env ->
    (a, b, ab) N.plus ->
    any_deg ->
    app list ->
    ((n, ab) env * any_deg * app list) option =
 fun env ab ins args ->
  match (ab, args) with
  | Zero, _ -> Some (env, ins, args)
  | Suc ab, App (arg, newins) :: args -> (
      (* If we're looking for another argument, we fail unless the current insertion is the identity.  In addition, the variables bound in a case tree are always zero-dimensional applications, so the apps here must all be the same dimension as the constant instance. *)
      match (is_id_any_deg ins, compare (dim_env env) (CubeOf.dim arg)) with
      | Some (), Eq ->
          take_lam_args
            (Ext (env, val_of_norm arg))
            (N.suc_plus' ab)
            (Any (perm_of_ins newins))
            args
      | _ -> None)
  | _, _ -> None

(* Given a family of value arguments (including boundaries) for a function of some given type (with domains and codomains), annotate the arguments to make them into normals (hence an "app"), and also compute the type of the applied function.  *)
and annote_arg :
    type a b ab k n.
    (k, value) CubeOf.t ->
    (k, unit) BindCube.t ->
    (a, b, ab, value) TubeOf.t ->
    (n, value) CubeOf.t ->
    app * value =
 fun doms cods pi_args args ->
  (* We check that the pi-type has the correct dimension, is fully instantiated, and has the correct dimension of instantiation. *)
  let mn = CubeOf.dim doms in
  match
    ( compare (TubeOf.uninst pi_args) D.zero,
      compare (TubeOf.inst pi_args) mn,
      compare (CubeOf.dim args) mn )
  with
  | Neq, _, _ -> raise (Failure "Application of non-fully-instantiated function")
  | _, Neq, _ -> raise (Failure "Instantiation mismatch applying a neutral function")
  | _, _, Neq -> raise (Failure "Arguments mismatch applying a neutral function")
  | Eq, Eq, Eq ->
      let Eq = D.plus_uniq (TubeOf.plus pi_args) (D.zero_plus mn) in
      (* In this case, the arguments must be normals rather than values.  Thus, while collecting them into a Bwv, we also compute their types from the domain types of the function-type, instantiated at previous arguments. *)
      let new_args =
        CubeOf.mmap
          {
            map =
              (fun fab [ dom ] ->
                let tm = CubeOf.find args fab in
                let k = dom_sface fab in
                let ty =
                  inst dom
                    (TubeOf.build D.zero (D.zero_plus k)
                       { build = (fun fc -> CubeOf.find args (comp_sface fab (sface_of_tface fc))) })
                in
                { tm; ty });
          }
          [ doms ] in
      (* The output type substitutes the arguments into the codomain of the function-type, and instantiates at the values of the boundary functions applied to appropriate ones of these arguments.  This loop is very similar to the previous one, so perhaps they could be combined. *)
      let out_args =
        TubeOf.mmap
          {
            map =
              (fun fab [ afn ] ->
                apply afn
                  (CubeOf.build (dom_tface fab)
                     { build = (fun fc -> CubeOf.find args (comp_sface (sface_of_tface fab) fc)) }));
          }
          [ pi_args ] in
      let idf = id_sface mn in
      let output = inst (apply_binder (BindCube.find cods idf) idf args) out_args in
      (App (new_args, zero_ins mn), output)

and eval_binder :
    type m n mn b f bf.
    (m, b) env ->
    (n, f) count_faces ->
    (m, n, mn) D.plus ->
    (b, f, bf) N.plus ->
    bf term ->
    mn binder =
 fun env bound_faces plus_dim plus_faces body ->
  (* let n = dim_faces bound_faces in *)
  let m = dim_env env in
  let nf = sfaces bound_faces in
  let args =
    Bwv.map
      (fun (SFace_of fa) ->
        CubeOf.build m
          {
            build =
              (fun fb ->
                let (Plus plus_dom) = D.plus (dom_sface fa) in
                Face_of
                  (Face
                     ( sface_plus_sface fb plus_dim plus_dom fa,
                       id_perm (D.plus_out (dom_sface fb) plus_dom) )));
          })
      nf in
  let perm = id_perm (D.plus_out m plus_dim) in
  Bind { env; perm; plus_dim; bound_faces; plus_faces; body; args }

(* TODO: Describe this function, particularly the sface argument *)
and apply_binder : type m n f a. m binder -> (m, n) sface -> (n, value) CubeOf.t -> value =
 fun (Bind b) s argstbl ->
  act_value
    (eval
       (env_append b.plus_faces b.env
          (Bwv.map
             (fun ffs ->
               CubeOf.mmap
                 {
                   map =
                     (fun _ [ Face_of (Face (fa, fb)) ] ->
                       act_value (CubeOf.find argstbl (comp_sface s fa)) fb);
                 }
                 [ ffs ])
             b.args))
       b.body)
    b.perm
