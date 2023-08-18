open Dim
open Value
open Act
open Term
open Global

let rec eval : type m b. (m, b) env -> b term -> value =
 fun env tm ->
  match tm with
  | Var v -> lookup act_any env v
  | Const name ->
      Uninst (Neu { fn = Const { name; dim = D.zero }; args = Emp; ty = Hashtbl.find global name })
  | UU -> Uninst (UU (dim_env env))
  | Inst (tm, args) ->
      let nk = TermTube.plus args in
      (* Add the environment dimension to the uninstantiated dimensions *)
      let m = dim_env env in
      let (Plus mn) = D.plus (TermTube.uninst args) in
      (* Evaluate the inner term *)
      let newtm = eval env tm in
      (* Evaluate the arguments, rearranging and acting by faces and degeneracies *)
      let (Plus mn_k) = D.plus (D.plus_right nk) in
      let newargs =
        ConstTube.build (D.plus_out m mn) mn_k
          {
            build =
              (fun fa ->
                let (TFace_of_plus (_, fb, fcd)) = tface_of_plus mn fa in
                let Eq = D.plus_uniq (cod_plus_of_tface fcd) nk in
                eval (Act (env, op_of_sface fb)) (TermTube.find args fcd));
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
      let n = TermCube.dim args in
      let (Plus m_n) = D.plus n in
      let mn = D.plus_out m m_n in
      (* Then we evaluate all the arguments, not just in the given environment (of dimension m), but in that environment acted on by all the strict faces of m.  Since the given arguments are indexed by strict faces of n, the result is a collection of values indexed by strict faces of m+n.  *)
      let eargs =
        ConstCube.build mn
          {
            build =
              (* Specifically, for each face of m+n... *)
              (fun fab ->
                (* ...we decompose it as a sum of a face "fa" of m and a face "fb" of n... *)
                let (SFace_of_plus (_, fa, fb)) = sface_of_plus m_n fab in
                (* ...and evaluate the supplied argument indexed by the face fb of n, in an environment acted on by the face fa of m. *)
                eval (Act (env, op_of_sface fa)) (TermCube.find args fb));
          } in
      (* Having evaluated the function and its arguments, we now pass the job off to a helper function. *)
      apply efn eargs
  | Pi (dom, cod) ->
      (* A user-space pi-type always has dimension zero, so this is simpler than the general case. *)
      let m = dim_env env in
      let doms = ConstCube.build m { build = (fun fa -> eval (Act (env, op_of_sface fa)) dom) } in
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

and apply : type n. value -> (n, value) ConstCube.t -> value =
 fun fn arg ->
  match fn with
  (* If the function is a lambda-abstraction, we check that it has the correct dimension and then beta-reduce, adding the arguments to the environment. *)
  | Lam body -> (
      let m = ConstCube.dim arg in
      match compare (dim_binder body) m with
      | Neq -> raise (Failure "Dimension mismatch applying a lambda")
      | Eq -> apply_binder body (id_sface m) arg)
  (* If it is a neutral application, we add the new argument to its list, first decomposing the function-type to annotate the new argument by its type and compute the new type of the further application. *)
  | Uninst (Neu { fn; args; ty }) -> (
      match ty with
      | Inst { tm = Pi (doms, cods); dim = _; args = tyargs } ->
          let newarg, outty = annote_arg doms cods tyargs arg in
          Uninst (Neu { fn; args = Snoc (args, newarg); ty = outty })
      | Uninst (Pi (doms, cods)) ->
          let newarg, outty = annote_arg doms cods (ConstTube.empty (ConstCube.dim arg)) arg in
          Uninst (Neu { fn; args = Snoc (args, newarg); ty = outty })
      | _ -> raise (Failure "Invalid annotation by non-function type"))
  | _ -> raise (Failure "Invalid application of non-function")

and annote_arg :
    type a b ab k n.
    (k, value) ConstCube.t ->
    (k, unit) BindCube.t ->
    (a, b, ab, value) ConstTube.t ->
    (n, value) ConstCube.t ->
    app * value =
 fun doms cods pi_args args ->
  (* We check that the pi-type has the correct dimension, is fully instantiated, and has the correct dimension of instantiation. *)
  let mn = ConstCube.dim doms in
  match
    ( compare (ConstTube.uninst pi_args) D.zero,
      compare (ConstTube.inst pi_args) mn,
      compare (ConstCube.dim args) mn )
  with
  | Neq, _, _ -> raise (Failure "Application of non-fully-instantiated function")
  | _, Neq, _ -> raise (Failure "Instantiation mismatch applying a neutral function")
  | _, _, Neq -> raise (Failure "Arguments mismatch applying a neutral function")
  | Eq, Eq, Eq ->
      let Eq = D.plus_uniq (ConstTube.plus pi_args) (D.zero_plus mn) in
      (* In this case, the arguments must be normals rather than values.  Thus, while collecting them into a Bwv, we also compute their types from the domain types of the function-type, instantiated at previous arguments. *)
      let new_args =
        ConstCube.mmap
          {
            map =
              (fun fab [ dom ] ->
                let tm = ConstCube.find args fab in
                let k = dom_sface fab in
                let ty =
                  inst dom
                    (ConstTube.build D.zero (D.zero_plus k)
                       {
                         build =
                           (fun fc -> ConstCube.find args (comp_sface fab (sface_of_tface fc)));
                       }) in
                { tm; ty });
          }
          [ doms ] in
      (* The output type substitutes the arguments into the codomain of the function-type, and instantiates at the values of the boundary functions applied to appropriate ones of these arguments.  This loop is very similar to the previous one, so perhaps they could be combined. *)
      let out_args =
        ConstTube.mmap
          {
            map =
              (fun fab [ afn ] ->
                apply afn
                  (ConstCube.build (dom_tface fab)
                     {
                       build = (fun fc -> ConstCube.find args (comp_sface (sface_of_tface fab) fc));
                     }));
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
        FaceCube.build m
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

and apply_binder : type m n f a. m binder -> (m, n) sface -> (n, value) ConstCube.t -> value =
 fun (Bind b) s argstbl ->
  act_value
    (eval
       (env_append b.plus_faces b.env
          (Bwv.map
             (fun ffs ->
               FaceConstCubeMap.map
                 {
                   map =
                     (fun _ (Face_of (Face (fa, fb))) ->
                       act_value (ConstCube.find argstbl (comp_sface s fa)) fb);
                 }
                 ffs)
             b.args))
       b.body)
    b.perm
