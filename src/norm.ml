open Dim
open Value
open Act
open Term

let rec eval : type m b. (m, b) env -> b term -> value =
 fun env tm ->
  match tm with
  | Var v -> lookup act_any env v
  | UU -> Uninst (UU (dim_env env))
  | Inst (tm, tube, args) ->
      let (Tube t) = tube in
      let nk = t.plus_dim in
      (* Add the environment dimension to the uninstantiated dimensions *)
      let (Plus mn) = D.plus (tube_uninst tube) in
      let (Has_tube newtube) = has_tube (D.plus_out (dim_env env) mn) (D.plus_right nk) in
      let (Tube newt) = newtube in
      let mn_k = newt.plus_dim in
      let m_nk = D.plus_assocr mn nk mn_k in
      (* Collate the supplied arguments into a hashtable for random access *)
      let argtbl = Hashtbl.create 10 in
      let () = Bwv.iter2_plus t.plus_faces (Hashtbl.add argtbl) (sfaces t.total_faces) args in
      (* Evaluate the inner term *)
      let newtm = eval env tm in
      (* Evaluate the arguments, rearranging and acting by faces and degeneracies *)
      let newargs =
        Bwv.map_plus newt.plus_faces
          (fun (SFace_of fa) ->
            let (SFace_of_plus (_, fb, fcd)) = sface_of_plus m_nk fa in
            eval (Act (env, op_of_sface fb)) (Hashtbl.find argtbl (SFace_of fcd)))
          (sfaces newt.total_faces) in
      inst newtm newtube newargs
  | Lam (n_faces, plus_n_faces, body) ->
      let (Plus mn) = D.plus (dim_faces n_faces) in
      Lam (eval_binder env n_faces mn plus_n_faces body)
  | App (fn, n_faces, args) ->
      (* First we evaluate the function. *)
      let fn = eval env fn in
      (* The environment is m-dimensional and the original application is n-dimensional, so the *substituted* application is m+n dimensional.  Thus must therefore match the dimension of the function being applied. *)
      let m = dim_env env in
      let n = dim_faces n_faces in
      let (Plus m_n) = D.plus n in
      let mn = D.plus_out m m_n in
      let (Faces mn_faces) = count_faces mn in
      (* We collect the supplied arguments in a hashtable for random access. *)
      let ntbl = Hashtbl.create 10 in
      let () = Bwv.iter2 (Hashtbl.add ntbl) (sfaces n_faces) args in
      (* Then we evaluate them all, not just in the given environment (of dimension m), but in that environment acted on by all the strict faces of m.  Since the given arguments are indexed by strict faces of n, the result is a collection of values indexed by strict faces of m+n.  *)
      let mntbl = Hashtbl.create 10 in
      let () =
        Bwv.iter
          (* Specifically, for each face of m+n... *)
            (fun (SFace_of fab) ->
            (* ...we decompose it as a sum of a face "fa" of m and a face "fb" of n... *)
            let (SFace_of_plus (_, fa, fb)) = sface_of_plus m_n fab in
            (* ...and evaluate the supplied argument indexed by the face fb of n, in an environment acted on by the face fa of m. *)
            Hashtbl.add mntbl (SFace_of fab)
              (eval (Act (env, op_of_sface fa)) (Hashtbl.find ntbl (SFace_of fb))))
          (sfaces mn_faces) in
      (* Having evaluated the function and its arguments, we now pass the job off to a helper function. *)
      apply fn mn mntbl
  | Pi (dom, cod) ->
      (* A user-space pi-type always has dimension zero, so this is simpler than the general case. *)
      let m = dim_env env in
      let (Faces dom_faces) = count_faces m in
      let doms =
        Bwv.map (fun (SFace_of fa) -> eval (Act (env, op_of_sface fa)) dom) (sfaces dom_faces) in
      let cods' =
        BindTree.build m
          {
            leaf =
              (fun fa ->
                eval_binder
                  (Act (env, op_of_sface fa))
                  faces_zero
                  (D.plus_zero (dom_sface fa))
                  (Suc Zero) cod);
          } in
      Uninst (Pi (dom_faces, doms, cods'))
  | Refl x -> act_value (eval env x) refl
  | Sym x -> act_value (eval env x) sym
  | Id (a, x, y) ->
      let x = eval env x in
      let y = eval env y in
      inst (act_value (eval env a) refl) tube_one (Snoc (Snoc (Bwv.Emp, x), y))

and apply : type n f. value -> n D.t -> (n sface_of, value) Hashtbl.t -> value =
 fun fn mn mntbl ->
  match fn with
  (* If the function is a lambda-abstraction, we beta-reduce, adding the above-computed arguments to the environment. *)
  | Lam body -> (
      (* First we check that it has the correct dimension. *)
      match compare (dim_binder body) mn with
      | Neq -> raise (Failure "Dimension mismatch applying a lambda")
      | Eq -> apply_binder body (id_sface mn) mntbl)
  (* If the function is a neutral function, either zero-dimensional or higher-dimensional with instantiated type, we create a new neutral application. *)
  | Uninst (Neu (fn, Inst { tm; dim = _; tube; args })) -> apply_neu fn tm tube args mn mntbl
  | Uninst (Neu (fn, Uninst tm)) -> apply_neu fn tm tube_zero Emp mn mntbl
  | _ -> raise (Failure "Invalid application of non-function")

and apply_neu :
    type n f a b g.
    neu ->
    uninst ->
    (a, b, g) count_tube ->
    (value, g) Bwv.t ->
    n D.t ->
    (n sface_of, value) Hashtbl.t ->
    value =
 fun fn tm pi_tube pi_args mn mntbl ->
  match tm with
  | Pi (app_faces, doms, cods) -> (
      (* We check that the pi-type has the correct dimension, is fully instantiated, and has the correct dimension of instantiation. *)
      match
        ( compare (dim_faces app_faces) mn,
          compare (tube_uninst pi_tube) D.zero,
          compare (tube_inst pi_tube) mn )
      with
      | Neq, _, _ -> raise (Failure "Function-type dimension mismatch applying a neutral function")
      | _, Neq, _ -> raise (Failure "Application of non-fully-instantiated function")
      | _, _, Neq -> raise (Failure "Instantiation mismatch applying a neutral function")
      | Eq, Eq, Eq ->
          let (Tube pt) = pi_tube in
          let Eq = D.plus_uniq pt.plus_dim (D.zero_plus mn) in
          let Eq = faces_uniq pt.total_faces app_faces in
          let Eq = faces_uniq pt.missing_faces faces_zero in
          let Eq = N.plus_uniq pt.plus_faces (Suc Zero) in
          let mnf = sfaces app_faces in
          (* In this case, the arguments must be normals rather than values.  Thus, while collecting them into a Bwv, we also compute their types from the domain types of the function-type, instantiated at previous arguments. *)
          let args =
            Bwv.map2
              (fun (SFace_of fab) dom ->
                let tm = Hashtbl.find mntbl (SFace_of fab) in
                let k = dom_sface fab in
                let (Has_tube (Tube t)) = has_tube D.zero k in
                let Eq = D.plus_uniq t.plus_dim (D.zero_plus k) in
                let ty =
                  inst dom (Tube t)
                    (Bwv.map_plus t.plus_faces
                       (fun (SFace_of fc) -> Hashtbl.find mntbl (SFace_of (comp_sface fab fc)))
                       (sfaces t.total_faces)) in
                { tm; ty })
              mnf doms in
          (* The output type substitutes the arguments into the codomain of the function-type, and instantiates at the values of the boundary functions applied to appropriate ones of these arguments.  This loop is very similar to the previous one, so perhaps they could be combined. *)
          let out_args =
            Bwv.map2_plus pt.plus_faces
              (fun (SFace_of fab) afn ->
                let k = dom_sface fab in
                let (Faces k_faces) = count_faces k in
                let afntbl = Hashtbl.create 10 in
                let () =
                  Bwv.iter
                    (fun (SFace_of fc) ->
                      Hashtbl.add afntbl (SFace_of fc)
                        (Hashtbl.find mntbl (SFace_of (comp_sface fab fc))))
                    (sfaces k_faces) in
                apply afn (dom_sface fab) afntbl)
              mnf pi_args in
          let idf = id_sface mn in
          let output = inst (apply_binder (BindTree.nth cods idf) idf mntbl) pi_tube out_args in
          (* Finally we assemble a new neutral application with these arguments, with a trivial outer insertion, and with the calculated type. *)
          Uninst (Neu (App { fn; app_faces; args; ins = zero_ins mn }, output)))
  | _ -> raise (Failure "Invalid application of non-function")

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
  let (Faces env_faces) = count_faces m in
  let mf = sfaces env_faces in
  let nf = sfaces bound_faces in
  let args =
    Bwv.map
      (fun (SFace_of fa) ->
        Bwv.map
          (fun (SFace_of fb) ->
            let (Plus plus_dom) = D.plus (dom_sface fa) in
            Face_of
              (Face
                 ( sface_plus_sface fb plus_dim plus_dom fa,
                   id_perm (D.plus_out (dom_sface fb) plus_dom) )))
          mf)
      nf in
  let perm = id_perm (D.plus_out m plus_dim) in
  Bind { env; perm; plus_dim; bound_faces; plus_faces; body; env_faces; args }

and apply_binder : type m n f a. m binder -> (m, n) sface -> (n sface_of, value) Hashtbl.t -> value
    =
 fun (Bind b) s argstbl ->
  act_value
    (eval
       (env_append b.plus_faces b.env
          (Bwv.map
             (fun ffs ->
               let tbl = Hashtbl.create 10 in
               let () =
                 Bwv.iter2
                   (fun fc (Face_of (Face (fa, fb))) ->
                     Hashtbl.add tbl fc
                       (act_value (Hashtbl.find argstbl (SFace_of (comp_sface s fa))) fb))
                   (sfaces b.env_faces) ffs in
               tbl)
             b.args))
       b.body)
    b.perm
