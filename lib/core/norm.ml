open Util
open Logger
open Dim
open Value
open Act
open Term
open Bwd
open Monad.Ops (Monad.Maybe)

(* Look up a value in an environment by variable index.  The result has to have a degeneracy action applied (from the actions stored in the environment).  Thus this depends on being able to act on a value by a degeneracy, so we can't define it until after act.ml is loaded (unless we do open recursive trickery). *)
let lookup : type n b. (n, b) env -> b N.index -> value =
 fun env v ->
  (* We traverse the environment, accumulating operator actions as we go, until we find the specified index. *)
  let rec lookup : type m n b. (n, b) env -> b N.index -> (m, n) op -> value =
   fun env v op ->
    match (env, v) with
    | Emp _, _ -> .
    | Ext (_, entry), Top ->
        (* When we find our variable, we decompose the accumulated operator into a strict face and degeneracy. *)
        let (Op (f, s)) = op in
        act_value (CubeOf.find entry f) s
    | Ext (env, _), Pop v -> lookup env v op
    | Act (env, op'), _ -> lookup env v (comp_op op' op) in
  lookup env v (id_op (dim_env env))

(* The master evaluation function. *)
let rec eval : type m b. (m, b) env -> b term -> value =
 fun env tm ->
  match tm with
  | Var v -> lookup env v
  | Const name -> (
      (* A constant starts out at dimension zero, but must be lifted to the dimension of the environment. *)
      let dim = dim_env env in
      let cty = Hashtbl.find Global.types name in
      (* Its type must also be instantiated at the lower-dimensional versions of itself. *)
      let ty =
        lazy
          (inst (eval (Emp dim) cty)
             (TubeOf.build D.zero (D.zero_plus dim)
                {
                  build =
                    (fun fa ->
                      (* To compute those lower-dimensional versions, we recursively evaluate the same constant in lower-dimensional contexts. *)
                      let tm = eval (Act (env, op_of_sface (sface_of_tface fa))) (Const name) in
                      (* We need to know the type of each lower-dimensional version in order to annotate it as a "normal" instantiation argument.  But we already computed that type while evaluating the term itself, since as a normal term it had to be annotated with its type. *)
                      match tm with
                      | Uninst (Neu _, (lazy ty)) | Uninst (Canonical _, (lazy ty)) -> { tm; ty }
                      | _ ->
                          die Anomaly
                            "Evaluation of lower-dimensional constant is not neutral/canonical");
                })) in
      match Hashtbl.find_opt Global.constants name with
      | Some (Record _) | Some (Data _) -> Uninst (Canonical (name, Emp, zero_ins (dim_env env)), ty)
      | Some Axiom | Some (Defined _) -> apply_spine (Const { name; dim }) Emp ty
      | None -> die ~severity:Asai.Diagnostic.Bug Unbound_variable name)
  | UU n ->
      let m = dim_env env in
      let (Plus mn) = D.plus n in
      universe (D.plus_out m mn)
  | Inst (tm, args) -> (
      let nk = TubeOf.plus args in
      (* Add the environment dimension to the uninstantiated dimensions *)
      let m = dim_env env in
      let (Plus mn) = D.plus (TubeOf.uninst args) in
      let mn' = D.plus_out m mn in
      (* Evaluate the inner term *)
      let newtm = eval env tm in
      (* Evaluate the arguments, rearranging and acting by faces and degeneracies *)
      let (Plus mn_k) = D.plus (D.plus_right nk) in
      let mn_k' = D.plus_out mn' mn_k in
      (* tys is a complete m+n+k tube *)
      let (Inst_tys tys) = inst_tys newtm in
      match compare (TubeOf.inst tys) mn_k' with
      | Neq -> die Dimension_mismatch ("evaluation instantiation", TubeOf.inst tys, mn_k')
      | Eq ->
          (* used_tys is an m+n+k tube with m+n uninstantiated and k instantiated.  These are the types that we must instantiate to give the types of the added instantiation arguments. *)
          let used_tys = TubeOf.pboundary (D.zero_plus mn') mn_k tys in
          let newargstbl = Hashtbl.create 10 in
          let newargs =
            TubeOf.mmap
              {
                map =
                  (fun fa [ ty ] ->
                    (* fa : p+q => m+n+k, fa = fb+fc where fb : p => m and fcd : q => n+k. *)
                    let (TFace_of_plus (pq, fb, fcd)) = tface_of_plus mn fa in
                    let fa = sface_of_tface fa in
                    let p = dom_sface fb in
                    let pq' = D.plus_out p pq in
                    let Eq = D.plus_uniq (cod_plus_of_tface fcd) nk in
                    (* Thus tm is p+q dimensional. *)
                    let tm = eval (Act (env, op_of_sface fb)) (TubeOf.find args fcd) in
                    (* So its type needs to be fully instantiated at that dimension. *)
                    let ty =
                      inst ty
                        (TubeOf.build D.zero (D.zero_plus pq')
                           {
                             build =
                               (fun fij ->
                                 let faij = comp_sface fa (sface_of_tface fij) in
                                 Hashtbl.find newargstbl (SFace_of faij));
                           }) in
                    let v = { tm; ty } in
                    Hashtbl.add newargstbl (SFace_of fa) v;
                    v);
              }
              [ used_tys ] in
          (* The types not in used_tys form a complete m+n tube, which will be the remaining instantiation arguments of the type of the result.  We don't need to worry about that here, it's taken care of in "inst". *)
          inst newtm newargs)
  | Lam (Bind (n_faces, plus_n_faces, body)) ->
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
  | Field (tm, fld) ->
      let etm = eval env tm in
      field etm fld
  | Struct fields -> Struct (Field.Map.map (fun tm -> eval env tm) fields, zero_ins (dim_env env))
  | Constr (constr, n, args) ->
      let m = dim_env env in
      let (Plus m_n) = D.plus n in
      let mn = D.plus_out m m_n in
      let eargs =
        Bwd.map
          (fun tms ->
            CubeOf.build mn
              {
                build =
                  (fun fab ->
                    let (SFace_of_plus (_, fa, fb)) = sface_of_plus m_n fab in
                    eval (Act (env, op_of_sface fa)) (CubeOf.find tms fb));
              })
          args in
      Constr (constr, mn, eargs)
  | Pi (doms, cods) ->
      let n = CubeOf.dim doms in
      let m = dim_env env in
      let (Plus m_n) = D.plus n in
      let mn = D.plus_out m m_n in
      let doms =
        CubeOf.build mn
          {
            build =
              (fun fab ->
                let (SFace_of_plus (_, fa, fb)) = sface_of_plus m_n fab in
                eval (Act (env, op_of_sface fa)) (CubeOf.find doms fb));
          } in
      let cods =
        BindCube.build mn
          {
            build =
              (fun fab ->
                let (SFace_of_plus (k_l, fa, fb)) = sface_of_plus m_n fab in
                let (Bind (lf, nlf, cod)) = CodCube.find cods fb in
                eval_binder (Act (env, op_of_sface fa)) lf k_l nlf cod);
          } in
      let tytbl = Hashtbl.create 10 in
      let tys =
        TubeOf.build D.zero (D.zero_plus m)
          {
            build =
              (fun fa ->
                let k = dom_tface fa in
                let fa = sface_of_tface fa in
                let tm = eval (Act (env, op_of_sface fa)) tm in
                let ty =
                  inst (universe k)
                    (TubeOf.build D.zero (D.zero_plus k)
                       {
                         build =
                           (fun fb ->
                             Hashtbl.find tytbl (SFace_of (comp_sface fa (sface_of_tface fb))));
                       }) in
                let ntm = { tm; ty } in
                Hashtbl.add tytbl (SFace_of fa) ntm;
                ntm);
          } in
      Uninst (Pi (doms, cods), lazy (inst (universe m) tys))
  | Let (v, body) ->
      let args =
        CubeOf.build (dim_env env) { build = (fun fa -> eval (Act (env, op_of_sface fa)) v) } in
      eval (Ext (env, args)) body
  (* It's tempting to write just "act_value (eval env x) s" here, but that is WRONG!  Pushing a substitution through an operator action requires whiskering the operator by the dimension of the substitution. *)
  | Act (x, s) ->
      let k = dim_env env in
      let (Plus km) = D.plus (dom_deg s) in
      let (Plus kn) = D.plus (cod_deg s) in
      let ks = plus_deg k kn km s in
      act_value (eval env x) ks

(* Apply a function value to an argument (with its boundaries). *)
and apply : type n. value -> (n, value) CubeOf.t -> value =
 fun fn arg ->
  match fn with
  (* If the function is a lambda-abstraction, we check that it has the correct dimension and then beta-reduce, adding the arguments to the environment. *)
  | Lam body -> (
      let m = CubeOf.dim arg in
      match compare (dim_binder body) m with
      | Neq -> die Dimension_mismatch ("applying a lambda", dim_binder body, m)
      | Eq -> apply_binder body arg)
  (* If it is a neutral application... *)
  | Uninst (tm, (lazy ty)) -> (
      (* ... we check that it is fully instantiated... *)
      let (Fullinst (ty, tyargs)) = full_inst ty "apply" in
      match ty with
      | Pi (doms, cods) -> (
          (* ... and that the pi-type and its instantiation have the correct dimension. *)
          let k = CubeOf.dim doms in
          match (compare (TubeOf.inst tyargs) k, compare (CubeOf.dim arg) k) with
          | Neq, _ -> die Dimension_mismatch ("applying a neutral function", TubeOf.inst tyargs, k)
          | _, Neq ->
              die Dimension_mismatch ("applying a neutral function (arguments)", CubeOf.dim arg, k)
          | Eq, Eq -> (
              (* We annotate the new argument by its type, extracted from the domain type of the function being applied. *)
              let newarg = norm_of_vals arg doms in
              (* We compute the output type of the application. *)
              let ty = lazy (tyof_app cods tyargs arg) in
              (* Then we add the new argument to the existing application spine, and possibly evaluate further with a case tree. *)
              match tm with
              | Neu (fn, args) -> apply_spine fn (Snoc (args, App (Arg newarg, zero_ins k))) ty
              | Canonical (name, prev_args, ins) -> (
                  match (is_id_perm (perm_of_ins ins), compare (cod_left_ins ins) k) with
                  | Some (), Eq -> Uninst (Canonical (name, Snoc (prev_args, newarg), ins), ty)
                  | _, Neq -> die Dimension_mismatch ("applying canonical", cod_left_ins ins, k)
                  | None, _ -> die Anomaly "Insertion mismatch applying canonical")
              | _ -> die Anomaly "Invalid application of non-function uninst"))
      | _ -> die Anomaly "Invalid application by non-function")
  | _ -> die Anomaly "Invalid application of non-function"

(* Compute the application of a head to a spine of arguments (including field projections), using a case tree for a head constant if possible, otherwise just constructing a neutral application.  We have to be given the overall type of the application, so that we can annotate the latter case. *)
and apply_spine : head -> app Bwd.t -> value Lazy.t -> value =
 fun fn args ty ->
  (* Check whether the head is a constant with an associated case tree. *)
  Option.value
    (match fn with
    | Const { name; dim } -> (
        match Hashtbl.find_opt Global.constants name with
        | Some (Defined tree) -> apply_tree (Emp dim) !tree (Any (id_deg dim)) (Bwd.prepend args [])
        | Some _ -> None
        | None -> die ~severity:Asai.Diagnostic.Bug Unbound_variable name)
    | _ -> None)
    (* If it has no case tree, or is not a constant, we just add the argument to the neutral application spine and return. *)
    ~default:(Uninst (Neu (fn, args), ty))

(* Evaluate a case tree, in an environment of variables for which we have already found values, with possible additional arguments.  The degeneracy is one to be applied to the value of the case tree *before* applying it to any additional arguments; thus if it is nonidentity we cannot pick up additional arguments.  Return None if the case tree doesn't apply for any reason (e.g. not enough arguments, or a dispatching argument doesn't match any branch, or there is a nonidentity degeneracy in the way of picking up extra arguments). *)
and apply_tree : type n a. (n, a) env -> a Case.tree -> any_deg -> app list -> value option =
 fun env tree ins args ->
  match tree with
  | Lam body ->
      (* Pick up another argument.  Note that this fails if ins is nonidentity. *)
      let* newenv, newins, newargs = take_lam_arg env ins args in
      apply_tree newenv !body newins newargs
  | Leaf body ->
      (* We've found a term to evaluate *)
      let res = act_any (eval env body) ins in
      (* Now apply this to any remaining arguments. *)
      Some
        (List.fold_left
           (fun f (Value.App (a, i)) ->
             act_value
               (match a with
               | Arg arg -> apply f (val_of_norm_cube arg)
               | Field fld -> field f fld)
               (perm_of_ins i))
           res args)
  | Branches (ix, branches) -> (
      (* Get the argument being inspected *)
      match lookup env ix with
      (* It must be an application of a constructor *)
      | Constr (name, dim, dargs) -> (
          (* A case tree can only include 0-dimensional applications, so the dimension here must match the dimension we're using it at. *)
          match compare dim (dim_env env) with
          | Eq ->
              let* (Branch (plus, body)) = Constr.Map.find_opt name branches in
              (* If we have a branch with a matching constant, then in the argument the constant must be applied to exactly the right number of elements (in dargs).  In that case, we pick out a possibly-smaller number of them (determined by a subset) and add them to the environment. *)
              let env = take_args env dargs plus in
              (* Then we proceed recursively with the body of that branch. *)
              apply_tree env !body ins args
          | _ -> None)
      | _ -> None)
  | Cobranches cobranches -> (
      (* A cobranch can only succeed if there is a field projection to match against occurring next in the spine. *)
      match args with
      | App (Field fld, new_ins) :: args ->
          (* This also requires the degeneracy to be the identity. *)
          let* () = is_id_any_deg ins in
          let* body = Field.Map.find_opt fld cobranches in
          apply_tree env !body (Any (perm_of_ins new_ins)) args
      | _ -> None)
  | Empty -> None

and take_lam_arg :
    type n a. (n, a) env -> any_deg -> app list -> ((n, a N.suc) env * any_deg * app list) option =
 fun env ins args ->
  match args with
  | App (Arg arg, newins) :: args -> (
      (* We fail unless the current insertion is the identity.  In addition, the variables bound in a case tree are always zero-dimensional applications, so the apps here must all be the same dimension as the constant instance. *)
      match (is_id_any_deg ins, compare (dim_env env) (CubeOf.dim arg)) with
      | Some (), Eq -> Some (Ext (env, val_of_norm_cube arg), Any (perm_of_ins newins), args)
      | _ -> None)
  | _ -> None

(* Compute the output type of a function application, given the codomains and instantiation arguments of the pi-type (the latter being the functions acting on the boundary) and the arguments it is applied to. *)
and tyof_app :
    type k. (k, unit) BindCube.t -> (D.zero, k, k, normal) TubeOf.t -> (k, value) CubeOf.t -> value
    =
 fun cods fns args ->
  let out_arg_tbl = Hashtbl.create 10 in
  let out_args =
    TubeOf.mmap
      {
        map =
          (fun fa [ { tm = afn; ty = _ } ] ->
            let fa = sface_of_tface fa in
            let tmargs = CubeOf.subcube fa args in
            let tm = apply afn tmargs in
            let ty =
              inst
                (apply_binder (BindCube.find cods fa) tmargs)
                (TubeOf.build D.zero
                   (D.zero_plus (dom_sface fa))
                   {
                     build =
                       (fun fc ->
                         Hashtbl.find out_arg_tbl (SFace_of (comp_sface fa (sface_of_tface fc))));
                   }) in
            let out_tm = { tm; ty } in
            Hashtbl.add out_arg_tbl (SFace_of fa) out_tm;
            out_tm);
      }
      [ fns ] in
  inst (apply_binder (BindCube.find cods (id_sface (CubeOf.dim args))) args) out_args

(* Compute a field of a structure, at a particular dimension. *)
and field : value -> Field.t -> value =
 fun tm fld ->
  match tm with
  | Struct (fields, _) -> Field.Map.find fld fields
  | Uninst (Neu (fn, args), (lazy ty)) ->
      let newty = lazy (tyof_field tm ty fld) in
      (* The D.zero here isn't really right, but since it's the identity permutation anyway I don't think it matters? *)
      apply_spine fn (Snoc (args, App (Field fld, zero_ins D.zero))) newty
  | _ -> die ~severity:Asai.Diagnostic.Bug No_such_field (None, fld)

(* Given a term and its record type, compute the type of a field projection.  The caller can control the severity of errors, depending on whether we're typechecking (Error) or normalizing (Bug, the default). *)
and tyof_field ?severity (tm : value) (ty : value) (fld : Field.t) : value =
  let (Fullinst (ty, tyargs)) = full_inst ?severity ty "tyof_field" in
  match ty with
  | Canonical (name, args, ins) -> (
      (* The head of the type must be a record type with a field having the correct name. *)
      let (Field { params = k; dim = n; dim_faces = nf; params_plus = kf; ty = fldty }) =
        Global.find_record_field ?severity name fld in
      (* The total dimension of the record type is the dimension (m) at which the constant is applied, plus the intrinsic dimension of the record (n).  It must therefore be (fully) instantiated at that dimension m+n.  *)
      let (Plus mn) = D.plus n in
      let m = cod_left_ins ins in
      let mn' = D.plus_out m mn in
      match compare (TubeOf.inst tyargs) mn' with
      | Neq -> die ?severity Dimension_mismatch ("computing type of field", TubeOf.inst tyargs, mn')
      | Eq ->
          (* The type must be applied, at dimension m, to exactly the right number of parameters (k). *)
          let env, Emp = take_canonical_args (Emp m) args (N.zero_plus k) Zero in
          (* If so, then the type of the field projection comes from the type associated to that field name in general, evaluated at the supplied parameters along with the term itself and its boundaries. *)
          let tyargs' = TubeOf.plus_cube (val_of_norm_tube tyargs) (CubeOf.singleton tm) in
          let entries =
            Bwv.map
              (fun (SFace_of fb) ->
                CubeOf.build m
                  {
                    build =
                      (fun fa ->
                        let (Plus pq) = D.plus (dom_sface fb) in
                        CubeOf.find tyargs' (sface_plus_sface fa mn pq fb));
                  })
              (sfaces nf) in
          let env = env_append kf env entries in
          (* This type is m-dimensional, hence must be instantiated at a full m-tube. *)
          inst (eval env fldty)
            (TubeOf.mmap
               {
                 map =
                   (fun _ [ arg ] ->
                     let tm = field arg.tm fld in
                     let ty = tyof_field arg.tm arg.ty fld in
                     { tm; ty });
               }
               [ TubeOf.middle (D.zero_plus m) mn tyargs ]))
  | _ -> die ?severity No_such_field (None, fld)

and eval_binder :
    type m n mn b f bf.
    (m, b) env ->
    (n, f) count_faces ->
    (m, n, mn) D.plus ->
    (b, f, bf) N.plus ->
    bf term ->
    mn Value.binder =
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
  Value.Bind { env; perm; plus_dim; bound_faces; plus_faces; body; args }

and apply_binder : type n. n Value.binder -> (n, value) CubeOf.t -> value =
 fun (Value.Bind b) argstbl ->
  act_value
    (eval
       (env_append b.plus_faces b.env
          (Bwv.map
             (fun ffs ->
               CubeOf.mmap
                 {
                   map =
                     (fun _ [ Face_of (Face (fa, fb)) ] -> act_value (CubeOf.find argstbl fa) fb);
                 }
                 [ ffs ])
             b.args))
       b.body)
    b.perm
