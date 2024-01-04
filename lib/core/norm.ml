open Util
open Reporter
open Dim
open Act
open Syntax
open Term
open Value
open Inst
open Bwd
open Monad.Ops (Monad.Maybe)
open Hctx

(* Look up a value in an environment by variable index.  The result has to have a degeneracy action applied (from the actions stored in the environment).  Thus this depends on being able to act on a value by a degeneracy, so we can't define it until after act.ml is loaded (unless we do open recursive trickery). *)
let lookup : type n b. (n, b) env -> b index -> value =
 fun env v ->
  (* We traverse the environment, accumulating operator actions as we go, until we find the specified index. *)
  let rec lookup : type m n b. (n, b) env -> b index -> (m, n) op -> value =
   fun env v op ->
    match (env, v) with
    | Emp _, _ -> .
    | Ext (_, entry), Top fa -> (
        (* When we find our variable, we decompose the accumulated operator into a strict face and degeneracy. *)
        let (Op (f, s)) = op in
        match compare (cod_sface fa) (CubeOf.dim entry) with
        | Eq -> act_value (CubeOf.find (CubeOf.find entry fa) f) s
        | Neq -> fatal (Dimension_mismatch ("lookup", cod_sface fa, CubeOf.dim entry)))
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
                          fatal
                            (Anomaly
                               "evaluation of lower-dimensional constant is not neutral/canonical"));
                })) in
      match Hashtbl.find_opt Global.constants name with
      | Some (Record _) | Some (Data _) -> Uninst (Canonical (name, Emp, zero_ins (dim_env env)), ty)
      | Some Axiom | Some (Defined _) -> apply_spine (Const { name; dim }) Emp ty
      | None -> fatal (Undefined_constant name))
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
      | Neq -> fatal (Dimension_mismatch ("evaluation instantiation", TubeOf.inst tys, mn_k'))
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
  | Lam (n, x, body) -> (
      match compare (dim_env env) D.zero with
      | Eq -> Lam (x, eval_binder env (D.zero_plus n) body)
      | Neq -> (
          let (Plus mn) = D.plus n in
          match x with
          | `Cube x -> Lam (`Cube x, eval_binder env mn body)
          (* TODO: Ideally this could be a "partially-cube" variable. *)
          | `Normal x -> Lam (`Cube (CubeOf.find_top x), eval_binder env mn body)))
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
  | Struct (_, fields) -> Struct (Abwd.map (fun tm -> eval env tm) fields, zero_ins (dim_env env))
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
  | Pi (x, doms, cods) ->
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
                let cod = CodCube.find cods fb in
                eval_binder (Act (env, op_of_sface fa)) k_l cod);
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
      Uninst (Pi (x, doms, cods), lazy (inst (universe m) tys))
  | Let (_, v, body) ->
      let args =
        CubeOf.build (dim_env env) { build = (fun fa -> eval (Act (env, op_of_sface fa)) v) } in
      eval (Ext (env, CubeOf.singleton args)) body
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
  | Lam (_, body) -> (
      let m = CubeOf.dim arg in
      match compare (dim_binder body) m with
      | Neq -> fatal (Dimension_mismatch ("applying a lambda", dim_binder body, m))
      | Eq -> apply_binder body arg)
  (* If it is a neutral application... *)
  | Uninst (tm, (lazy ty)) -> (
      (* ... we check that it is fully instantiated... *)
      let (Fullinst (ty, tyargs)) = full_inst ty "apply" in
      match ty with
      | Pi (_, doms, cods) -> (
          (* ... and that the pi-type and its instantiation have the correct dimension. *)
          let k = CubeOf.dim doms in
          match (compare (TubeOf.inst tyargs) k, compare (CubeOf.dim arg) k) with
          | Neq, _ ->
              fatal (Dimension_mismatch ("applying a neutral function", TubeOf.inst tyargs, k))
          | _, Neq ->
              fatal
                (Dimension_mismatch ("applying a neutral function (arguments)", CubeOf.dim arg, k))
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
                  | _, Neq -> fatal (Dimension_mismatch ("applying canonical", cod_left_ins ins, k))
                  | None, _ -> fatal (Anomaly "insertion mismatch applying canonical"))
              | _ -> fatal (Anomaly "invalid application of non-function uninst")))
      | _ -> fatal (Anomaly "invalid application by non-function"))
  | _ -> fatal (Anomaly "invalid application of non-function")

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
        | None -> fatal (Undefined_constant name))
    | _ -> None)
    (* If it has no case tree, or is not a constant, we just add the argument to the neutral application spine and return. *)
    ~default:(Uninst (Neu (fn, args), ty))

(* Evaluate a case tree, in an environment of variables for which we have already found values, with possible additional arguments.  The degeneracy is one to be applied to the value of the case tree *before* applying it to any additional arguments; thus if it is nonidentity we cannot pick up additional arguments.  Return None if the case tree doesn't apply for any reason (e.g. not enough arguments, or a dispatching argument doesn't match any branch, or there is a nonidentity degeneracy in the way of picking up extra arguments). *)
and apply_tree : type n a. (n, a) env -> a Case.tree -> any_deg -> app list -> value option =
 fun env tree ins args ->
  match tree with
  | Lam (n, _, body) -> (
      (* We fail unless the current insertion is the identity.  TODO: Actually should we allow degeneracies for higher lambdas and behave like degeneracy actions on lambdas?  *)
      let* () = is_id_any_deg ins in
      (* Pick up another argument. *)
      let m = dim_env env in
      let (Plus plus_dim) = D.plus n in
      match args with
      | App (Arg arg, newins) :: args -> (
          match compare (CubeOf.dim arg) (D.plus_out m plus_dim) with
          | Neq ->
              fatal
                (Dimension_mismatch ("applying case tree", CubeOf.dim arg, D.plus_out m plus_dim))
          | Eq ->
              apply_tree
                (Ext
                   ( env,
                     CubeOf.build n
                       {
                         build =
                           (fun fa ->
                             CubeOf.build m
                               {
                                 build =
                                   (fun fb ->
                                     let (Plus plus_dom) = D.plus (dom_sface fa) in
                                     (CubeOf.find arg (sface_plus_sface fb plus_dim plus_dom fa)).tm);
                               });
                       } ))
                !body
                (Any (perm_of_ins newins))
                args)
      | _ -> None)
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
  | Branches (ix, n, branches) -> (
      (* Get the argument being inspected *)
      let m = dim_env env in
      match lookup env ix with
      (* It must be an application of a constructor *)
      | Constr (name, dim, dargs) -> (
          match Constr.Map.find_opt name branches with
          (* Matches are constructed to contain all the constructors of the datatype being matched on, and this constructor belongs to that datatype, so it ought to be in the match. *)
          | None -> fatal (Anomaly "constructor missing from compiled match")
          | Some (Branch (plus, body)) -> (
              let (Plus mn) = D.plus n in
              match compare dim (D.plus_out m mn) with
              | Eq ->
                  (* If we have a branch with a matching constant, then in the argument the constant must be applied to exactly the right number of elements (in dargs).  In that case, we pick them out and add them to the environment. *)
                  let env = take_args env mn dargs plus in
                  (* Then we proceed recursively with the body of that branch. *)
                  apply_tree env !body ins args
              | _ -> None))
      | _ -> None)
  | Cobranches cobranches -> (
      (* A cobranch can only succeed if there is a field projection to match against occurring next in the spine. *)
      match args with
      | App (Field fld, new_ins) :: args ->
          (* This also requires the degeneracy to be the identity. *)
          let* () = is_id_any_deg ins in
          let* body = Abwd.find_opt fld cobranches in
          apply_tree env !body (Any (perm_of_ins new_ins)) args
      | _ -> None)
  | Empty -> None

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
  inst (apply_binder (BindCube.find_top cods) args) out_args

(* Compute a field of a structure, at a particular dimension. *)
and field : value -> Field.t -> value =
 fun tm fld ->
  match tm with
  (* TODO: Is it okay to ignore the insertion here? *)
  | Struct (fields, _) -> Abwd.find fld fields
  | Uninst (Neu (fn, args), (lazy ty)) ->
      let newty = lazy (tyof_field tm ty fld) in
      (* The D.zero here isn't really right, but since it's the identity permutation anyway I don't think it matters? *)
      apply_spine fn (Snoc (args, App (Field fld, zero_ins D.zero))) newty
  | _ -> fatal ~severity:Asai.Diagnostic.Bug (No_such_field (`Other, fld))

(* Given a term and its record type, compute the type of a field projection.  The caller can control the severity of errors, depending on whether we're typechecking (Error) or normalizing (Bug, the default). *)
and tyof_field ?severity (tm : value) (ty : value) (fld : Field.t) : value =
  let (Fullinst (ty, tyargs)) = full_inst ?severity ty "tyof_field" in
  match ty with
  | Canonical (name, args, ins) -> (
      (* The head of the type must be a record type with a field having the correct name. *)
      let (Field { params = kc; dim = n; ty = fldty }) =
        Global.find_record_field ?severity name fld in
      (* The total dimension of the record type is the dimension (m) at which the constant is applied, plus the intrinsic dimension of the record (n).  It must therefore be (fully) instantiated at that dimension m+n.  *)
      let (Plus mn) = D.plus n in
      let m = cod_left_ins ins in
      let mn' = D.plus_out m mn in
      match compare (TubeOf.inst tyargs) mn' with
      | Neq ->
          fatal ?severity (Dimension_mismatch ("computing type of field", TubeOf.inst tyargs, mn'))
      | Eq ->
          (* The type must be applied, at dimension m, to exactly the right number of parameters (k). *)
          let env, Emp = take_canonical_args (Emp m) args kc N.zero in
          (* If so, then the type of the field projection comes from the type associated to that field name in general, evaluated at the supplied parameters along with the term itself and its boundaries. *)
          let tyargs' = TubeOf.plus_cube (val_of_norm_tube tyargs) (CubeOf.singleton tm) in
          let entries =
            CubeOf.build n
              {
                build =
                  (fun fb ->
                    CubeOf.build m
                      {
                        build =
                          (fun fa ->
                            let (Plus pq) = D.plus (dom_sface fb) in
                            CubeOf.find tyargs' (sface_plus_sface fa mn pq fb));
                      });
              } in
          let env = Value.Ext (env, entries) in
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
  | _ -> fatal ?severity (No_such_field (`Other, fld))

and eval_binder :
    type m n mn b. (m, b) env -> (m, n, mn) D.plus -> (b, n) ext term -> mn Value.binder =
 fun env plus_dim body ->
  let n = D.plus_right plus_dim in
  let m = dim_env env in
  let args =
    CubeOf.build n
      {
        build =
          (fun fa ->
            CubeOf.build m
              {
                build =
                  (fun fb ->
                    let (Plus plus_dom) = D.plus (dom_sface fa) in
                    Face_of
                      (Face
                         ( sface_plus_sface fb plus_dim plus_dom fa,
                           id_perm (D.plus_out (dom_sface fb) plus_dom) )));
              });
      } in
  let perm = id_perm (D.plus_out m plus_dim) in
  Value.Bind { env; perm; plus_dim; body; args }

and apply_binder : type n. n Value.binder -> (n, value) CubeOf.t -> value =
 fun (Value.Bind b) argstbl ->
  act_value
    (eval
       (Ext
          ( b.env,
            CubeOf.mmap
              {
                map =
                  (fun _ [ ffs ] ->
                    CubeOf.mmap
                      {
                        map =
                          (fun _ [ Face_of (Face (fa, fb)) ] ->
                            act_value (CubeOf.find argstbl fa) fb);
                      }
                      [ ffs ]);
              }
              [ b.args ] ))
       b.body)
    b.perm
