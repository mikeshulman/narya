open Bwd
open Util
open Tbwd
open Reporter
open Dim
open Syntax
open Term
open Value
open Inst
open Act
open Permute

(* Evaluation of terms and evaluation of case trees are technically separate things.  In particular, evaluating a kinetic (standard) term always produces just a value, whereas evaluating a potential term (a function case tree) can either

   1. Produce a new partially-evaluated case tree that isn't fully applied yet.  This is actually represented by a value that's either a Lam or a Struct.
   2. Reach a leaf and produce a value.
   3. Conclude that the case tree is true neutral and will never reduce further.

   These possibilities are encoded in an "evaluation", defined in Syntax.Value.  The point is that, just as with the representation of terms, there is enough commonality between the two (application of lambdas and field projection from structs) that we don't want to duplicate the code, so we define the evaluation functions to return an "evaluation" result that is a GADT parametrized by the kind of energy of the term. *)

(* Look up a value in an environment by variable index.  The result has to have a degeneracy action applied (from the actions stored in the environment).  Thus this depends on being able to act on a value by a degeneracy, so we can't define it until after act.ml is loaded (unless we do open recursive trickery). *)
let lookup : type n b. (n, b) env -> b index -> kinetic value =
 fun env v ->
  (* We traverse the environment, accumulating operator actions as we go, until we find the specified index. *)
  let rec lookup : type m n b. (n, b) env -> b index -> (m, n) op -> kinetic value =
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
let rec eval : type m b s. (m, b) env -> (b, s) term -> s evaluation =
 fun env tm ->
  match tm with
  | Var v -> Val (lookup env v)
  | Const name -> (
      let dim = dim_env env in
      let cty =
        match Global.find_type_opt name with
        | Some cty -> cty
        | None -> fatal (Undefined_constant (PConstant name)) in
      (* Its type must also be instantiated at the lower-dimensional versions of itself. *)
      let ty =
        lazy
          (inst (eval_term (Emp dim) cty)
             (TubeOf.build D.zero (D.zero_plus dim)
                {
                  build =
                    (fun fa ->
                      (* To compute those lower-dimensional versions, we recursively evaluate the same constant in lower-dimensional contexts. *)
                      let (Val tm) =
                        eval (Act (env, op_of_sface (sface_of_tface fa))) (Const name) in
                      (* We need to know the type of each lower-dimensional version in order to annotate it as a "normal" instantiation argument.  But we already computed that type while evaluating the term itself, since as a normal term it had to be annotated with its type. *)
                      match tm with
                      | Uninst (Neu _, (lazy ty)) -> { tm; ty }
                      | _ -> fatal (Anomaly "eval of lower-dim constant not neutral/canonical"));
                })) in
      let head = Const { name; ins = ins_zero dim } in
      match Global.find_definition_opt name with
      | Some (Defined tree) -> (
          match eval (Emp dim) tree with
          | Realize x -> Val x
          | Val x -> Val (Uninst (Neu { head; args = Emp; alignment = Chaotic x }, ty))
          | Canonical c -> Val (Uninst (Neu { head; args = Emp; alignment = Lawful c }, ty))
          (* Since a top-level case tree is in the empty context, it doesn't have't anything to stuck-match against. *)
          | Unrealized -> fatal (Anomaly "true neutral case tree in empty context"))
      | Some _ -> Val (Uninst (Neu { head; args = Emp; alignment = True }, ty))
      | None -> fatal (Undefined_constant (PConstant name)))
  | UU n ->
      let m = dim_env env in
      let (Plus mn) = D.plus n in
      Val (universe (D.plus_out m mn))
  | Inst (tm, args) -> (
      let nk = TubeOf.plus args in
      (* Add the environment dimension to the uninstantiated dimensions *)
      let m = dim_env env in
      let (Plus mn) = D.plus (TubeOf.uninst args) in
      let mn' = D.plus_out m mn in
      (* Evaluate the inner term *)
      let newtm = eval_term env tm in
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
                    let (Val tm) = eval (Act (env, op_of_sface fb)) (TubeOf.find args fcd) in
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
          Val (inst newtm newargs))
  | Lam (Variables (n, n_k, vars), body) ->
      let m = dim_env env in
      let (Plus m_nk) = D.plus (D.plus_out n n_k) in
      let (Plus m_n) = D.plus n in
      let mn_k = D.plus_assocl m_n n_k m_nk in
      Val (Lam (Variables (D.plus_out m m_n, mn_k, vars), eval_binder env m_nk body))
  | App (fn, args) ->
      (* First we evaluate the function. *)
      let (Val efn) = eval env fn in
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
                let (Val v) = eval (Act (env, op_of_sface fa)) (CubeOf.find args fb) in
                v);
          } in
      (* Having evaluated the function and its arguments, we now pass the job off to a helper function. *)
      apply efn eargs
  | Field (tm, fld) ->
      let (Val etm) = eval env tm in
      Val (field etm fld)
  | Struct (_, fields) ->
      Val
        (Struct (Abwd.map (fun (tm, l) -> (lazy (eval env tm), l)) fields, ins_zero (dim_env env)))
  | Constr (constr, n, args) ->
      let m = dim_env env in
      let (Plus m_n) = D.plus n in
      let mn = D.plus_out m m_n in
      let eargs = Bwd.map (eval_args env m_n mn) args in
      Val (Constr (constr, mn, eargs))
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
                let (Val v) = eval (Act (env, op_of_sface fa)) (CubeOf.find doms fb) in
                v);
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
                let (Val tm) = eval (Act (env, op_of_sface fa)) tm in
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
      Val (Uninst (Pi (x, doms, cods), lazy (inst (universe m) tys)))
  | Let (_, v, body) ->
      let args =
        CubeOf.build (dim_env env)
          {
            build =
              (fun fa ->
                let (Val v) = eval (Act (env, op_of_sface fa)) v in
                v);
          } in
      eval (Ext (env, CubeOf.singleton args)) body
  (* It's tempting to write just "act_value (eval env x) s" here, but that is WRONG!  Pushing a substitution through an operator action requires whiskering the operator by the dimension of the substitution. *)
  | Act (x, s) ->
      let k = dim_env env in
      let (Plus km) = D.plus (dom_deg s) in
      let (Plus kn) = D.plus (cod_deg s) in
      let ks = plus_deg k kn km s in
      let (Val v) = eval env x in
      Val (act_value v ks)
  | Match (ix, n, branches) -> (
      (* Get the argument being inspected *)
      let m = dim_env env in
      match lookup env ix with
      (* It must be an application of a constructor *)
      | Constr (name, dim, dargs) -> (
          match Constr.Map.find_opt name branches with
          (* Matches are constructed to contain all the constructors of the datatype being matched on, and this constructor belongs to that datatype, so it ought to be in the match. *)
          | None ->
              fatal
                (Anomaly
                   (Printf.sprintf "constructor %s missing from compiled match"
                      (Constr.to_string name)))
          | Some (Branch (plus, perm, body)) -> (
              let (Plus mn) = D.plus n in
              match compare dim (D.plus_out m mn) with
              | Eq ->
                  (* If we have a branch with a matching constant, then our constructor must be applied to exactly the right number of elements (in dargs).  In that case, we pick them out and add them to the environment. *)
                  let env = take_args env mn dargs plus in
                  (* Then we proceed recursively with the body of that branch. *)
                  eval (permute_env perm env) body
              | _ -> Unrealized))
      | _ -> Unrealized)
  | Realize tm ->
      let (Val v) = eval env tm in
      Realize v
  | Canonical c -> Canonical (eval_canonical env c)

(* A helper function that doesn't get the correct types if we define it inline. *)
and eval_args :
    type m n mn a.
    (m, a) env ->
    (m, n, mn) D.plus ->
    mn D.t ->
    (n, (a, kinetic) term) CubeOf.t ->
    (mn, kinetic value) CubeOf.t =
 fun env m_n mn tms ->
  CubeOf.build mn
    {
      build =
        (fun fab ->
          let (SFace_of_plus (_, fa, fb)) = sface_of_plus m_n fab in
          match eval (Act (env, op_of_sface fa)) (CubeOf.find tms fb) with
          | Val v -> v);
    }

(* Apply a function value to an argument (with its boundaries). *)
and apply : type n s. s value -> (n, kinetic value) CubeOf.t -> s evaluation =
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
              | Neu { head; args; alignment } -> (
                  let args = Snoc (args, App (Arg newarg, ins_zero k)) in
                  match alignment with
                  | True -> Val (Uninst (Neu { head; args; alignment = True }, ty))
                  | Chaotic tm -> (
                      match apply tm arg with
                      | Realize x -> Val x
                      | Val x -> Val (Uninst (Neu { head; args; alignment = Chaotic x }, ty))
                      | Unrealized -> Val (Uninst (Neu { head; args; alignment = True }, ty))
                      | Canonical c -> Val (Uninst (Neu { head; args; alignment = Lawful c }, ty)))
                  | Lawful (Data { dim; indices; missing = Suc _ as ij; constrs }) -> (
                      match compare dim k with
                      | Neq -> fatal (Dimension_mismatch ("apply", dim, k))
                      | Eq ->
                          let indices, missing = (Bwv.Snoc (indices, newarg), N.suc_plus ij) in
                          let alignment = Lawful (Data { dim; indices; missing; constrs }) in
                          Val (Uninst (Neu { head; args; alignment }, ty)))
                  | Lawful (Codata _) | Lawful (Data { missing = Zero; _ }) ->
                      fatal (Anomaly "invalid application of type"))
              | _ -> fatal (Anomaly "invalid application of non-function uninst")))
      | _ -> fatal (Anomaly "invalid application by non-function"))
  | _ -> fatal (Anomaly "invalid application of non-function")

(* Compute the output type of a function application, given the codomains and instantiation arguments of the pi-type (the latter being the functions acting on the boundary) and the arguments it is applied to. *)
and tyof_app :
    type k.
    (k, unit) BindCube.t ->
    (D.zero, k, k, normal) TubeOf.t ->
    (k, kinetic value) CubeOf.t ->
    kinetic value =
 fun cods fns args ->
  let out_arg_tbl = Hashtbl.create 10 in
  let out_args =
    TubeOf.mmap
      {
        map =
          (fun fa [ { tm = afn; ty = _ } ] ->
            let fa = sface_of_tface fa in
            let tmargs = CubeOf.subcube fa args in
            let (Val tm) = apply afn tmargs in
            let (Val cod) = apply_binder (BindCube.find cods fa) tmargs in
            let ty =
              inst cod
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
  let (Val out) = apply_binder (BindCube.find_top cods) args in
  inst out out_args

(* Compute a field of a structure, at a particular dimension. *)
and field : kinetic value -> Field.t -> kinetic value =
 fun tm fld ->
  match tm with
  (* TODO: Is it okay to ignore the insertion here? *)
  | Struct (fields, _) ->
      let xv =
        match Abwd.find_opt fld fields with
        | Some xv -> xv
        | None -> fatal (Anomaly "missing field in eval") in
      let (Val x) = Lazy.force (fst xv) in
      x
  | Uninst (Neu { head; args; alignment }, (lazy ty)) -> (
      let newty = lazy (tyof_field tm ty fld) in
      let args = Snoc (args, App (Field fld, ins_zero D.zero)) in
      match alignment with
      | True -> Uninst (Neu { head; args; alignment = True }, newty)
      | Chaotic (Struct (fields, _)) -> (
          let x =
            match Abwd.find_opt fld fields with
            | Some x -> x
            | None -> fatal (Anomaly "missing field in eval") in
          match Lazy.force (fst x) with
          | Realize x -> x
          | Val x -> Uninst (Neu { head; args; alignment = Chaotic x }, newty)
          | Unrealized -> Uninst (Neu { head; args; alignment = True }, newty)
          | Canonical c -> Uninst (Neu { head; args; alignment = Lawful c }, newty))
      | Chaotic _ -> fatal (Anomaly "field projection of non-struct case tree")
      | Lawful _ -> fatal (Anomaly "field projection of canonical type"))
  | _ -> fatal ~severity:Asai.Diagnostic.Bug (No_such_field (`Other, `Name fld))

(* Given a term and its record type, compute the type of a field projection.  The caller can control the severity of errors, depending on whether we're typechecking (Error) or normalizing (Bug, the default). *)
and tyof_field_withname ?severity (tm : kinetic value) (ty : kinetic value) (fld : Field.or_index) :
    Field.t * kinetic value =
  let (Fullinst (ty, tyargs)) = full_inst ?severity ty "tyof_field" in
  match ty with
  | Neu
      {
        head = Const { name = const; _ };
        alignment = Lawful (Codata { eta = _; env; ins; fields });
        _;
      } -> (
      (* The type cannot have a nonidentity degeneracy applied to it (though it can be at a higher dimension). *)
      if Option.is_none (is_id_ins ins) then
        fatal ?severity (No_such_field (`Degenerated_record, fld));
      let m = cod_left_ins ins in
      let n = cod_right_ins ins in
      let mn = plus_of_ins ins in
      let mn' = D.plus_out m mn in
      match compare (TubeOf.inst tyargs) mn' with
      | Neq ->
          fatal ?severity (Dimension_mismatch ("computing type of field", TubeOf.inst tyargs, mn'))
      | Eq -> (
          (* The type of the field projection comes from the type associated to that field name in general, evaluated at the supplied parameters along with the term itself and its boundaries. *)
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
          match Field.find fields fld with
          | Some (fldname, fldty) ->
              let (Val efldty) = eval env fldty in
              ( fldname,
                (* This type is m-dimensional, hence must be instantiated at a full m-tube. *)
                inst efldty
                  (TubeOf.mmap
                     {
                       map =
                         (fun _ [ arg ] ->
                           let tm = field arg.tm fldname in
                           let _, ty = tyof_field_withname arg.tm arg.ty fld in
                           { tm; ty });
                     }
                     [ TubeOf.middle (D.zero_plus m) mn tyargs ]) )
          | None -> fatal ?severity (No_such_field (`Record (PConstant const), fld))))
  | _ -> fatal ?severity (No_such_field (`Other, fld))

and tyof_field ?severity (tm : kinetic value) (ty : kinetic value) (fld : Field.t) : kinetic value =
  snd (tyof_field_withname ?severity tm ty (`Name fld))

and eval_binder :
    type m n mn b s.
    (m, b) env -> (m, n, mn) D.plus -> ((b, n) snoc, s) term -> (mn, s) Value.binder =
 fun env mn body ->
  let m = dim_env env in
  let n = D.plus_right mn in
  let (Id_ins ins) = id_ins m n in
  let Eq = D.plus_uniq mn (plus_of_ins ins) in
  Value.Bind { env; ins; body }

and apply_binder : type n s. (n, s) Value.binder -> (n, kinetic value) CubeOf.t -> s evaluation =
 fun (Value.Bind { env; ins; body }) argstbl ->
  let m = dim_env env in
  let n = cod_right_ins ins in
  let mn = plus_of_ins ins in
  let perm = perm_of_ins ins in
  match
    eval
      (Ext
         ( env,
           CubeOf.build n
             {
               build =
                 (fun fs ->
                   CubeOf.build m
                     {
                       build =
                         (fun fr ->
                           let (Plus kj) = D.plus (dom_sface fs) in
                           let frfs = sface_plus_sface fr mn kj fs in
                           let (Face (fa, fb)) = perm_sface (perm_inv perm) frfs in
                           act_value (CubeOf.find argstbl fa) fb);
                     });
             } ))
      body
  with
  | Unrealized -> Unrealized
  | Realize v -> Realize (act_value v perm)
  | Val v -> Val (act_value v perm)
  | Canonical c -> Canonical (act_canonical c perm)

and eval_canonical : type m a. (m, a) env -> a Term.canonical -> Value.canonical =
 fun env can ->
  match can with
  | Data (i, constrs) ->
      let constrs =
        Constr.Map.map
          (fun (Term.Dataconstr { args; indices }) -> Value.Dataconstr { env; args; indices })
          constrs in
      Data { dim = dim_env env; indices = Emp; missing = N.zero_plus i; constrs }
  | Codata (eta, n, fields) ->
      let (Id_ins ins) = id_ins (dim_env env) n in
      Codata { eta; env; ins; fields }

and eval_term : type m b. (m, b) env -> (b, kinetic) term -> kinetic value =
 fun env tm ->
  let (Val v) = eval env tm in
  v

let apply_term : kinetic value -> ('n, kinetic value) CubeOf.t -> kinetic value =
 fun fn arg ->
  let (Val v) = apply fn arg in
  v

let apply_binder_term : ('n, kinetic) binder -> ('n, kinetic value) CubeOf.t -> kinetic value =
 fun b arg ->
  let (Val v) = apply_binder b arg in
  v
