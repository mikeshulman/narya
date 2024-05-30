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
        match D.compare (cod_sface fa) (CubeOf.dim entry) with
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
      let cty, defn = Global.find_opt name <|> Undefined_constant (PConstant name) in
      (* Its type must also be instantiated at the lower-dimensional versions of itself. *)
      let ty =
        lazy
          (inst (eval_term (Emp dim) cty)
             (TubeOf.build D.zero (D.zero_plus dim)
                {
                  build =
                    (fun fa ->
                      (* To compute those lower-dimensional versions, we recursively evaluate the same constant in lower-dimensional contexts. *)
                      let tm = eval_term (Act (env, op_of_sface (sface_of_tface fa))) (Const name) in
                      (* We need to know the type of each lower-dimensional version in order to annotate it as a "normal" instantiation argument.  But we already computed that type while evaluating the term itself, since as a normal term it had to be annotated with its type. *)
                      match tm with
                      | Uninst (Neu _, (lazy ty)) -> { tm; ty }
                      | _ -> fatal (Anomaly "eval of lower-dim constant not neutral/canonical"));
                })) in
      let head = Const { name; ins = ins_zero dim } in
      match defn with
      | Defined tree -> (
          match eval (Emp dim) tree with
          | Realize x -> Val x
          | Val x -> Val (Uninst (Neu { head; args = Emp; alignment = Chaotic x }, ty))
          | Canonical c -> Val (Uninst (Neu { head; args = Emp; alignment = Lawful c }, ty))
          (* It is actually possible to have a true neutral case tree in the empty context, e.g. a constant without arguments defined to equal a potential hole. *)
          | Unrealized -> Val (Uninst (Neu { head; args = Emp; alignment = True }, ty)))
      | Axiom _ -> Val (Uninst (Neu { head; args = Emp; alignment = True }, ty)))
  | Meta (meta, ambient) -> (
      let dim = dim_env env in
      let head = Value.Meta { meta; env; ins = ins_zero dim } in
      (* As with constants, we need to instantiate the type at the same meta evaluated at lower dimensions. *)
      let make_ty meta ty =
        inst (eval_term env ty)
          (TubeOf.build D.zero (D.zero_plus dim)
             {
               build =
                 (fun fa ->
                   let tm =
                     eval_term (Act (env, op_of_sface (sface_of_tface fa))) (Meta (meta, Kinetic))
                   in
                   match tm with
                   | Uninst (Neu _, (lazy ty)) -> { tm; ty }
                   | _ -> fatal (Anomaly "eval of lower-dim meta not neutral/canonical"));
             }) in
      let make_neutral meta ty alignment =
        Uninst (Neu { head; args = Emp; alignment }, lazy (make_ty meta ty)) in
      match (Global.find_meta_opt meta <|> Undefined_metavariable (PMeta meta), ambient) with
      (* If an undefined potential metavariable appears in a case tree, then that branch of the case tree is stuck.  We don't need to return the metavariable itself; it suffices to know that that branch of the case tree is stuck, as the constant whose definition it is should handle all identity/equality checks correctly. *)
      | Metadef { tm = `None; _ }, Potential -> Unrealized
      (* To evaluate an undefined kinetic metavariable, we have to build a neutral. *)
      | Metadef { tm = `None; ty; _ }, Kinetic -> Val (make_neutral meta ty True)
      (* If a metavariable has a definition that fits with the current energy, we simply evaluate that definition. *)
      | Metadef { tm = `Nonrec tm; energy = Potential; _ }, Potential -> eval env tm
      | Metadef { tm = `Nonrec tm; energy = Kinetic; _ }, Kinetic -> eval env tm
      | Metadef { tm = `Nonrec tm; energy = Kinetic; _ }, Potential -> Realize (eval_term env tm)
      | Metadef { tm = `Nonrec tm; energy = Potential; ty; _ }, Kinetic -> (
          (* If a potential metavariable with a definition is used in a kinetic context, and doesn't evaluate yet to a kinetic result, we again have to build a neutral. *)
          match eval env tm with
          | Val v -> Val (make_neutral meta ty (Chaotic v))
          | Realize tm -> Val tm
          | Unrealized -> Val (make_neutral meta ty True)
          | Canonical v -> Val (make_neutral meta ty (Lawful v))))
  | MetaEnv (meta, metaenv) ->
      let (Plus m_n) = D.plus (dim_term_env metaenv) in
      eval (eval_env env m_n metaenv) (Term.Meta (meta, Kinetic))
  | UU n ->
      let m = dim_env env in
      let (Plus mn) = D.plus n in
      Val (universe (D.plus_out m mn))
  | Inst (tm, args) -> (
      (* The arguments are an (n,k) tube, with k dimensions instantiated and n dimensions uninstantiated. *)
      let n = TubeOf.uninst args in
      let k = TubeOf.inst args in
      let n_k = TubeOf.plus args in
      (* Add the environment dimension to the uninstantiated dimensions *)
      let m = dim_env env in
      let (Plus m_n) = D.plus n in
      let mn = D.plus_out m m_n in
      (* Evaluate the inner term.  This gives an m+n+k dimensional object; it might have been instantiated from something higher-dimensional, but requires a full m+n+k tube to become fully instantiated.  We will instantiate k of those dimensions, leaving m+n. *)
      let newtm = eval_term env tm in
      let (Plus mn_k) = D.plus k in
      let mnk = D.plus_out mn mn_k in
      (* tys is a complete m+n+k tube, giving the types of all the arguments that newtm remains to be instantiated by. *)
      let (Inst_tys tys) = inst_tys newtm in
      match D.compare (TubeOf.inst tys) mnk with
      | Neq -> fatal (Dimension_mismatch ("evaluation instantiation", TubeOf.inst tys, mnk))
      | Eq ->
          (* used_tys is an (m+n,k) tube, with m+n uninstantiated and k instantiated.  These are the types that we must instantiate to give the types of the added instantiation arguments. *)
          let used_tys = TubeOf.pboundary (D.zero_plus mn) mn_k tys in
          let newargstbl = Hashtbl.create 10 in
          let newargs =
            TubeOf.mmap
              {
                map =
                  (fun fa [ ty ] ->
                    (* fa : p+q => m+n+k, fa = fb+fc where fb : p => m and fcd : q => n+k. *)
                    let (TFace_of_plus (_, fb, fcd)) = tface_of_plus m_n fa in
                    let fa = sface_of_tface fa in
                    let Eq = D.plus_uniq (cod_plus_of_tface fcd) n_k in
                    (* Thus tm is p+q dimensional. *)
                    let tm = eval_term (Act (env, op_of_sface fb)) (TubeOf.find args fcd) in
                    (* So its type needs to be fully instantiated at that dimension. *)
                    let ty =
                      inst ty
                        (TubeOf.build D.zero
                           (D.zero_plus (dom_sface fa))
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
      let efn = eval_term env fn in
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
                eval_term (Act (env, op_of_sface fa)) (CubeOf.find args fb));
          } in
      (* Having evaluated the function and its arguments, we now pass the job off to a helper function. *)
      apply efn eargs
  | Field (tm, fld) -> Val (field (eval_term env tm) fld)
  | Struct (_, dim, fields) ->
      let (Plus mn) = D.plus (dim_env env) in
      let ins = ins_zero (D.plus_out dim mn) in
      Val (Struct (Abwd.map (fun (tm, l) -> (lazy (eval env tm), l)) fields, ins))
  | Constr (constr, n, args) ->
      let m = dim_env env in
      let (Plus m_n) = D.plus n in
      let mn = D.plus_out m m_n in
      let eargs = List.map (eval_args env m_n mn) args in
      Val (Constr (constr, mn, eargs))
  | Pi (x, doms, cods) ->
      (* We are starting with an n-dimensional pi-type and evaluating it in an m-dimensional environment, producing an (m+n)-dimensional result. *)
      let n = CubeOf.dim doms in
      let m = dim_env env in
      let (Plus m_n) = D.plus n in
      let mn = D.plus_out m m_n in
      (* The basic thing we do is evaluate the cubes of domains and codomains. *)
      let doms =
        CubeOf.build mn
          {
            build =
              (fun fab ->
                let (SFace_of_plus (_, fa, fb)) = sface_of_plus m_n fab in
                eval_term (Act (env, op_of_sface fa)) (CubeOf.find doms fb));
          } in
      let cods =
        BindCube.build mn
          {
            build =
              (fun fab ->
                let (SFace_of_plus (k_l, fa, fb)) = sface_of_plus m_n fab in
                eval_binder (Act (env, op_of_sface fa)) k_l (CodCube.find cods fb));
          } in
      (* However, because the result will be an Uninst, we need to know its type as well.  The starting n-dimensional pi-type (which is itself uninstantiated) lies in a full instantiation of the n-dimensional universe at lower-dimensional pi-types formed from subcubes of its domains and codomains.  Accordingly, the resulting (m+n)-dimensional pi-type will like in a full instantiation of the (m+n)-dimensional universe at lower-dimensional pi-types obtained by evaluating these at appropriately split faces.  Since each of them *also* belongs to a universe instantiated similarly, and needs to know its type not just because it is an uninst but because it is a normal, we build the whole cube at once and then take its top. *)
      let pitbl = Hashtbl.create 10 in
      let pis =
        CubeOf.build mn
          {
            build =
              (fun fab ->
                let kl = dom_sface fab in
                let ty =
                  inst (universe kl)
                    (TubeOf.build D.zero (D.zero_plus kl)
                       {
                         build =
                           (fun fc ->
                             Hashtbl.find pitbl (SFace_of (comp_sface fab (sface_of_tface fc))));
                       }) in
                let tm =
                  Uninst
                    (Pi (x, CubeOf.subcube fab doms, BindCube.subcube fab cods), Lazy.from_val ty)
                in
                let ntm = { tm; ty } in
                Hashtbl.add pitbl (SFace_of fab) ntm;
                ntm);
          } in
      Val (CubeOf.find_top pis).tm
  | Let (_, v, body) ->
      let args =
        CubeOf.build (dim_env env) { build = (fun fa -> eval_term (Act (env, op_of_sface fa)) v) }
      in
      eval (Ext (env, CubeOf.singleton args)) body
  (* It's tempting to write just "act_value (eval env x) s" here, but that is WRONG!  Pushing a substitution through an operator action requires whiskering the operator by the dimension of the substitution. *)
  | Act (x, s) ->
      let k = dim_env env in
      let (Plus km) = D.plus (dom_deg s) in
      let (Plus kn) = D.plus (cod_deg s) in
      let ks = plus_deg k kn km s in
      Val (act_value (eval_term env x) ks)
  | Match { tm; dim = match_dim; branches } -> (
      let env_dim = dim_env env in
      let (Plus plus_dim) = D.plus match_dim in
      let total_dim = D.plus_out env_dim plus_dim in
      (* Get the argument being inspected *)
      match eval_term env tm with
      (* To reduce nontrivially, the discriminee must be an application of a constructor. *)
      | Constr (name, constr_dim, dargs) -> (
          match Constr.Map.find_opt name branches with
          (* Matches are constructed to contain all the constructors of the datatype being matched on, and this constructor belongs to that datatype, so it ought to be in the match. *)
          | None ->
              fatal
                (Anomaly
                   (Printf.sprintf "constructor %s missing from compiled match"
                      (Constr.to_string name)))
          | Some (Branch (plus, perm, body)) -> (
              match D.compare constr_dim total_dim with
              | Neq -> fatal (Dimension_mismatch ("evaluating match", constr_dim, total_dim))
              | Eq ->
                  (* If we have a branch with a matching constructor, then our constructor must be applied to exactly the right number of elements (in dargs).  In that case, we pick them out and add them to the environment. *)
                  let env = take_args env plus_dim dargs plus in
                  (* Then we proceed recursively with the body of that branch. *)
                  eval (permute_env perm env) body))
      (* Otherwise, the case tree doesn't reduce. *)
      | _ -> Unrealized)
  | Realize tm -> Realize (eval_term env tm)
  | Canonical c -> Canonical (eval_canonical env c)

and eval_with_boundary :
    type m n mn a. (m, a) env -> (a, kinetic) term -> (m, kinetic value) CubeOf.t =
 fun env tm ->
  CubeOf.build (dim_env env) { build = (fun fa -> eval_term (Act (env, op_of_sface fa)) tm) }

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
          eval_term (Act (env, op_of_sface fa)) (CubeOf.find tms fb));
    }

(* Apply a function value to an argument (with its boundaries). *)
and apply : type n s. s value -> (n, kinetic value) CubeOf.t -> s evaluation =
 fun fn arg ->
  match fn with
  (* If the function is a lambda-abstraction, we check that it has the correct dimension and then beta-reduce, adding the arguments to the environment. *)
  | Lam (_, body) -> (
      let m = CubeOf.dim arg in
      match D.compare (dim_binder body) m with
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
          match (D.compare (TubeOf.inst tyargs) k, D.compare (CubeOf.dim arg) k) with
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
                  | Lawful (Data { dim; indices = Unfilled _ as indices; constrs }) -> (
                      match D.compare dim k with
                      | Neq -> fatal (Dimension_mismatch ("apply", dim, k))
                      | Eq ->
                          let indices = Fillvec.snoc indices newarg in
                          let alignment = Lawful (Data { dim; indices; constrs }) in
                          Val (Uninst (Neu { head; args; alignment }, ty)))
                  | _ -> fatal (Anomaly "invalid application of type"))
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
            let tm = apply_term afn tmargs in
            let cod = apply_binder_term (BindCube.find cods fa) tmargs in
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
  inst (apply_binder_term (BindCube.find_top cods) args) out_args

(* Compute a field of a structure. *)
and field : type n. kinetic value -> Field.t -> kinetic value =
 fun tm fld ->
  match tm with
  (* TODO: Is it okay to ignore the insertion here? *)
  | Struct (fields, _) ->
      let xv =
        Abwd.find_opt fld fields <|> Anomaly ("missing field in eval struct: " ^ Field.to_string fld)
      in
      let (Val x) = Lazy.force (fst xv) in
      x
  | Uninst (Neu { head; args; alignment }, (lazy ty)) -> (
      let Wrap n, newty = tyof_field_withdim tm ty fld in
      let newty = Lazy.from_val newty in
      let args = Snoc (args, App (Field fld, ins_zero n)) in
      match alignment with
      | True -> Uninst (Neu { head; args; alignment = True }, newty)
      | Chaotic (Struct (fields, _)) -> (
          match Abwd.find_opt fld fields with
          | None ->
              (* This can happen correctly during checking a recursive case tree, where the body of one field refers to its not-yet-defined self or other not-yet-defined fields. *)
              Uninst (Neu { head; args; alignment = True }, newty)
          | Some x -> (
              match Lazy.force (fst x) with
              | Realize x -> x
              | Val x -> Uninst (Neu { head; args; alignment = Chaotic x }, newty)
              | Unrealized -> Uninst (Neu { head; args; alignment = True }, newty)
              | Canonical c -> Uninst (Neu { head; args; alignment = Lawful c }, newty)))
      | Chaotic _ -> fatal (Anomaly "field projection of non-struct case tree")
      | Lawful _ -> fatal (Anomaly "field projection of canonical type"))
  | _ -> fatal ~severity:Asai.Diagnostic.Bug (No_such_field (`Other, `Name fld))

(* Given a term and its record type, compute the type and dimension of a field projection.  The caller can control the severity of errors, depending on whether we're typechecking (Error) or normalizing (Bug, the default). *)
and tyof_field_withname ?severity (tm : kinetic value) (ty : kinetic value) (fld : Field.or_index) :
    Field.t * dim_wrapped * kinetic value =
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
      match D.compare (TubeOf.inst tyargs) mn' with
      | Neq ->
          fatal ?severity (Dimension_mismatch ("computing type of field", TubeOf.inst tyargs, mn'))
      | Eq -> (
          (* The type of the field projection comes from the type associated to that field name in general, evaluated at the stored environment extended by the term itself and its boundaries. *)
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
              ( fldname,
                Wrap m,
                (* This type is m-dimensional, hence must be instantiated at a full m-tube. *)
                inst (eval_term env fldty)
                  (TubeOf.mmap
                     {
                       map =
                         (fun _ [ arg ] ->
                           let tm = field arg.tm fldname in
                           let _, _, ty = tyof_field_withname arg.tm arg.ty fld in
                           { tm; ty });
                     }
                     [ TubeOf.middle (D.zero_plus m) mn tyargs ]) )
          | None -> fatal ?severity (No_such_field (`Record (PConstant const), fld))))
  | _ -> fatal ?severity (No_such_field (`Other, fld))

and tyof_field_withdim ?severity (tm : kinetic value) (ty : kinetic value) (fld : Field.t) :
    dim_wrapped * kinetic value =
  let _, n, ty = tyof_field_withname ?severity tm ty (`Name fld) in
  (n, ty)

and tyof_field ?severity (tm : kinetic value) (ty : kinetic value) (fld : Field.t) : kinetic value =
  let _, _, ty = tyof_field_withname ?severity tm ty (`Name fld) in
  ty

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
      Data { dim = dim_env env; indices = Fillvec.empty i; constrs }
  | Codata (eta, n, fields) ->
      let (Id_ins ins) = id_ins (dim_env env) n in
      Codata { eta; env; ins; fields }

and eval_term : type m b. (m, b) env -> (b, kinetic) term -> kinetic value =
 fun env tm ->
  let (Val v) = eval env tm in
  v

and eval_env :
    type a m n mn b. (m, a) env -> (m, n, mn) D.plus -> (a, n, b) Term.env -> (mn, b) Value.env =
 fun env m_n tmenv ->
  let mn = D.plus_out (dim_env env) m_n in
  match tmenv with
  | Emp _ -> Emp mn
  | Ext (tmenv, xss) ->
      Ext
        ( eval_env env m_n tmenv,
          CubeOf.mmap
            {
              map =
                (fun _ [ xs ] ->
                  CubeOf.build mn
                    {
                      build =
                        (fun fab ->
                          let (SFace_of_plus (_, fa, fb)) = sface_of_plus m_n fab in
                          eval_term (Act (env, op_of_sface fa)) (CubeOf.find xs fb));
                    });
            }
            [ xss ] )

and apply_term : type n. kinetic value -> (n, kinetic value) CubeOf.t -> kinetic value =
 fun fn arg ->
  let (Val v) = apply fn arg in
  v

and apply_binder_term : type n. (n, kinetic) binder -> (n, kinetic value) CubeOf.t -> kinetic value
    =
 fun b arg ->
  let (Val v) = apply_binder b arg in
  v

(* Apply a function to all the values in a cube one by one as 0-dimensional applications, rather than as one n-dimensional application. *)
let apply_singletons : type n. kinetic value -> (n, kinetic value) CubeOf.t -> kinetic value =
 fun fn xs ->
  let module MC = CubeOf.Monadic (Monad.State (struct
    type t = kinetic value
  end)) in
  snd (MC.miterM { it = (fun _ [ x ] fn -> ((), apply_term fn (CubeOf.singleton x))) } [ xs ] fn)

(* Evaluate a term context to produce a value context. *)

let eval_bindings :
    type a b n.
    (a, b) Ctx.Ordered.t -> (n, (b, n) snoc Termctx.binding) CubeOf.t -> (n, Ctx.Binding.t) CubeOf.t
    =
 fun ctx cbs ->
  let open Termctx in
  let i = Ctx.Ordered.length ctx in
  let vbs = CubeOf.build (CubeOf.dim cbs) { build = (fun _ -> Ctx.Binding.unknown ()) } in
  let tempctx = Ctx.Ordered.Snoc (ctx, Invis vbs, Zero) in
  let argtbl = Hashtbl.create 10 in
  let j = ref 0 in
  let () =
    CubeOf.miter
      {
        it =
          (fun fa [ ({ ty = cty; tm = ctm } : (b, n) snoc binding); vb ] ->
            (* Unlike in dom_vars, we don't need to instantiate the types, since their instantiations should have been preserved by readback and will reappear correctly here. *)
            let ety = eval_term (Ctx.Ordered.env tempctx) cty in
            let level = (i, !j) in
            j := !j + 1;
            let v =
              match ctm with
              | None -> ({ tm = var level ety; ty = ety } : normal)
              | Some ctm -> { tm = eval_term (Ctx.Ordered.env tempctx) ctm; ty = ety } in
            Hashtbl.add argtbl (SFace_of fa) v;
            Ctx.Binding.specify vb None v);
      }
      [ cbs; vbs ] in
  vbs

let eval_entry : type a b f n. (a, b) Ctx.Ordered.t -> (b, f, n) Termctx.entry -> (f, n) Ctx.entry =
 fun ctx e ->
  match e with
  | Termctx.Vis { dim; plusdim; vars; bindings; hasfields; fields; fplus } ->
      let bindings = eval_bindings ctx bindings in
      let fields = Bwv.map (fun (f, x, _) -> (f, x)) fields in
      Vis { dim; plusdim; vars; bindings; hasfields; fields; fplus }
  | Invis bindings -> Invis (eval_bindings ctx bindings)

let rec eval_ordered_ctx : type a b. (a, b) Termctx.ordered -> (a, b) Ctx.Ordered.t = function
  | Termctx.Emp -> Emp
  | Snoc (ctx, e, af) ->
      let ectx = eval_ordered_ctx ctx in
      Snoc (ectx, eval_entry ectx e, af)
  | Lock ctx -> Lock (eval_ordered_ctx ctx)

let eval_ctx : type a b. (a, b) Termctx.t -> (a, b) Ctx.t = function
  | Termctx.Permute (p, ctx) -> Permute (p, eval_ordered_ctx ctx)
