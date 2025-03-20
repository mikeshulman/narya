open Bwd
open Util
open Dim
open Reporter
open Term
open Value

(* Operator actions on values.  Unlike substitution, operator actions take a *value* as input (and produces another value). *)

(* Since values don't have a statically specified dimension, we have to act on them by an *arbitrary* degeneracy, which means that in many places we have to check dynamically that the dimensions either match or can be extended to match.  This function encapsulates that. *)
let deg_plus_to : type m n nk. on:string -> ?err:Code.t -> (m, n) deg -> nk D.t -> nk deg_of =
 fun ~on ?err s nk ->
  match factor nk (cod_deg s) with
  | None -> fatal (Option.value err ~default:(Invalid_degeneracy_action (on, nk, cod_deg s)))
  | Some (Factor nk) ->
      let (Plus mk) = D.plus (D.plus_right nk) in
      let sk = deg_plus s nk mk in
      Of sk

(* Act on a cube of objects *)

type ('a, 'b) actor = { act : 'm 'n. 'a -> ('m, 'n) deg -> 'b }

let act_cube : type a b m n. (a, b) actor -> (n, a) CubeOf.t -> (m, n) deg -> (m, b) CubeOf.t =
 fun actor xs fa ->
  CubeOf.build (dom_deg fa)
    {
      build =
        (fun fb ->
          let (Op (fd, fc)) = deg_sface fa fb in
          actor.act (CubeOf.find xs fd) fc);
    }

(* Forward recursion to Norm *)
let forward_view_term : (kinetic value -> kinetic value) ref = ref (fun x -> x)

module Act = struct
  (* When acting on a cube of variables that's at least partially split up into ordinary variables, we have a problem if the degeneracy mixes up the dimensions that are ordinary with the dimensions that are cube.  We could get around this by storing an 'insertion' rather than a D.plus in a 'variables', but we wouldn't be able to *use* that usefully anywhere, since there's no way to create a partially-cube variable in syntax.  So instead, if the dimensions get mixed up we just give up the split and make it fully-cube using only the previous top variable.  *)
  let act_variables : type m n. n variables -> (m, n) deg -> m variables =
   fun (Variables (_, nk, vars)) s ->
    match deg_perm_of_plus nk s with
    | None_deg_perm_of_plus ->
        let m = dom_deg s in
        Variables (m, D.plus_zero m, NICubeOf.singleton (NICubeOf.find_top vars))
    (* If the degeneracy doesn't mix up the ordinary and cube dimensions, it still might permute the ordinary ones.  I'm not positive that it makes sense to throw away the degeneracy part here and the permutation part below, but this is the best I can think of.  If it doesn't end up making sense, we may have to revert to making it fully-cube as above. *)
    | Deg_perm_of_plus (ml, s, p) ->
        let m = dom_deg s in
        let module Build = NICubeOf.Traverse (struct
          type 'acc t = unit
        end) in
        let (Wrap (vars, _)) =
          Build.build_left (D.plus_right ml)
            {
              build =
                (fun fa () ->
                  let (Face (fb, _)) = perm_sface p fa in
                  Fwrap (NFamOf (NICubeOf.find vars fb), ()));
            }
            () in
        Variables (m, ml, vars)

  (* Acting on a binder and on other sorts of closures will be unified by the function 'act_closure', but its return value involves an existential type, so it has to be a GADT. *)
  type (_, _, _) act_closure =
    | Act_closure : ('m, 'a) env * ('mn, 'm, 'n) insertion -> ('a, 'mn, 'n) act_closure

  (* Acting on a value that could be instantiated or uninstantiated, or an introduction form. *)
  let rec act_value : type m n status. status value -> (m, n) deg -> status value =
   fun v s ->
    match v with
    | Uninst (tm, (lazy ty)) -> Uninst (act_uninst tm s, lazy (act_ty v ty s))
    | Inst { tm; dim; args; tys } ->
        let (Of fa) = deg_plus_to s (TubeOf.uninst args) ~on:"instantiation" in
        (* The action on an instantiation instantiates the same dimension j, but the leftover dimensions are now the domain of the degeneracy. *)
        let j = TubeOf.inst args in
        (* let n = TubeOf.uninst args in *)
        let nj = TubeOf.plus args in
        let m = dom_deg fa in
        let (Plus mj) = D.plus j in
        (* The new arguments are obtained by factoring and acting on appropriate original arguments *)
        let args =
          TubeOf.build m mj
            {
              build =
                (fun fed ->
                  let (PFace_of_plus (_, fb, fd)) = pface_of_plus fed in
                  let (Op (fe, fs)) = deg_sface fa fb in
                  let (Plus q) = D.plus (dom_tface fd) in
                  act_normal (TubeOf.find args (sface_plus_pface fe nj q fd)) fs);
            } in
        let tys' = TubeOf.plus_cube tys (CubeOf.singleton v) in
        (* This is the boundary of "act_cube {...} tys' fa", but computing it that way would also try to compute the inner filler, which would be an infinite loop. *)
        let tys =
          TubeOf.build D.zero
            (D.zero_plus (dom_deg fa))
            {
              build =
                (fun fb ->
                  let (Op (fd, fc)) = deg_sface fa (sface_of_tface fb) in
                  act_value (CubeOf.find tys' fd) fc);
            } in
        Inst { tm = act_uninst tm fa; dim; args; tys }
    | Lam (x, body) ->
        let (Of fa) = deg_plus_to s (dim_binder body) ~on:"lambda" in
        Lam (act_variables x fa, act_binder body fa)
    | Struct
        (type p k pk et)
        ((fields, ins, energy) :
          (p * status * et) Value.StructfieldAbwd.t * (pk, p, k) insertion * status energy) ->
        let (Insfact_comp
               (type q l ql j z)
               ((deg0, new_ins, _, _) :
                 (q, p) deg * (ql, q, l) insertion * (k, j, l) D.plus * (m, z, ql) D.plus)) =
          insfact_comp ins s in
        let fields =
          Mbwd.mmap
            (fun [ StructfieldAbwd.Entry (fld, sfld) ] ->
              StructfieldAbwd.Entry (fld, act_structfield deg0 sfld))
            [ fields ] in
        Struct (fields, new_ins, energy)
    | Constr (name, dim, args) ->
        let (Of fa) = deg_plus_to s dim ~on:"constr" in
        Constr
          ( name,
            dom_deg fa,
            List.map (fun tm -> act_cube { act = (fun x s -> act_value x s) } tm fa) args )

  and act_structfield : type p q i status et.
      (q, p) deg -> (i, p * status * et) Structfield.t -> (i, q * status * et) Structfield.t =
   fun deg0 sfld ->
    match sfld with
    (* For a lower structfield, we just act in a straightforward way on each (lazy) value. *)
    | Lower (v, l) -> Lower (act_lazy_eval v deg0, l)
    | Higher
        (type m n mn a)
        (* Higher structfields are trickier. *)
        ({ vals; intrinsic; plusdim; env; deg = deg1; terms } :
          (m, n, mn, p, i, a) Structfield.higher_data) ->
        (* That means
           vals : (p, i, potential lazy_eval option) InsmapOf.t;
           intrinsic : i D.t;
           plusdim : (m, n, mn) D.plus;
           env : (m, a) env;
           deg1 : (p, mn) deg;
           terms : (n, i, a) PlusPbijmap.t; *)
        (* Also in here we have status = potential. *)
        (* Now we want to change p to q by acting by fa : (q, p) deg.  We'll keep almost everything the same and simply compose deg with fa.  The sticky bit is to update vals, which has to become an Insmap with evaluation dimension q rather than p.
        *)
        let vals =
          InsmapOf.build (dom_deg deg0) intrinsic
            {
              build =
                (fun (type s) (ins : (q, s, i) insertion) ->
                  (* First we unfactor this q-insertion through deg0 to get a partial bijection from p to i. *)
                  let (Deg_comp_ins
                         (type s2 r2 h2)
                         ((ins2, shuf2, deg2) :
                           (p, s2, h2) insertion * (r2, h2, i) shuffle * (s, s2) deg)) =
                    deg_comp_ins deg0 ins in
                  let r2 = left_shuffle shuf2 in
                  (* If this partial bijection is itself just an insertion, then we can simply use it as an index into the old vals and act in a simple way, as we did for lower structfields. *)
                  match D.compare_zero r2 with
                  | Zero ->
                      let Eq = eq_of_zero_shuffle shuf2 in
                      (* Note we have to act by deg2 here, not by deg0, since the field *values* only have the corresponding 'result dimension. *)
                      Option.map (fun v -> act_lazy_eval v deg2) (InsmapOf.find ins2 vals)
                  | Pos _s -> (
                      (* Otherwise, we have to look into the 'terms' to find something to evaluate.  We start by further unfactoring through 'deg1' (combining it with deg0 first, to simplify the results) and 'plusdim' to get down to the original record dimension 'n and evaluation dimension 'm.  *)
                      let (Deg_comp_ins
                             (type s3 r3 h3)
                             ((ins3, shuf3, deg3) :
                               (mn, s3, h3) insertion * (r3, h3, i) shuffle * (s, s3) deg)) =
                        deg_comp_ins (comp_deg deg1 deg0) ins in
                      (* The dimensions that disappear in this degeneracy, and hence will have to be added back in, are those added by the degeneracy deg3 (s - s3) and those in the remaining dimensions r3. *)
                      let (Unplus_pbij
                             (type s4 h4 r4 r34 t tn)
                             ((ins4, shuf4, rr, mtr, _tn, tnsh) :
                               (n, s4, h4) insertion
                               * (r34, h4, i) shuffle
                               * (r3, r4, r34) shuffle
                               * (m, t, r4) insertion
                               * (t, n, tn) D.plus
                               * (tn, s3, h4) insertion)) =
                        unplus_pbij (dim_env env) plusdim ins3 shuf3 in
                      match PlusPbijmap.find (Pbij (ins4, shuf4)) terms with
                      | PlusFam None -> None
                      | PlusFam
                          (type ra)
                          (Some (ra, tm) : ((r34, a, ra) Plusmap.t * (ra, potential) term) option)
                        ->
                          (* Now the game is to build a degeneracy that we can apply to the environment 'env' so that we can shift it by 'ra' and evaluate the term 'tm'.  That means we need to get an environment whose dimension is something+r34.  We start by adding r3.
                             m + r3
                             ≅ (t + r4) + r3    (mtr)
                             ≅ t + (r4 + r3)
                             ≅ t + (r3 + r4)
                             ≅ t + r34          (rr)
                          *)
                          let m = dim_env env in
                          let r3 = left_shuffle rr in
                          let (Plus mr3) = D.plus r3 in
                          let plusr3 = plus_deg m (D.plus_zero m) mr3 (deg_zero r3) in
                          let env1 = act_env env (op_of_deg plusr3) in
                          (* env1 has dimension m + r3 *)
                          let r4 = cod_right_ins mtr in
                          let (Plus tr4) = D.plus r4 in
                          let mtrp = deg_of_perm (perm_inv (perm_of_ins_plus mtr tr4)) in
                          let (Plus tr4_r3) = D.plus r3 in
                          let env2 = act_env env1 (op_of_deg (deg_plus mtrp mr3 tr4_r3)) in
                          (* env2 has dimension (t + r4) + r3 *)
                          let (Plus r4r3) = D.plus r3 in
                          let (Plus r3r4) = D.plus r4 in
                          let t_r4r3 = D.plus_assocr tr4 r4r3 tr4_r3 in
                          let (Plus t_r3r4) = D.plus (D.plus_out r3 r3r4) in
                          let rrswap = swap_deg r3r4 r4r3 in
                          let t = cod_left_ins mtr in
                          let env3 = act_env env2 (op_of_deg (plus_deg t t_r4r3 t_r3r4 rrswap)) in
                          (* env3 has dimension t + (r3 + r4). *)
                          let r34 = out_shuffle rr in
                          let (Plus t_r34) = D.plus r34 in
                          let drr = plus_deg t t_r3r4 t_r34 (deg_of_shuffle rr r3r4) in
                          let env4 = act_env env3 (op_of_deg drr) in
                          (* env4 has dimension t + r34 *)
                          let env5 = Shift (env4, t_r34, ra) in
                          (* env5 has dimension t.  So when we evaluate the n-dimensional record type in this environment, we get an object of dimension
                             t + n
                             = tn        (tn)
                             ≅ s3 + h4  (tnsh)
                             ← s + h4   (deg3)
                          *)
                          let etm = lazy_eval env5 tm in
                          let h4 = cod_right_ins tnsh in
                          let (Plus s3h4) = D.plus h4 in
                          let ptnsh = deg_of_perm (perm_inv (perm_of_ins_plus tnsh s3h4)) in
                          let (Plus sh4) = D.plus h4 in
                          let deg3_h4 = deg_plus deg3 s3h4 sh4 in
                          Some (act_lazy_eval etm (comp_deg ptnsh deg3_h4))));
            } in
        let deg = comp_deg deg1 deg0 in
        Higher { vals; intrinsic; plusdim; env; deg; terms }

  and act_evaluation : type m n s. s evaluation -> (m, n) deg -> s evaluation =
   fun tm s ->
    match tm with
    | Unrealized -> Unrealized
    | Realize tm -> Realize (act_value tm s)
    | Val tm -> Val (act_value tm s)
    | Canonical c ->
        let (Any c) = act_canonical c s in
        Canonical c

  and act_canonical : type m n nk. nk canonical -> (m, n) deg -> any_canonical =
   fun tm s ->
    match tm with
    | Data { dim; tyfam; indices; constrs; discrete } ->
        let (Of fa) = deg_plus_to ~on:"data" s dim in
        let tyfam = ref (Option.map (fun x -> lazy (act_normal (Lazy.force x) fa)) !tyfam) in
        let indices =
          Fillvec.map (fun ixs -> act_cube { act = (fun x s -> act_normal x s) } ixs fa) indices
        in
        let constrs = Abwd.map (fun c -> act_dataconstr c fa) constrs in
        Any (Data { dim = dom_deg fa; tyfam; indices; constrs; discrete })
    | Codata { eta; opacity; env; termctx; ins; fields } ->
        let (Of fa) = deg_plus_to ~on:"codata" s (dom_ins ins) in
        let (Act_closure (env, ins)) = act_closure env ins fa in
        Any (Codata { eta; opacity; env; termctx; ins; fields })

  and act_dataconstr : type m n i. (n, i) dataconstr -> (m, n) deg -> (m, i) dataconstr =
   fun (Dataconstr { env; args; indices }) s ->
    let env = act_env env (op_of_deg s) in
    Dataconstr { env; args; indices }

  and act_uninst : type m n. uninst -> (m, n) deg -> uninst =
   fun tm s ->
    match tm with
    | Neu { head; args; value } ->
        (* We act on the applications from the outside (last) to the inside, since the degeneracy has to be factored and may leave neutral insertions behind.  The resulting inner degeneracy then acts on the head. *)
        let Any_deg s', args = act_apps args s in
        let head = act_head head s' in
        (* We act on the alignment separately with the original s, since (e.g.) a chaotic alignment is a "value" of the entire application spine, not just the head. *)
        let value = act_lazy_eval value s in
        Neu { head; args; value }
    | UU nk ->
        let (Of fa) = deg_plus_to s nk ~on:"universe" in
        UU (dom_deg fa)
    | Pi (x, doms, cods) ->
        let k = CubeOf.dim doms in
        let (Of fa) = deg_plus_to s k ~on:"pi-type" in
        let mi = dom_deg fa in
        let doms' = act_cube { act = (fun x s -> act_value x s) } doms fa in
        let cods' =
          BindCube.build mi
            {
              build =
                (fun fb ->
                  let (Op (fc, fd)) = deg_sface fa fb in
                  act_binder (BindCube.find cods fc) fd);
            } in
        Pi (x, doms', cods')

  (* act_closure and act_binder assume that the degeneracy has exactly the correct codomain.  So if it doesn't, the caller should call deg_plus_to first. *)
  and act_closure : type mn m n a kn.
      (m, a) env -> (mn, m, n) insertion -> (kn, mn) deg -> (a, kn, n) act_closure =
   fun env ins fa ->
    let (Plus mn) = D.plus (cod_right_ins ins) in
    let (Insfact (fc, ins)) = insfact (comp_deg (deg_of_ins_plus ins mn) fa) mn in
    Act_closure (act_env env (op_of_deg fc), ins)

  and act_binder : type mn kn s. (mn, s) binder -> (kn, mn) deg -> (kn, s) binder =
   fun (Bind { env; ins; body }) fa ->
    let (Act_closure (env, ins)) = act_closure env ins fa in
    Bind { env; ins; body }

  and act_normal : type a b. normal -> (a, b) deg -> normal =
   fun { tm; ty } s -> { tm = act_value tm s; ty = act_ty tm ty s }

  (* When acting on a neutral or normal, we also need to specify the type of the output.  This *isn't* act_value on the original type; instead the type is required to be fully instantiated and the operator acts on the *instantiated* dimensions, in contrast to how act_value on an instantiation acts on the *uninstantiated* dimensions (as well as the instantiated term).  This function computes this "type of acted terms".  In general, it has to be passed the term as well as the type because the instantiation of the result may involve that term, e.g. if x : A then refl x : Id A x x; but we allow that term to be omitted in case the degeneracy is a pure symmetry in which case this doesn't happen. *)
  and gact_ty : type a b.
      ?err:Code.t -> kinetic value option -> kinetic value -> (a, b) deg -> kinetic value =
   fun ?err tm tmty s ->
    match !forward_view_term tmty with
    | Inst { tm = ty; dim; args; tys = _ } -> (
        (* A type must be fully instantiated, so in particular tys is trivial. *)
        match D.compare (TubeOf.uninst args) D.zero with
        | Neq -> fatal (Anomaly "act_ty applied to non-fully-instantiated term")
        | Eq ->
            let Eq = D.plus_uniq (TubeOf.plus args) (D.zero_plus (TubeOf.inst args)) in
            (* We check that the degeneracy can be extended to match the instantiation dimension.  If this fails, it is sometimes a bug, but sometimes a user error, e.g. when trying to symmetrize a 1-dimensional thing.  So we allow the caller to provide the error code. *)
            let (Of fa) = deg_plus_to s (TubeOf.inst args) ?err ~on:"instantiated type" in
            (* We build the new arguments by factorization and action.  Note that the one missing face would be "act_value tm s", which would be an infinite loop in case tm is a neutral.  (Hence why we can't just call act_cube and then take the boundary.) *)
            let args =
              TubeOf.build D.zero
                (D.zero_plus (dom_deg fa))
                {
                  build =
                    (fun fb ->
                      let (Op (fd, fc)) = deg_sface fa (sface_of_tface fb) in
                      let ftm =
                        (* The arguments of a full instantiation are missing only the top face, which is filled in by the term belonging to it. *)
                        match (pface_of_sface fd, tm) with
                        | `Proper fd, _ -> TubeOf.find args fd
                        | `Id Eq, Some tm -> { tm; ty = tmty }
                        | `Id _, None ->
                            fatal
                              (Anomaly "term missing in action on instantiated type by non-symmetry")
                      in
                      act_normal ftm fc);
                } in
            Inst { tm = act_uninst ty s; dim = pos_deg dim fa; args; tys = TubeOf.empty D.zero })
    | Uninst (ty, (lazy uu)) -> (
        (* This is just the case when dim = 0, so it is the same except simpler. *)
        let fa = s in
        match (D.compare (cod_deg fa) D.zero, uu) with
        (* This can also be a user error, e.g. symmetrizing a 0-dimensional thing, so we allow the caller to provide a different error code. *)
        | Neq, _ ->
            fatal
              (Option.value ~default:(Anomaly "invalid degeneracy action on uninstantiated type")
                 err)
        | Eq, Uninst (UU z, _) -> (
            match (D.compare z D.zero, D.compare_zero (dom_deg fa), tm) with
            | Neq, _, _ -> fatal (Anomaly "acting on non-fully-instantiated type as a type")
            | Eq, Zero, _ -> Uninst (act_uninst ty fa, lazy uu)
            | Eq, Pos _, None -> fatal (Anomaly "term missing in action on uninstantiated type")
            | Eq, Pos dim, Some tm ->
                let args =
                  TubeOf.build D.zero
                    (D.zero_plus (dom_deg fa))
                    {
                      build =
                        (fun fb ->
                          let (Op (_, fc)) = deg_sface fa (sface_of_tface fb) in
                          act_normal { tm; ty = tmty } fc);
                    } in
                Inst { tm = act_uninst ty fa; dim; args; tys = TubeOf.empty D.zero })
        | _ -> fatal (Anomaly "acting on non-type as if a type"))
    | Lam _ -> fatal (Anomaly "a lambda-abstraction cannot be a type to act on")
    | Struct _ -> fatal (Anomaly "a struct cannot be a type to act on")
    | Constr _ -> fatal (Anomaly "a constructor cannot be a type to act on")

  and act_ty : type a b.
      ?err:Code.t -> kinetic value -> kinetic value -> (a, b) deg -> kinetic value =
   fun ?err tm tmty s -> gact_ty ?err (Some tm) tmty s

  (* Action on a head *)
  and act_head : type a b. head -> (a, b) deg -> head =
   fun ne s ->
    match ne with
    (* To act on a variable, we just accumulate the delayed action. *)
    | Var { level; deg } ->
        let (DegExt (_, _, deg)) = comp_deg_extending deg s in
        Var { level; deg }
    (* To act on a constant, we push as much of the degeneracy through the insertion as possible.  The actual degeneracy that gets pushed through doesn't matter, since it just raises the constant to an even higher dimension, and that dimension is stored in the insertion. *)
    | Const { name; ins } ->
        let (Insfact_comp (_, ins, _, _)) = insfact_comp ins s in
        Const { name; ins }
    (* Acting on a metavariable is similar to a constant, but now the inner degeneracy acts on the stored environment. *)
    | Meta { meta; env; ins } ->
        let (Insfact_comp (deg, ins, _, _)) = insfact_comp ins s in
        Meta { meta; env = act_env env (op_of_deg deg); ins }

  (* Action on a Bwd of applications (each of which is just the argument and its boundary).  Pushes the degeneracy past the stored insertions, factoring it each time and leaving an appropriate insertion on the outside.  Also returns the innermost degeneracy, for acting on the head with. *)
  and act_apps : type a b. app Bwd.t -> (a, b) deg -> any_deg * app Bwd.t =
   fun apps s ->
    match apps with
    | Emp -> (Any_deg s, Emp)
    | Snoc (rest, App (arg, ins)) ->
        (* To act on an application, we compose the acting degeneracy with the delayed insertion, factor the result into a new insertion to leave outside and a smaller degeneracy to push in, and push the smaller degeneracy action into the application, acting on the function/struct. *)
        let (Insfact_comp (fa, new_ins, _, _)) = insfact_comp ins s in
        let new_arg =
          match arg with
          | Arg args ->
              (* And, in the function case, on the arguments by factorization. *)
              Arg (act_cube { act = (fun x s -> act_normal x s) } args fa)
          | Field (fld, fldplus) ->
              (* Note that we don't need to change the degeneracy, since it can be extended on the right as needed. *)
              let (Plus new_fldplus) = D.plus (D.plus_right fldplus) in
              Field (fld, new_fldplus) in
        (* Finally, we recurse and assemble the result. *)
        let new_s, new_rest = act_apps rest fa in
        (new_s, Snoc (new_rest, App (new_arg, new_ins)))

  and act_lazy_eval : type s m n. s lazy_eval -> (m, n) deg -> s lazy_eval =
   fun lev s ->
    match !lev with
    | Deferred_eval (env, tm, ins, apps) ->
        let Any_deg s, apps = act_apps apps s in
        let (Insfact_comp (fa, ins, _, _)) = insfact_comp ins s in
        ref (Deferred_eval (act_env env (op_of_deg fa), tm, ins, apps))
    | Deferred (tm, s', apps) ->
        let Any_deg s, apps = act_apps apps s in
        let (DegExt (_, _, fa)) = comp_deg_extending s' s in
        ref (Deferred (tm, fa, apps))
    | Ready tm -> ref (Deferred ((fun () -> tm), s, Emp))
end

let short_circuit : type m n a. (m, n) deg -> a -> ((m, n) deg -> a) -> a =
 fun s x act ->
  match is_id_deg s with
  | Some _ -> x
  | None -> act s

let act_value tm s = short_circuit s tm (Act.act_value tm)
let act_normal tm s = short_circuit s tm (Act.act_normal tm)
let gact_ty ?err tm ty s = short_circuit s ty (Act.gact_ty ?err tm ty)
let act_ty ?err tm ty s = short_circuit s ty (Act.act_ty ?err tm ty)
let act_evaluation ev s = short_circuit s ev (Act.act_evaluation ev)
let act_lazy_eval v s = short_circuit s v (Act.act_lazy_eval v)

let act_value_cube : type a s m n.
    (a -> s value) -> (n, a) CubeOf.t -> (m, n) deg -> (m, s value) CubeOf.t =
 fun force xs s -> act_cube { act = (fun x s -> act_value (force x) s) } xs s

(* Like apply_lazy for fields.  Was deferred to here since it requires pushing the insertion through with act. *)
let field_lazy : type s n t i. s lazy_eval -> i Field.t -> (n, t, i) insertion -> s lazy_eval =
 fun lev fld fldins ->
  let n, k = (cod_left_ins fldins, cod_right_ins fldins) in
  let (Plus nk) = D.plus k in
  let p = deg_of_perm (perm_inv (perm_of_ins_plus fldins nk)) in
  let fld = App (Field (fld, nk), ins_zero n) in
  match !(act_lazy_eval lev p) with
  | Deferred_eval (env, tm, ins, apps) -> ref (Deferred_eval (env, tm, ins, Snoc (apps, fld)))
  | Deferred (tm, ins, apps) -> ref (Deferred (tm, ins, Snoc (apps, fld)))
  | Ready tm -> ref (Deferred ((fun () -> tm), id_deg D.zero, Snoc (Emp, fld)))
