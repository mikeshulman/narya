open Bwd
open Util
open Dim
open Reporter
open Syntax
open Value

(* Operator actions on values.  Unlike substitution, operator actions take a *value* as input (and produces another value). *)

(* Since values don't have a statically specified dimension, we have to act on them by an *arbitrary* degeneracy, which means that in many places we have to check dynamically that the dimensions either match or can be extended to match.  This function encapsulates that. *)
let deg_plus_to : type m n nk. ?on:string -> ?err:Code.t -> (m, n) deg -> nk D.t -> nk deg_of =
 fun ?on ?err s nk ->
  match factor nk (cod_deg s) with
  | None -> (
      match (err, on) with
      | Some e, _ -> fatal e
      | None, Some x -> fatal (Anomaly ("invalid degeneracy action on " ^ x))
      | None, None -> fatal (Anomaly "invalid degeneracy action"))
  | Some (Factor nk) ->
      let (Plus mk) = D.plus (D.plus_right nk) in
      let sk = deg_plus s nk mk in
      Of sk

(* When acting on a cube of variables that's at least partially split up into normal variables, we have a problem if the degeneracy mixes up the dimensions that are normal with the dimensions that are cube.  We could get around this by storing an 'insertion' rather than a D.plus in a 'variables', but we wouldn't be able to *use* that usefully anywhere, since there's no way to create a partially-cube variable in syntax.  So instead, if the dimensions get mixed up we just give up the split and make it fully-cube using only the previous top variable.  *)
let act_variables : type m n. n variables -> (m, n) deg -> m variables =
 fun (Variables (_, nk, vars)) s ->
  match deg_perm_of_plus nk s with
  | None_deg_perm_of_plus ->
      let m = dom_deg s in
      Variables (m, D.plus_zero m, NICubeOf.singleton (NICubeOf.find_top vars))
  (* If the degeneracy doesn't mix up the normal and cube dimensions, it still might permute the normal ones.  I'm not positive that it makes sense to throw away the degeneracy part here and the permutation part below, but this is the best I can think of.  If it doesn't end up making sense, we may have to revert to making it fully-cube as above. *)
  | Deg_perm_of_plus (mk, s, p) ->
      let m = dom_deg s in
      let module Build = NICubeOf.Traverse (struct
        type 'acc t = unit
      end) in
      let (Wrap (vars, _)) =
        Build.build_left (NICubeOf.dim vars)
          {
            build =
              (fun fa () ->
                let (Face (fb, _)) = perm_sface p fa in
                Fwrap (NFamOf (NICubeOf.find vars fb), ()));
          }
          () in
      Variables (m, mk, vars)

(* Acting on a binder and on other sorts of closures will be unified by the function 'act_closure', but its return value involves an existential type, so it has to be a GADT. *)
type (_, _, _) act_closure =
  | Act_closure : ('m, 'a) env * ('mn, 'm, 'n) insertion -> ('a, 'mn, 'n) act_closure

(* Since a value is either instantiated or uninstantiated, this function just deals with instantiations and lambda-abstractions and passes everything else off to act_uninst. *)
let rec act_value : type m n s. s value -> (m, n) deg -> s value =
 fun v s ->
  match v with
  | Lazy (lazy v) -> act_value v s
  | Uninst (tm, (lazy ty)) -> Uninst (act_uninst tm s, Lazy.from_val (act_ty v ty s))
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
      (* This is the boundary of "act_value_cube tys' fa", but computing it that way would also try to compute the inner filler, which would be an infinite loop. *)
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
  | Struct (fields, ins) ->
      let (Insfact_comp (fa, new_ins, _, _)) = insfact_comp ins s in
      Struct
        (Abwd.map (fun (tm, l) -> (lazy (act_evaluation (Lazy.force tm) fa), l)) fields, new_ins)
  | Constr (name, dim, args) ->
      let (Of fa) = deg_plus_to s dim ~on:"constr" in
      Constr (name, dom_deg fa, List.map (fun tm -> act_value_cube tm fa) args)

and act_evaluation : type m n s. s evaluation -> (m, n) deg -> s evaluation =
 fun tm s ->
  match tm with
  | Unrealized -> Unrealized
  | Realize tm -> Realize (act_value tm s)
  | Val tm -> Val (act_value tm s)
  | Canonical c -> Canonical (act_canonical c s)

and act_alignment : type m n h. h alignment -> (m, n) deg -> h alignment =
 fun alignment s ->
  match alignment with
  | True -> True
  | Chaotic tm -> Chaotic (act_value tm s)
  | Lawful tm -> Lawful (act_canonical tm s)

and act_canonical : type m n. canonical -> (m, n) deg -> canonical =
 fun tm s ->
  match tm with
  | Data { dim; indices; missing; constrs } ->
      let (Of fa) = deg_plus_to s dim in
      Data
        {
          dim = dom_deg fa;
          indices = Bwv.map (fun ixs -> act_normal_cube ixs fa) indices;
          missing;
          constrs = Constr.Map.map (fun c -> act_dataconstr c fa) constrs;
        }
  | Codata { eta; env; ins; fields } ->
      let (Of fa) = deg_plus_to s (dom_ins ins) in
      let (Act_closure (env, ins)) = act_closure env ins fa in
      Codata { eta; env; ins; fields }

and act_dataconstr : type m n i. (n, i) dataconstr -> (m, n) deg -> (m, i) dataconstr =
 fun (Dataconstr { env; args; indices }) s ->
  let env = Act (env, op_of_deg s) in
  Dataconstr { env; args; indices }

and act_uninst : type m n. uninst -> (m, n) deg -> uninst =
 fun tm s ->
  match tm with
  | Neu { head; args; alignment } ->
      (* We act on the applications from the outside (last) to the inside, since the degeneracy has to be factored and may leave neutral insertions behind.  The resulting inner degeneracy then acts on the head. *)
      let Any s', args = act_apps args s in
      let head = act_head head s' in
      (* We act on the alignment separately with the original s, since (e.g.) a chaotic alignment is a "value" of the entire application spine, not just the head. *)
      let alignment = act_alignment alignment s in
      Neu { head; args; alignment }
  | UU nk ->
      let (Of fa) = deg_plus_to s nk ~on:"universe" in
      UU (dom_deg fa)
  | Pi (x, doms, cods) ->
      let k = CubeOf.dim doms in
      let (Of fa) = deg_plus_to s k ~on:"pi-type" in
      let mi = dom_deg fa in
      let doms' = act_value_cube doms fa in
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
and act_closure :
    type mn m n a kn. (m, a) env -> (mn, m, n) insertion -> (kn, mn) deg -> (a, kn, n) act_closure =
 fun env ins fa ->
  let (Insfact (fc, ins)) = insfact (comp_deg (perm_of_ins ins) fa) (plus_of_ins ins) in
  Act_closure (Act (env, op_of_deg fc), ins)

and act_binder : type mn kn s. (mn, s) binder -> (kn, mn) deg -> (kn, s) binder =
 fun (Bind { env; ins; body }) fa ->
  let (Act_closure (env, ins)) = act_closure env ins fa in
  Bind { env; ins; body }

and act_normal : type a b. normal -> (a, b) deg -> normal =
 fun { tm; ty } s -> { tm = act_value tm s; ty = act_ty tm ty s }

(* When acting on a neutral or normal, we also need to specify the typed of the output.  This *isn't* act_value on the original type; instead the type is required to be fully instantiated and the operator acts on the *instantiated* dimensions, in contrast to how act_value on an instantiation acts on the *uninstantiated* dimensions.  This function computes this "type of acted terms". *)
and act_ty : type a b. ?err:Code.t -> kinetic value -> kinetic value -> (a, b) deg -> kinetic value
    =
 fun ?err tm tmty s ->
  match tmty with
  | Lazy (lazy tmty) -> act_ty ?err tm tmty s
  | Inst { tm = ty; dim; args; tys = _ } -> (
      (* A type must be fully instantiated, so in particular tys is trivial. *)
      match D.compare (TubeOf.uninst args) D.zero with
      | Neq -> fatal (Anomaly "act_ty applied to non-fully-instantiated term")
      | Eq ->
          let Eq = D.plus_uniq (TubeOf.plus args) (D.zero_plus (TubeOf.inst args)) in
          (* This can be a user error, e.g. when trying to symmetrize a 1-dimensional thing, so we allow the caller to provide a different error code. *)
          let (Of fa) = deg_plus_to s (TubeOf.inst args) ?err ~on:"instantiated type" in
          (* The arguments of a full instantiation are missing only the top face, which is filled in by the term belonging to it. *)
          let args' = TubeOf.plus_cube args (CubeOf.singleton { tm; ty = tmty }) in
          (* We build the new arguments by factorization and action.  Note that the one missing face would be "act_value tm s", which would be an infinite loop in case tm is a neutral.  (Hence why we can't use call act_normal_cube and then take the boundary.) *)
          let args =
            TubeOf.build D.zero
              (D.zero_plus (dom_deg fa))
              {
                build =
                  (fun fb ->
                    let (Op (fd, fc)) = deg_sface fa (sface_of_tface fb) in
                    act_normal (CubeOf.find args' fd) fc);
              } in
          Inst { tm = act_uninst ty s; dim = pos_deg dim fa; args; tys = TubeOf.empty D.zero })
  | Uninst (ty, (lazy uu)) -> (
      (* This is just the case when dim = 0, so it is the same except simpler. *)
      let fa = s in
      match (D.compare (cod_deg fa) D.zero, uu) with
      (* This can also be a user error, e.g. symmetrizing a 0-dimensional thing, so we allow the caller to provide a different error code. *)
      | Neq, _ ->
          fatal
            (Option.value ~default:(Anomaly "invalid degeneracy action on uninstantiated type") err)
      | Eq, Uninst (UU z, _) -> (
          match D.compare z D.zero with
          | Neq -> fatal (Anomaly "acting on non-fully-instantiated type as a type")
          | Eq -> (
              match D.compare_zero (dom_deg fa) with
              | Zero -> Uninst (act_uninst ty fa, lazy uu)
              | Pos dim ->
                  let args =
                    TubeOf.build D.zero
                      (D.zero_plus (dom_deg fa))
                      {
                        build =
                          (fun fb ->
                            let (Op (_, fc)) = deg_sface fa (sface_of_tface fb) in
                            act_normal { tm; ty = tmty } fc);
                      } in
                  Inst { tm = act_uninst ty fa; dim; args; tys = TubeOf.empty D.zero }))
      | _ -> fatal (Anomaly "acting on non-type as if a type"))
  | Lam _ -> fatal (Anomaly "a lambda-abstraction cannot be a type to act on")
  | Struct _ -> fatal (Anomaly "a struct cannot be a type to act on")
  | Constr _ -> fatal (Anomaly "a constructor cannot be a type to act on")

(* Action on a head *)
and act_head : type a b h. h head -> (a, b) deg -> h head =
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
      Meta { meta; env = Act (env, op_of_deg deg); ins }

(* Action on a Bwd of applications (each of which is just the argument and its boundary).  Pushes the degeneracy past the stored insertions, factoring it each time and leaving an appropriate insertion on the outside.  Also returns the innermost degeneracy, for acting on the head with. *)
and act_apps : type a b. app Bwd.t -> (a, b) deg -> any_deg * app Bwd.t =
 fun apps s ->
  match apps with
  | Emp -> (Any s, Emp)
  | Snoc (rest, App (arg, ins)) ->
      (* To act on an application, we compose the acting degeneracy with the delayed insertion, factor the result into a new insertion to leave outside and a smaller degeneracy to push in, and push the smaller degeneracy action into the application, acting on the function/struct. *)
      let (Insfact_comp (fa, new_ins, _, _)) = insfact_comp ins s in
      let new_arg =
        match arg with
        | Arg args ->
            (* And, in the function case, on the arguments by factorization. *)
            Arg (act_normal_cube args fa)
        | Field fld -> Field fld in
      (* Finally, we recurse and assemble the result. *)
      let new_s, new_rest = act_apps rest fa in
      (new_s, Snoc (new_rest, App (new_arg, new_ins)))

(* Act on a cube of objects *)
and act_value_cube : type m n s. (n, s value) CubeOf.t -> (m, n) deg -> (m, s value) CubeOf.t =
 fun xs fa ->
  CubeOf.build (dom_deg fa)
    {
      build =
        (fun fb ->
          let (Op (fd, fc)) = deg_sface fa fb in
          act_value (CubeOf.find xs fd) fc);
    }

and act_normal_cube : type m n. (n, normal) CubeOf.t -> (m, n) deg -> (m, normal) CubeOf.t =
 fun xs fa ->
  CubeOf.build (dom_deg fa)
    {
      build =
        (fun fb ->
          let (Op (fd, fc)) = deg_sface fa fb in
          act_normal (CubeOf.find xs fd) fc);
    }

(* A version that takes the degeneracy wrapped. *)
let act_any : type s. s value -> any_deg -> s value = fun v (Any s) -> act_value v s
