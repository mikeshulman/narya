open Bwd
open Util
open Dim
open Reporter
open Syntax
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
  let rec act_value : type m n s. s value -> (m, n) deg -> s value =
   fun v s ->
    match v with
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
    | Struct (fields, ins, energy) ->
        let (Insfact_comp (fa, new_ins, _, _)) = insfact_comp ins s in
        Struct (Abwd.map (fun (tm, l) -> (act_lazy_eval tm fa, l)) fields, new_ins, energy)
    | Constr (name, dim, args) ->
        let (Of fa) = deg_plus_to s dim ~on:"constr" in
        Constr
          ( name,
            dom_deg fa,
            List.map (fun tm -> act_cube { act = (fun x s -> act_value x s) } tm fa) args )

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
    | Codata { eta; opacity; env; ins; fields } ->
        let (Of fa) = deg_plus_to ~on:"codata" s (dom_ins ins) in
        let (Act_closure (env, ins)) = act_closure env ins fa in
        Any (Codata { eta; opacity; env; ins; fields })

  and act_dataconstr : type m n i. (n, i) dataconstr -> (m, n) deg -> (m, i) dataconstr =
   fun (Dataconstr { env; args; indices }) s ->
    let env = act_env env (op_of_deg s) in
    Dataconstr { env; args; indices }

  and act_uninst : type m n. uninst -> (m, n) deg -> uninst =
   fun tm s ->
    match tm with
    | Neu { head; args; value } ->
        (* We act on the applications from the outside (last) to the inside, since the degeneracy has to be factored and may leave neutral insertions behind.  The resulting inner degeneracy then acts on the head. *)
        let Any s', args = act_apps args s in
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
  and act_closure :
      type mn m n a kn. (m, a) env -> (mn, m, n) insertion -> (kn, mn) deg -> (a, kn, n) act_closure
      =
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
  and gact_ty :
      type a b. ?err:Code.t -> kinetic value option -> kinetic value -> (a, b) deg -> kinetic value
      =
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

  and act_ty :
      type a b p. ?err:Code.t -> kinetic value -> kinetic value -> (a, b) deg -> kinetic value =
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
    | Emp -> (Any s, Emp)
    | Snoc (rest, App (arg, ins)) ->
        (* To act on an application, we compose the acting degeneracy with the delayed insertion, factor the result into a new insertion to leave outside and a smaller degeneracy to push in, and push the smaller degeneracy action into the application, acting on the function/struct. *)
        let (Insfact_comp (fa, new_ins, _, _)) = insfact_comp ins s in
        let new_arg =
          match arg with
          | Arg args ->
              (* And, in the function case, on the arguments by factorization. *)
              Arg (act_cube { act = (fun x s -> act_normal x s) } args fa)
          | Field fld -> Field fld in
        (* Finally, we recurse and assemble the result. *)
        let new_s, new_rest = act_apps rest fa in
        (new_s, Snoc (new_rest, App (new_arg, new_ins)))

  and act_lazy_eval : type s m n. s lazy_eval -> (m, n) deg -> s lazy_eval =
   fun lev s ->
    match !lev with
    | Deferred_eval (env, tm, ins, apps) ->
        let Any s, apps = act_apps apps s in
        let (Insfact_comp (fa, ins, _, _)) = insfact_comp ins s in
        ref (Deferred_eval (act_env env (op_of_deg fa), tm, ins, apps))
    | Deferred (tm, s', apps) ->
        let Any s, apps = act_apps apps s in
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

let act_value_cube :
    type a s m n. (a -> s value) -> (n, a) CubeOf.t -> (m, n) deg -> (m, s value) CubeOf.t =
 fun force xs s -> act_cube { act = (fun x s -> act_value (force x) s) } xs s
