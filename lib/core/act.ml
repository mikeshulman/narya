open Util
open Dim
open Value
open Bwd

(* Operator actions on values.  Unlike substitution, operator actions take a *value* as input (and produces another value). *)

exception Invalid_uninst_action

(* Since values don't have a statically specified dimension, we have to act on them by an *arbitrary* degeneracy, which means that in many places we have to check dynamically that the dimensions either match or can be extended to match.  This function encapsulates that. *)
let deg_plus_to : type m n nk. (m, n) deg -> nk D.t -> string -> nk deg_of =
 fun s nk err ->
  match factor nk (cod_deg s) with
  | None -> raise (Failure ("Invalid degeneracy action on " ^ err))
  | Some (Factor nk) ->
      let (Plus mk) = D.plus (D.plus_right nk) in
      let sk = deg_plus s nk mk in
      Of sk

(* Existential GADT that encapsulates the output of acting on a binder, along with the extended degeneracy so that it can be used elsewhere with the same dimension. *)
type _ plus_binder = Binder : ('mi, 'ni) deg * 'mi binder -> 'ni plus_binder

(* Since a value is either instantiated or uninstantiated, this function just deals with instantiations and lambda-abstractions and passes everything else off to act_uninst. *)
let rec act_value : type m n. value -> (m, n) deg -> value =
 fun v s ->
  match v with
  | Uninst (tm, (lazy ty)) -> Uninst (act_uninst tm s, lazy (act_ty v ty s))
  | Inst { tm; dim; args; tys } ->
      let (Of fa) = deg_plus_to s (TubeOf.uninst args) "instantiation" in
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
  | Lam body ->
      let (Of fa) = deg_plus_to s (dim_binder body) "lambda" in
      Lam (act_binder body fa)
  | Struct (fields, ins) ->
      let (Insfact_comp (fa, new_ins)) = insfact_comp ins s in
      Struct (Field.Map.map (fun tm -> act_value tm fa) fields, new_ins)
  | Constr (name, dim, args) ->
      let (Of fa) = deg_plus_to s dim "constr" in
      Constr
        ( name,
          dom_deg fa,
          Bwd.map
            (fun tm ->
              CubeOf.build (dom_deg fa)
                {
                  build =
                    (fun fb ->
                      let (Op (fc, fd)) = deg_sface fa fb in
                      act_value (CubeOf.find tm fc) fd);
                })
            args )

and act_uninst : type m n. uninst -> (m, n) deg -> uninst =
 fun tm s ->
  match tm with
  | Neu (fn, args) ->
      (* We act on the applications from the outside (last) to the inside, since the degeneracy has to be factored and may leave neutral insertions behind.  The resulting inner degeneracy then acts on the head. *)
      let Any s', args = act_apps args s in
      let fn = act_head fn s' in
      Neu (fn, args)
  | UU nk ->
      let (Of fa) = deg_plus_to s nk "universe" in
      UU (dom_deg fa)
  | Pi (doms, cods) ->
      let k = CubeOf.dim doms in
      let (Of fa) = deg_plus_to s k "pi-type" in
      let mi = dom_deg fa in
      let doms' =
        CubeOf.build mi
          {
            build =
              (fun fb ->
                let (Op (fc, fd)) = deg_sface fa fb in
                act_value (CubeOf.find doms fc) fd);
          } in
      let cods' =
        BindCube.build mi
          {
            build =
              (fun fb ->
                let (Op (fc, fd)) = deg_sface fa fb in
                act_binder (BindCube.find cods fc) fd);
          } in
      Pi (doms', cods')
  | Canonical (name, args, ins) ->
      (* Similar to act_apps, but without needing to thread through changes in the insertion, since the intermediate applications lie in 0-dimensional types and hence any degeneracy action can be pushed inside except possibly after the complete application (if the end result is a higher-dimensional type). *)
      let (Insfact_comp (fa, new_ins)) = insfact_comp ins s in
      let p = dom_deg fa in
      let new_args =
        Bwd.map
          (fun arg ->
            CubeOf.build p
              {
                build =
                  (fun fb ->
                    let (Op (fd, fc)) = deg_sface fa fb in
                    act_normal (CubeOf.find arg fd) fc);
              })
          args in
      Canonical (name, new_args, new_ins)

and act_binder : type m n. n binder -> (m, n) deg -> m binder =
 fun (Bind { env; perm; plus_dim; bound_faces; plus_faces; body; args }) fa ->
  let m = dim_env env in
  let m_n = plus_dim in
  (* let n = D.plus_right m_n in *)
  let mn = D.plus_out m m_n in
  (* We factor the degeneracy as a strict degeneracy determined by fc, following a permutation fb (a.k.a. an insertion into zero). *)
  let (Insfact (fc, ins)) = insfact fa (D.zero_plus mn) in
  let j_mn = plus_of_ins ins in
  let fb = perm_of_ins ins in
  let fbinv = perm_inv fb in
  let j = dom_deg fc in
  (* The permutation fb is composed with (a whiskering of) the previous stored permutation to become the new one. *)
  let perm = comp_perm (plus_perm j j_mn perm) fb in
  (* The strict degeneracy fc acts on the stored environment *)
  let (Plus jm) = D.plus m in
  let fcm = deg_plus fc (D.zero_plus m) jm in
  let env = Act (env, op_of_deg fcm) in
  (* Now we have to assemble the arguments.  First we compute some faces. *)
  let plus_dim = D.plus_assocl jm plus_dim j_mn in
  let n_faces = sfaces bound_faces in
  (* We collate the previous argument matrix in a hashtable for random access *)
  let tbl = Hashtbl.create 10 in
  let () =
    Bwv.iter2
      (fun x v ->
        CubeOf.miter { it = (fun y [ arg ] -> Hashtbl.add tbl (SFace_of y, x) arg) } [ v ])
      n_faces args in
  (* Now to make the new argument matrix... *)
  let args =
    Bwv.map
      (fun (SFace_of fv) ->
        (* let c = dom_sface fv in *)
        CubeOf.build (D.plus_out j jm)
          {
            build =
              (fun frfu ->
                (* ...we split the face of j+m into a face fr of j and a face fu of m... *)
                let (SFace_of_plus (_, fr, fu)) = sface_of_plus jm frfu in
                (* ...combine the face fu of m and the face fv of n using the previous argument matrix... *)
                let (Face_of fs) = Hashtbl.find tbl (SFace_of fu, SFace_of fv) in
                let (Plus ci) = D.plus (dom_face fs) in
                (* ...add the resulting face to fr... *)
                let frfs = face_plus_face (face_of_sface fr) j_mn ci fs in
                (* ...and combine it with the inverse of fb from above. *)
                Face_of (comp_face (face_of_perm fbinv) frfs));
          })
      n_faces in
  Bind { env; perm; plus_dim; bound_faces; plus_faces; body; args }

and act_normal : type a b. normal -> (a, b) deg -> normal =
 fun { tm; ty } s -> { tm = act_value tm s; ty = act_ty tm ty s }

(* When acting on a neutral or normal, we also need to specify the typed of the output.  This *isn't* act_value on the original type; instead the type is required to be fully instantiated and the operator acts on the *instantiated* dimensions, in contrast to how act_value on an instantiation acts on the *uninstantiated* dimensions.  This function computes this "type of acted terms". *)
and act_ty : type a b. value -> value -> (a, b) deg -> value =
 fun tm tmty s ->
  match tmty with
  | Inst { tm = ty; dim; args; tys = _ } -> (
      (* A type must be fully instantiated, so in particular tys is trivial. *)
      match compare (TubeOf.uninst args) D.zero with
      | Neq -> raise (Failure "act_ty applied to non-fully-instantiated term")
      | Eq -> (
          let Eq = D.plus_uniq (TubeOf.plus args) (D.zero_plus (TubeOf.inst args)) in
          (* This is a user error, e.g. trying to symmetrize a 1-dimensional thing.  So we raise a custom exception here, that can get caught by type synthesis and turned into an error. *)
          match deg_plus_to s (TubeOf.inst args) "instantiated type" with
          | exception _ -> raise Invalid_uninst_action
          | Of fa ->
              (* The arguments of a full instantiation are missing only the top face, which is filled in by the term belonging to it. *)
              let args' = TubeOf.plus_cube args (CubeOf.singleton { tm; ty = tmty }) in
              (* We build the new arguments by factorization and action.  Note that the one missing face would be "act_value tm s", which would be an infinite loop in case tm is a neutral. *)
              let args =
                TubeOf.build D.zero
                  (D.zero_plus (dom_deg fa))
                  {
                    build =
                      (fun fb ->
                        let (Op (fd, fc)) = deg_sface fa (sface_of_tface fb) in
                        act_normal (CubeOf.find args' fd) fc);
                  } in
              Inst { tm = act_uninst ty s; dim = pos_deg dim fa; args; tys = TubeOf.empty D.zero }))
  | Uninst (ty, (lazy uu)) -> (
      (* This is just the case when dim = 0, so it is the same except simpler. *)
      let fa = s in
      match (compare (cod_deg fa) D.zero, uu) with
      (* Again this is a user error, this time of trying to symmetrize a 0-dimensional thing. *)
      | Neq, _ -> raise Invalid_uninst_action
      | Eq, Uninst (UU z, _) -> (
          match compare z D.zero with
          | Neq -> raise (Failure "Acting on non-fully-instantiated type as a type")
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
      | _ -> raise (Failure "Acting on non-type as if a type"))
  | Lam _ -> raise (Failure "A lambda-abstraction cannot be a type to act on")
  | Struct _ -> raise (Failure "A struct cannot be a type to act on")
  | Constr _ -> raise (Failure "A constructor cannot be a type to act on")

(* Action on a head *)
and act_head : type a b. head -> (a, b) deg -> head =
 fun ne s ->
  match ne with
  (* To act on a variable, we just accumulate the delayed action. *)
  | Var { level; deg } ->
      let (DegExt (_, _, deg)) = comp_deg_extending deg s in
      Var { level; deg }
  (* To act on a constant, we just change its dimension.  This is correct because all constants are originally zero-dimensional, so an n-dimensional one is already a substitution along (Emp n).  *)
  | Const { name; dim } ->
      let (Of s') = deg_plus_to s dim "constant" in
      Const { name; dim = dom_deg s' }

(* Action on a Bwd of applications (each of which is just the argument and its boundary).  Pushes the degeneracy past the stored insertions, factoring it each time and leaving an appropriate insertion on the outside.  Also returns the innermost degeneracy, for acting on the head with. *)
and act_apps : type a b. app Bwd.t -> (a, b) deg -> any_deg * app Bwd.t =
 fun apps s ->
  match apps with
  | Emp -> (Any s, Emp)
  | Snoc (rest, App (arg, ins)) ->
      (* To act on an application, we compose the acting degeneracy with the delayed insertion, factor the result into a new insertion to leave outside and a smaller degeneracy to push in, and push the smaller degeneracy action into the application, acting on the function/struct. *)
      let (Insfact_comp (fa, new_ins)) = insfact_comp ins s in
      let p = dom_deg fa in
      let new_arg =
        match arg with
        | Arg args ->
            (* And, in the function case, on the arguments by factorization. *)
            Arg
              (CubeOf.build p
                 {
                   build =
                     (fun fb ->
                       let (Op (fd, fc)) = deg_sface fa fb in
                       act_normal (CubeOf.find args fd) fc);
                 })
        | Field fld -> Field fld in
      (* Finally, we recurse and assemble the result. *)
      let new_s, new_rest = act_apps rest fa in
      (new_s, Snoc (new_rest, App (new_arg, new_ins)))

(* A version that takes the degeneracy wrapped. *)
let act_any : value -> any_deg -> value = fun v (Any s) -> act_value v s
