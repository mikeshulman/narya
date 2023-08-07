open Dim
open Value

(* Operator actions on values.  Unlike substitution, operator actions take a *value* as input (and produces another value). *)

exception Invalid_uninst_action

(* Since values don't have a statically specified dimension, we have to act on them by an *arbitrary* degeneracy, which means that in many places we have to check dynamically that the dimensions either match or can be extended to match.  This function encapsulates that. *)
let deg_plus_to : type m n nk. (m, n) deg -> nk D.t -> string -> nk deg_of =
 fun s nk err ->
  match factor nk (cod_deg s) with
  | None -> raise (Failure ("Invalid degeneracy action on " ^ err))
  | Some (Factor nk) ->
      let (Has_plus mk) = D.plus (D.plus_right nk) in
      let sk = deg_plus s nk mk in
      Of sk

(* Existential GADT that encapsulates the output of acting on a binder, along with the extended degeneracy so that it can be used elsewhere with the same dimension. *)
type _ plus_binder = Binder : ('mi, 'ni) deg * 'mi binder -> 'ni plus_binder

(* Since a value is either instantiated or uninstantiated, this function just deals with instantiations and passes everything else off to act_uninst. *)
let rec act_value : type m n. value -> (m, n) deg -> value =
 fun v s ->
  match v with
  | Uninst tm -> Uninst (act_uninst tm s)
  | Inst { tm; dim; tube; args } ->
      let (Of fa) = deg_plus_to s (tube_uninst tube) "instantiation" in
      (* The action on an instantiation instantiates the same dimension j, but the leftover dimensions are now the domain of the degeneracy. *)
      let j = tube_inst tube in
      let (Tube t) = tube in
      let nj = t.plus_dim in
      (* Collate the supplied arguments into a hashtable for random access *)
      let argtbl = Hashtbl.create 10 in
      let () = Bwv.iter2 (Hashtbl.add argtbl) (Bwv.take t.plus_faces (sfaces t.total_faces)) args in
      (* Create a new tube for the new arguments *)
      let m = dom_deg fa in
      let (Has_tube tube) = has_tube m j in
      let (Tube t) = tube in
      (* The new arguments are obtained by factoring and acting on appropriate original arguments *)
      let args =
        Bwv.map
          (fun (SFace_of fed) ->
            let (SFace_of_plus (_, fb, fd)) = sface_of_plus t.plus_dim fed in
            let (Op (fe, fs)) = deg_sface fa fb in
            let (Has_plus q) = D.plus (dom_sface fd) in
            act_value (Hashtbl.find argtbl (SFace_of (sface_plus_sface fe nj q fd))) fs)
          (Bwv.take t.plus_faces (sfaces t.total_faces)) in
      Inst { tm = act_uninst tm fa; dim; tube; args }

and act_uninst : type m n. uninst -> (m, n) deg -> uninst =
 fun tm s ->
  match tm with
  | Neu (ne, ty) -> Neu (act_neu ne s, act_ty (Uninst tm) ty s)
  | UU nk ->
      let (Of fa) = deg_plus_to s nk "universe" in
      UU (dom_deg fa)
  | Lam body ->
      let (Of fa) = deg_plus_to s (dim_binder body) "lambda" in
      Lam (act_binder body fa)
  | Pi (ni_faces, doms, cod) ->
      let (Of fa) = deg_plus_to s (dim_binder cod) "pi-type" in
      let domtbl = Hashtbl.create 10 in
      let () = Bwv.iter2 (Hashtbl.add domtbl) (sfaces ni_faces) doms in
      let (Has_faces mi_faces) = count_faces (dom_deg fa) in
      let doms' =
        Bwv.map
          (fun (SFace_of fb) ->
            let (Op (fc, fd)) = deg_sface fa fb in
            act_value (Hashtbl.find domtbl (SFace_of fc)) fd)
          (sfaces mi_faces) in
      let cod' = act_binder cod fa in
      Pi (mi_faces, doms', cod')

and act_binder : type m n. n binder -> (m, n) deg -> m binder =
 fun (Bind { env; perm; plus_dim; bound_faces; plus_faces; body; env_faces; args }) fa ->
  let m = dim_env env in
  let m_n = plus_dim in
  (* let n = D.plus_right m_n in *)
  let mn = D.plus_out m m_n in
  (* We factor the degeneracy as a strict degeneracy determined by fc, following a permutation fb (which happens to be an insertion). *)
  let (Insfact (fc, ins)) = insfact fa (D.zero_plus mn) in
  let j_mn = plus_of_ins ins in
  let fb = perm_of_ins ins in
  let fbinv = perm_inv fb in
  let j = dom_deg fc in
  (* The permutation fb is composed with (a whiskering of) the previous stored permutation to become the new one. *)
  let perm = comp_perm (plus_perm j j_mn perm) fb in
  (* The strict degeneracy fc acts on the stored environment *)
  let (Has_plus jm) = D.plus m in
  let fcm = deg_plus fc (D.zero_plus m) jm in
  let env = Act (env, op_of_deg fcm) in
  (* Now we have to assemble the arguments.  First we compute some faces. *)
  let plus_dim = D.plus_assocl jm plus_dim j_mn in
  let m_faces = sfaces env_faces in
  let (Has_faces env_faces) = count_faces (D.plus_out j jm) in
  let n_faces = sfaces bound_faces in
  let jm_faces = sfaces env_faces in
  (* We collate the previous argument matrix in a hashtable for random access *)
  let tbl = Hashtbl.create 10 in
  let () =
    Bwv.iter2
      (fun x v -> Bwv.iter2 (fun y arg -> Hashtbl.add tbl (y, x) arg) m_faces v)
      n_faces args in
  (* Now to make the new argument matrix... *)
  let args =
    Bwv.map
      (fun (SFace_of fv) ->
        (* let c = dom_sface fv in *)
        Bwv.map
          (fun (SFace_of frfu) ->
            (* ...we split the face of j+m into a face fr of j and a face fu of m... *)
            let (SFace_of_plus (_, fr, fu)) = sface_of_plus jm frfu in
            (* ...combine the face fu of m and the face fv of n using the previous argument matrix... *)
            let (Face_of fs) = Hashtbl.find tbl (SFace_of fu, SFace_of fv) in
            let (Has_plus ci) = D.plus (dom_face fs) in
            (* ...add the resulting face to fr... *)
            let frfs = face_plus_face (face_of_sface fr) j_mn ci fs in
            (* ...and combine it with the inverse of fb from above. *)
            Face_of (comp_face (face_of_perm fbinv) frfs))
          jm_faces)
      n_faces in
  Bind { env; perm; plus_dim; bound_faces; plus_faces; body; env_faces; args }

and act_normal : type a b. normal -> (a, b) deg -> normal =
 fun { tm; ty } s -> { tm = act_value tm s; ty = act_ty tm ty s }

(* The type annotation of a neutral or normal isn't just act_value on the type, but is further instantiated to describe the boundary of a degeneracy in terms of the original term and its degeneracies.  This function computes that. *)
and act_ty : type a b. value -> value -> (a, b) deg -> value =
 fun tm ty s ->
  match ty with
  | Inst { tm = ty; dim; tube; args } -> (
      let (Of fa) = deg_plus_to s (tube_inst tube) "instantiated type" in
      (* A type must be fully instantiated *)
      match compare (tube_uninst tube) D.zero with
      | Neq -> raise (Failure "act_ty applied to non-fully-instantiated term")
      | Eq ->
          (* The arguments of a full instantiation are missing only the top face, which is filled in by the term belonging to it. *)
          let (Tube t) = tube in
          let Eq = faces_uniq t.missing_faces faces_zero in
          let Eq = D.plus_uniq t.plus_dim (D.zero_plus (tube_inst tube)) in
          let (Suc Zero) = t.plus_faces in
          let args' = Bwv.Snoc (args, tm) in
          (* We collate the arguments into a hashtable for random access *)
          let argstbl = Hashtbl.create 10 in
          let () = Bwv.iter2 (Hashtbl.add argstbl) (sfaces t.total_faces) args' in
          (* We construct a new tube for a full instantiation *)
          let m = dom_deg fa in
          let (Has_tube tube) = has_tube D.zero m in
          let (Tube t) = tube in
          let Eq = faces_uniq t.missing_faces faces_zero in
          let Eq = D.plus_uniq t.plus_dim (D.zero_plus m) in
          let (Suc Zero) = t.plus_faces in
          let (Snoc (new_faces, _)) = sfaces t.total_faces in
          (* And we build the argument list by factorization and action.  Note that the one missing face would be "act_value tm s", which would be an infinite loop in case tm is a neutral. *)
          let args =
            Bwv.map
              (fun (SFace_of fb) ->
                let (Op (fd, fc)) = deg_sface fa fb in
                act_value (Hashtbl.find argstbl (SFace_of fd)) fc)
              new_faces in
          Inst { tm = act_uninst ty s; dim = pos_deg dim fa; tube; args })
  | Uninst ty -> (
      (* This case is the same, but simpler. *)
      let fa = s in
      match compare (cod_deg fa) D.zero with
      (* We raise a custom exception here so that it can get caught by type synthesis, if we try to symmetrize something that's not at least 2-dimensional. *)
      | Neq -> raise Invalid_uninst_action
      | Eq -> (
          match D.compare_zero (dom_deg fa) with
          | Zero -> Uninst (act_uninst ty fa)
          | Pos dim ->
              let m = dom_deg fa in
              let (Has_tube tube) = has_tube D.zero m in
              let (Tube t) = tube in
              let Eq = faces_uniq t.missing_faces faces_zero in
              let Eq = D.plus_uniq t.plus_dim (D.zero_plus m) in
              let (Suc Zero) = t.plus_faces in
              let (Snoc (new_faces, _)) = sfaces t.total_faces in
              let args =
                Bwv.map
                  (fun (SFace_of fb) ->
                    let (Op (_, fc)) = deg_sface fa fb in
                    act_value tm fc)
                  new_faces in
              Inst { tm = act_uninst ty fa; dim; tube; args }))

and act_neu : type a b. neu -> (a, b) deg -> neu =
 fun ne s ->
  match ne with
  | Var { level; deg } ->
      (* To act on a variable, we just accumulate the delayed action. *)
      let (DegExt (_, _, deg)) = comp_deg_extending deg s in
      Var { level; deg }
  | App { fn; app_faces; args; ins } ->
      (* To act on an application, we compose with the delayed insertion *)
      let nk = plus_of_ins ins in
      let s' = perm_of_ins ins in
      let (DegExt (_, nk_d, s's)) = comp_deg_extending s' s in
      let (Has_plus kd) = D.plus (D.plus_right nk_d) in
      let n_kd = D.plus_assocr nk kd nk_d in
      (* Factor the result into a new insertion and a smaller degeneracy *)
      let (Insfact (fa, ins)) = insfact s's n_kd in
      (* Collate the supplied arguments into a hashtable for random access *)
      let ntbl = Hashtbl.create 10 in
      let () = Bwv.iter2 (Hashtbl.add ntbl) (sfaces app_faces) args in
      (* And push the smaller degeneracy action into the application, acting on the function *)
      let fn = act_neu fn fa in
      let p = dom_deg fa in
      let (Has_faces app_faces) = count_faces p in
      (* And on the arguments, by factorization *)
      let args =
        Bwv.map
          (fun (SFace_of fb) ->
            let (Op (fd, fc)) = deg_sface fa fb in
            act_normal (Hashtbl.find ntbl (SFace_of fd)) fc)
          (sfaces app_faces) in
      App { fn; app_faces; args; ins }

(* A version that takes the degeneracy wrapped. *)
let act_any : value -> any_deg -> value = fun v (Any s) -> act_value v s
