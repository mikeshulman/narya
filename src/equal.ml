open Dim
open Value
open Norm
open Monoid
open Monad.ZeroOps (Monad.Maybe)

(* Eta-expanding equality checks.  The integer is the current De Bruijn level, i.e. the length of the current context (we don't need any other information about the context). *)

let rec equal_nf : int -> normal -> normal -> unit option =
 fun n x y ->
  (* TODO: Are we supposed to check that the types are equal, or just assume it? *)
  equal_at n x.tm y.tm x.ty

and equal_at : int -> value -> value -> value -> unit option =
 fun n x y ty ->
  match ty with
  | Uninst tm -> equal_at_uninst n x y tm tube_zero Emp
  | Inst { tm; dim = _; tube; args } -> equal_at_uninst n x y tm tube args
  | Lam _ -> raise (Failure "Lambda-abstraction is not a type for equality-checking")

and equal_at_uninst :
    type m n f.
    int -> value -> value -> uninst -> (m, n, f) count_tube -> (value, f) Bwv.t -> unit option =
 fun n x y ty tube args ->
  match ty with
  | Pi (dom_faces, doms, cod) -> (
      match (compare (tube_uninst tube) D.zero, compare (tube_inst tube) (dim_faces dom_faces)) with
      | Neq, _ -> raise (Failure "Non-fully-instantiated type in equality-checking")
      | _, Neq -> raise (Failure "Instantiation mismatch in equality-checking")
      | Eq, Eq ->
          let (Tube t) = tube in
          let m = tube_inst tube in
          let Eq = D.plus_uniq t.plus_dim (D.zero_plus m) in
          let Eq = faces_uniq t.total_faces dom_faces in
          let Eq = faces_uniq t.missing_faces faces_zero in
          let Eq = N.plus_uniq t.plus_faces (Suc Zero) in
          let df = sfaces dom_faces in
          let curlvl = ref n in
          let argtbl = Hashtbl.create 10 in
          let () =
            Bwv.iter2
              (fun (SFace_of fa) dom ->
                let level = !curlvl in
                let () = curlvl := !curlvl + 1 in
                let k = dom_sface fa in
                let (Has_tube (Tube t)) = has_tube D.zero k in
                let Eq = D.plus_uniq t.plus_dim (D.zero_plus k) in
                let ty =
                  inst dom (Tube t)
                    (Bwv.map_plus t.plus_faces
                       (fun (SFace_of fc) -> Hashtbl.find argtbl (SFace_of (comp_sface fa fc)))
                       (sfaces t.total_faces)) in
                Hashtbl.add argtbl (SFace_of fa)
                  (Uninst (Neu (Var { level; deg = id_deg D.zero }, ty))))
              df doms in
          (* TODO: This code is copy-and-pasted from apply_neu.  Factor it out. *)
          let out_args =
            Bwv.map2_plus t.plus_faces
              (fun (SFace_of fa) afn ->
                let k = dom_sface fa in
                let (Faces k_faces) = count_faces k in
                let afntbl = Hashtbl.create 10 in
                let () =
                  Bwv.iter
                    (fun (SFace_of fc) ->
                      Hashtbl.add afntbl (SFace_of fc)
                        (Hashtbl.find argtbl (SFace_of (comp_sface fa fc))))
                    (sfaces k_faces) in
                apply afn (dom_sface fa) afntbl)
              df args in
          let output = inst (apply_binder cod argtbl) tube out_args in
          equal_at !curlvl (apply x m argtbl) (apply y m argtbl) output)
  | _ -> equal_val n x y

and equal_val : int -> value -> value -> unit option =
 fun n x y ->
  match (x, y) with
  | Uninst u, Uninst v -> equal_uninst n u v
  | ( Inst { tm = tm1; dim = _; tube = t1; args = a1 },
      Inst { tm = tm2; dim = _; tube = t2; args = a2 } ) -> (
      let* () = equal_uninst n tm1 tm2 in
      match (compare (tube_inst t1) (tube_inst t2), compare (tube_uninst t1) (tube_uninst t2)) with
      | Eq, Eq ->
          let Tube t1, Tube t2 = (t1, t2) in
          let Eq = D.plus_uniq t1.plus_dim t2.plus_dim in
          let Eq = faces_uniq t1.total_faces t2.total_faces in
          let Eq = faces_uniq t1.missing_faces t2.missing_faces in
          let Eq = N.minus_uniq t1.plus_faces t2.plus_faces in
          bwv_iterM2 (equal_val n) a1 a2
      | _ -> fail)
  | Lam _, _ | _, Lam _ -> raise (Failure "Unexpected lambda in synthesizing equality-check")
  | _, _ -> None

and equal_uninst : int -> uninst -> uninst -> unit option =
 fun n x y ->
  match (x, y) with
  | UU m, UU n -> (
      match compare m n with
      | Eq -> return ()
      | _ -> fail)
  (* TODO: Are we supposed to compare the types of neutrals? *)
  | Neu (u, _), Neu (v, _) -> equal_neu n u v
  | _ -> fail

and equal_neu : int -> neu -> neu -> unit option =
 fun n x y ->
  match (x, y) with
  | Var { level = l1; deg = d1 }, Var { level = l2; deg = d2 } ->
      let* () = guard (l1 = l2) in
      deg_equiv d1 d2
  | ( App { fn = f1; app_faces = af1; args = a1; ins = i1 },
      App { fn = f2; app_faces = af2; args = a2; ins = i2 } ) -> (
      let* () = equal_neu n f1 f2 in
      let* () = deg_equiv (perm_of_ins i1) (perm_of_ins i2) in
      match compare (dim_faces af1) (dim_faces af2) with
      | Eq ->
          let Eq = faces_uniq af1 af2 in
          bwv_iterM2 (equal_nf n) a1 a2
      | _ -> fail)
  | _ -> fail
