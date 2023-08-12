open Dim
open Value
open Norm
open Monoid
open Monad.ZeroOps (Monad.Maybe)

(* Eta-expanding equality checks.  In all functions, the integer is the current De Bruijn level, i.e. the length of the current context (we don't need any other information about the context). *)

(* To do an eta-expanding equality check, we must create one new variable for each argument in the boundary.  With De Bruijn levels, these variables are just sequential numbers after n.  But to make these variables into values, we need to annotate them with their types, which in general are instantiations of the domains at previous variables.  Thus, we assemble them in a hashtable as we create them for random access to the previous ones. *)
let dom_vars :
    type m f.
    int -> (m sface_of, f) Bwv.t -> (value, f) Bwv.t -> int * (m sface_of, value) Hashtbl.t =
 fun n df doms ->
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
        Hashtbl.add argtbl (SFace_of fa) (Uninst (Neu (Var { level; deg = id_deg D.zero }, ty))))
      df doms in
  (!curlvl, argtbl)

(* Compare two normal forms that are *assumed* to have the same type. *)
let rec equal_nf : int -> normal -> normal -> unit option =
 fun n x y ->
  (* Thus, we can do an eta-expanding check at either one of their stored types, since they are assumed equal.  *)
  equal_at n x.tm y.tm x.ty

(* Eta-expanding compare two values at a type, which they are both assumed to belong to. *)
and equal_at : int -> value -> value -> value -> unit option =
 fun n x y ty ->
  match ty with
  | Uninst tm -> equal_at_uninst n x y tm tube_zero Emp
  | Inst { tm; dim = _; tube; args } -> equal_at_uninst n x y tm tube args
  | Lam _ -> raise (Failure "Lambda-abstraction is not a type for equality-checking")

(* Subroutine for equal_at with the instantiation of the type peeled off. *)
and equal_at_uninst :
    type m n f.
    int -> value -> value -> uninst -> (m, n, f) count_tube -> (value, f) Bwv.t -> unit option =
 fun n x y ty tube args ->
  match ty with
  (* The only interesting thing here happens when the type is one with an eta-rule, such as a pi-type. *)
  | Pi (dom_faces, doms, cods) -> (
      (* The pi-type must be fully instantiated at the correct dimension. *)
      let m = dim_faces dom_faces in
      match (compare (tube_uninst tube) D.zero, compare (tube_inst tube) m) with
      | Neq, _ -> raise (Failure "Non-fully-instantiated type in equality-checking")
      | _, Neq -> raise (Failure "Instantiation mismatch in equality-checking")
      | Eq, Eq ->
          let (Tube t) = tube in
          let Eq = D.plus_uniq t.plus_dim (D.zero_plus m) in
          let Eq = faces_uniq t.total_faces dom_faces in
          let Eq = faces_uniq t.missing_faces faces_zero in
          let Eq = N.plus_uniq t.plus_faces (Suc Zero) in
          let df = sfaces dom_faces in
          (* Create variables for all the boundary domains. *)
          let newlvl, argtbl = dom_vars n df doms in
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
          let idf = id_sface m in
          let output =
            inst (apply_binder (fbind (BindTree.nth cods idf)) idf argtbl) tube out_args in
          (* If both terms have the given pi-type, then when applied to variables of the domains, they will both have the computed output-type, so we can recurse back to eta-expanding equality at that type. *)
          equal_at newlvl (apply x m argtbl) (apply y m argtbl) output)
  (* If the type is not one that has an eta-rule, then we pass off to a synthesizing equality-check, forgetting about our assumption that the two terms had the same type.  This is the equality-checking analogue of the conversion rule for checking a synthesizing term, but since equality requires no evidence we don't have to actually synthesize a type at which they are equal or verify that it equals the type we assumed them to have. *)
  | _ -> equal_val n x y

(* "Synthesizing" equality check of two values, now *not* assumed a priori to have the same type.  If this function concludes that they are equal, then the equality of their types is part of that conclusion. *)
and equal_val : int -> value -> value -> unit option =
 fun n x y ->
  match (x, y) with
  (* Since an Inst has a positive amount of instantiation, it can never equal an Uninst. *)
  | Uninst u, Uninst v -> equal_uninst n u v
  | ( Inst { tm = tm1; dim = _; tube = t1; args = a1 },
      Inst { tm = tm2; dim = _; tube = t2; args = a2 } ) -> (
      let* () = equal_uninst n tm1 tm2 in
      (* If tm1 and tm2 are equal and have the same type, that type must be an instantiation of a universe of the same dimension, itself instantiated at the same arguments.  So for the instantiations to be equal (including their types), it suffices for the instantiation dimensions and arguments to be equal. *)
      match (compare (tube_inst t1) (tube_inst t2), compare (tube_uninst t1) (tube_uninst t2)) with
      | Eq, Eq ->
          let Tube t1, Tube t2 = (t1, t2) in
          let Eq = D.plus_uniq t1.plus_dim t2.plus_dim in
          let Eq = faces_uniq t1.total_faces t2.total_faces in
          let Eq = faces_uniq t1.missing_faces t2.missing_faces in
          let Eq = N.minus_uniq t1.plus_faces t2.plus_faces in
          bwv_iterM2 (equal_val n) a1 a2
      | _ ->
          Printf.printf "Unequal dimensions of instantiation";
          fail)
  | Lam _, _ | _, Lam _ -> raise (Failure "Unexpected lambda in synthesizing equality-check")
  | _, _ ->
      Printf.printf "Unequal terms in synthesizing equality-check";
      fail

(* Subroutine of equal_val.  Like it, equality of the types is part of the conclusion, not a hypothesis.  *)
and equal_uninst : int -> uninst -> uninst -> unit option =
 fun lvl x y ->
  match (x, y) with
  | UU m, UU n -> (
      (* Two universes are equal precisely when they have the same dimension, in which case they also automatically have the same type (a standard instantiation of a (higher) universe of that same dimension). *)
      match compare m n with
      | Eq -> return ()
      | _ ->
          Printf.printf "Unequal dimensions of universese";
          fail)
  (* We don't need to check that the types of neutral terms are equal, since equal_neu concludes equality of types rather than assumes it. *)
  | Neu (u, _), Neu (v, _) -> equal_neu lvl u v
  | Pi (dom1f, dom1s, cod1s), Pi (dom2f, dom2s, cod2s) -> (
      (* If two pi-types have the same dimension, equal domains, and equal codomains, they are equal and have the same type (an instantiation of the universe of that dimension at pi-types formed from the lower-dimensional domains and codomains). *)
      let k = dim_faces dom1f in
      match compare (dim_faces dom2f) k with
      | Eq ->
          let Eq = faces_uniq dom1f dom2f in
          let* () = bwv_iterM2 (equal_val lvl) dom1s dom2s in
          (* We create variables for all the domains, in order to typecheck all the codomains.  The codomain boundary types only use some of those variables, but it doesn't hurt to have the others around. *)
          let newlvl, argtbl = dom_vars lvl (sfaces dom1f) dom1s in
          BindTree.iterOpt2 k
            {
              it =
                (fun s cod1 cod2 ->
                  equal_val newlvl
                    (apply_binder (fbind cod1) s argtbl)
                    (apply_binder (fbind cod2) s argtbl));
            }
            cod1s cod2s
      | Neq ->
          Printf.printf "Unequal dimensions of pi-type";
          fail)
  | _ ->
      Printf.printf "Unequal uninstantiated terms";
      fail

(* Synthesizing equality check for neutrals.  Again equality of types is part of the conclusion, not a hypothesis. *)
and equal_neu : int -> neu -> neu -> unit option =
 fun n x y ->
  match (x, y) with
  | Var { level = l1; deg = d1 }, Var { level = l2; deg = d2 } ->
      (* Two equal variables with the same degeneracy applied are equal, including their types because that variable has only one type. *)
      let* () = guard (l1 = l2) in
      deg_equiv d1 d2
  | ( App { fn = f1; app_faces = af1; args = a1; ins = i1 },
      App { fn = f2; app_faces = af2; args = a2; ins = i2 } ) -> (
      (* To check two neutral applications are equal, with their types, we first check if the functions are equal, including their types and hence also their domains and codomains (and also they have the same insertion applied outside), and that they are applied at the same dimension. *)
      let* () = equal_neu n f1 f2 in
      let* () = deg_equiv (perm_of_ins i1) (perm_of_ins i2) in
      match compare (dim_faces af1) (dim_faces af2) with
      | Eq ->
          let Eq = faces_uniq af1 af2 in
          (* If so, this ensures right away that the arguments have the same type, so we can hand back to the eta-expanding equality-check for them. *)
          bwv_iterM2 (equal_nf n) a1 a2
      | _ ->
          Printf.printf "Unequal dimensions of application";
          fail)
  | _ ->
      Printf.printf "Unequal neutral terms";
      fail
