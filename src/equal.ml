open Dim
open Value
open Norm
open Monoid
open Monad.ZeroOps (Monad.Maybe)

let msg _ = ()

(* Eta-expanding equality checks.  In all functions, the integer is the current De Bruijn level, i.e. the length of the current context (we don't need any other information about the context). *)

(* To do an eta-expanding equality check, we must create one new variable for each argument in the boundary.  With De Bruijn levels, these variables are just sequential numbers after n.  But to make these variables into values, we need to annotate them with their types, which in general are instantiations of the domains at previous variables.  Thus, we assemble them in a hashtable as we create them for random access to the previous ones. *)
let dom_vars : type m. int -> (m, value) ConstCube.t -> int * (m, value) ConstCube.t =
 fun n doms ->
  let curlvl = ref n in
  let argtbl = Hashtbl.create 10 in
  let () =
    ConstCube.miter
      {
        it =
          (fun fa [ dom ] ->
            let level = !curlvl in
            let () = curlvl := !curlvl + 1 in
            let ty =
              inst dom
                (ConstTube.build D.zero
                   (D.zero_plus (dom_sface fa))
                   {
                     build =
                       (fun fc ->
                         Hashtbl.find argtbl (SFace_of (comp_sface fa (sface_of_tface fc))));
                   }) in
            Hashtbl.add argtbl (SFace_of fa) (Uninst (Neu (Var { level; deg = id_deg D.zero }, ty))));
      }
      [ doms ] in
  ( !curlvl,
    ConstCube.build (ConstCube.dim doms) { build = (fun fa -> Hashtbl.find argtbl (SFace_of fa)) }
  )

(* Compare two normal forms that are *assumed* to have the same type. *)
let rec equal_nf : int -> normal -> normal -> unit option =
 fun n x y ->
  (* Thus, we can do an eta-expanding check at either one of their stored types, since they are assumed equal.  *)
  equal_at n x.tm y.tm x.ty

(* Eta-expanding compare two values at a type, which they are both assumed to belong to. *)
and equal_at : int -> value -> value -> value -> unit option =
 fun n x y ty ->
  match ty with
  | Uninst tm -> equal_at_uninst n x y tm (ConstTube.empty D.zero)
  | Inst { tm; dim = _; args } -> equal_at_uninst n x y tm args
  | Lam _ -> raise (Failure "Lambda-abstraction is not a type for equality-checking")

(* Subroutine for equal_at with the instantiation of the type peeled off. *)
and equal_at_uninst :
    type m n mn f. int -> value -> value -> uninst -> (m, n, mn, value) ConstTube.t -> unit option =
 fun n x y ty args ->
  match ty with
  (* The only interesting thing here happens when the type is one with an eta-rule, such as a pi-type. *)
  | Pi (doms, cods) -> (
      (* The pi-type must be fully instantiated at the correct dimension. *)
      let m = ConstCube.dim doms in
      match (compare (ConstTube.uninst args) D.zero, compare (ConstTube.inst args) m) with
      | Neq, _ -> raise (Failure "Non-fully-instantiated type in equality-checking")
      | _, Neq -> raise (Failure "Instantiation mismatch in equality-checking")
      | Eq, Eq ->
          let Eq = D.plus_uniq (ConstTube.plus args) (D.zero_plus m) in
          (* Create variables for all the boundary domains. *)
          let newlvl, newargs = dom_vars n doms in
          (* TODO: This code is copy-and-pasted from apply_neu.  Factor it out. *)
          let out_args =
            ConstTube.mmap
              {
                map =
                  (fun fa [ afn ] ->
                    let k = dom_tface fa in
                    apply afn
                      (ConstCube.build k
                         {
                           build =
                             (fun fc -> ConstCube.find newargs (comp_sface (sface_of_tface fa) fc));
                         }));
              }
              [ args ] in
          let idf = id_sface m in
          let output = inst (apply_binder (BindCube.find cods idf) idf newargs) out_args in
          (* If both terms have the given pi-type, then when applied to variables of the domains, they will both have the computed output-type, so we can recurse back to eta-expanding equality at that type. *)
          equal_at newlvl (apply x newargs) (apply y newargs) output)
  (* If the type is not one that has an eta-rule, then we pass off to a synthesizing equality-check, forgetting about our assumption that the two terms had the same type.  This is the equality-checking analogue of the conversion rule for checking a synthesizing term, but since equality requires no evidence we don't have to actually synthesize a type at which they are equal or verify that it equals the type we assumed them to have. *)
  | _ -> equal_val n x y

(* "Synthesizing" equality check of two values, now *not* assumed a priori to have the same type.  If this function concludes that they are equal, then the equality of their types is part of that conclusion. *)
and equal_val : int -> value -> value -> unit option =
 fun n x y ->
  match (x, y) with
  (* Since an Inst has a positive amount of instantiation, it can never equal an Uninst. *)
  | Uninst u, Uninst v -> equal_uninst n u v
  | Inst { tm = tm1; dim = _; args = a1 }, Inst { tm = tm2; dim = _; args = a2 } -> (
      let* () = equal_uninst n tm1 tm2 in
      (* If tm1 and tm2 are equal and have the same type, that type must be an instantiation of a universe of the same dimension, itself instantiated at the same arguments.  So for the instantiations to be equal (including their types), it suffices for the instantiation dimensions and arguments to be equal. *)
      match
        ( compare (ConstTube.inst a1) (ConstTube.inst a2),
          compare (ConstTube.uninst a1) (ConstTube.uninst a2) )
      with
      | Eq, Eq ->
          let Eq = D.plus_uniq (ConstTube.plus a1) (ConstTube.plus a2) in
          let open ConstTube.Monadic (Monad.Maybe) in
          miterM { it = (fun _ [ x; y ] -> equal_val n x y) } [ a1; a2 ]
      | _ ->
          msg "Unequal dimensions of instantiation";
          fail)
  | Lam _, _ | _, Lam _ -> raise (Failure "Unexpected lambda in synthesizing equality-check")
  | _, _ ->
      msg "Unequal terms in synthesizing equality-check";
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
          msg "Unequal dimensions of universese";
          fail)
  (* We don't need to check that the types of neutral terms are equal, since equal_neu concludes equality of types rather than assumes it. *)
  | Neu (u, _), Neu (v, _) -> equal_neu lvl u v
  | Pi (dom1s, cod1s), Pi (dom2s, cod2s) -> (
      (* If two pi-types have the same dimension, equal domains, and equal codomains, they are equal and have the same type (an instantiation of the universe of that dimension at pi-types formed from the lower-dimensional domains and codomains). *)
      let k = ConstCube.dim dom1s in
      match compare (ConstCube.dim dom2s) k with
      | Eq ->
          let open ConstCube.Monadic (Monad.Maybe) in
          let* () = miterM { it = (fun _ [ x; y ] -> equal_val lvl x y) } [ dom1s; dom2s ] in
          (* We create variables for all the domains, in order to typecheck all the codomains.  The codomain boundary types only use some of those variables, but it doesn't hurt to have the others around. *)
          let newlvl, newargs = dom_vars lvl dom1s in
          let open BindCube.Monadic (Monad.Maybe) in
          miterM
            {
              it =
                (fun s [ cod1; cod2 ] ->
                  equal_val newlvl (apply_binder cod1 s newargs) (apply_binder cod2 s newargs));
            }
            [ cod1s; cod2s ]
      | Neq ->
          msg "Unequal dimensions of pi-type";
          fail)
  | _ ->
      msg "Unequal uninstantiated terms";
      fail

(* Synthesizing equality check for neutrals.  Again equality of types is part of the conclusion, not a hypothesis. *)
and equal_neu : int -> neu -> neu -> unit option =
 fun n x y ->
  match (x, y) with
  | Var { level = l1; deg = d1 }, Var { level = l2; deg = d2 } ->
      (* Two equal variables with the same degeneracy applied are equal, including their types because that variable has only one type. *)
      let* () = guard (l1 = l2) in
      deg_equiv d1 d2
  | App { fn = f1; args = a1; ins = i1 }, App { fn = f2; args = a2; ins = i2 } -> (
      (* To check two neutral applications are equal, with their types, we first check if the functions are equal, including their types and hence also their domains and codomains (and also they have the same insertion applied outside), and that they are applied at the same dimension. *)
      let* () = equal_neu n f1 f2 in
      let* () = deg_equiv (perm_of_ins i1) (perm_of_ins i2) in
      match compare (ConstCube.dim a1) (ConstCube.dim a2) with
      | Eq ->
          (* If so, this ensures right away that the arguments have the same type, so we can hand back to the eta-expanding equality-check for them. *)
          let open ConstCube.Monadic (Monad.Maybe) in
          miterM { it = (fun _ [ x; y ] -> (equal_nf n) x y) } [ a1; a2 ]
      | _ ->
          msg "Unequal dimensions of application";
          fail)
  | _ ->
      msg "Unequal neutral terms";
      fail
