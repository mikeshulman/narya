open Dim
open Value
open Norm
open Monoid
open Monad.ZeroOps (Monad.Maybe)
open Bwd

let msg _ = ()

(* Eta-expanding equality checks.  In all functions, the integer is the current De Bruijn level, i.e. the length of the current context (we don't need any other information about the context). *)

(* To do an eta-expanding equality check, we must create one new variable for each argument in the boundary.  With De Bruijn levels, these variables are just sequential numbers after n.  But to make these variables into values, we need to annotate them with their types, which in general are instantiations of the domains at previous variables.  Thus, we assemble them in a hashtable as we create them for random access to the previous ones. *)
let dom_vars : type m. int -> (m, value) CubeOf.t -> int * (m, value) CubeOf.t =
 fun n doms ->
  let curlvl = ref n in
  let argtbl = Hashtbl.create 10 in
  let () =
    CubeOf.miter
      {
        it =
          (fun fa [ dom ] ->
            let level = !curlvl in
            let () = curlvl := !curlvl + 1 in
            let ty =
              inst dom
                (TubeOf.build D.zero
                   (D.zero_plus (dom_sface fa))
                   {
                     build =
                       (fun fc ->
                         Hashtbl.find argtbl (SFace_of (comp_sface fa (sface_of_tface fc))));
                   }) in
            Hashtbl.add argtbl (SFace_of fa)
              (Uninst (Neu { fn = Var { level; deg = id_deg D.zero }; args = Emp; ty })));
      }
      [ doms ] in
  (!curlvl, CubeOf.build (CubeOf.dim doms) { build = (fun fa -> Hashtbl.find argtbl (SFace_of fa)) })

(* Compare two normal forms that are *assumed* to have the same type. *)
let rec equal_nf : int -> normal -> normal -> unit option =
 fun n x y ->
  (* Thus, we can do an eta-expanding check at either one of their stored types, since they are assumed equal.  *)
  equal_at n x.tm y.tm x.ty

(* Eta-expanding compare two values at a type, which they are both assumed to belong to. *)
and equal_at : int -> value -> value -> value -> unit option =
 fun n x y ty ->
  match ty with
  | Uninst tm -> equal_at_uninst n x y tm (TubeOf.empty D.zero)
  | Inst { tm; dim = _; args } -> equal_at_uninst n x y tm args
  | Lam _ -> raise (Failure "Lambda-abstraction is not a type for equality-checking")

(* Subroutine for equal_at with the instantiation of the type peeled off. *)
and equal_at_uninst :
    type m n mn f. int -> value -> value -> uninst -> (m, n, mn, value) TubeOf.t -> unit option =
 fun n x y ty args ->
  match ty with
  (* The only interesting thing here happens when the type is one with an eta-rule, such as a pi-type. *)
  | Pi (doms, cods) -> (
      (* The pi-type must be fully instantiated at the correct dimension. *)
      let m = CubeOf.dim doms in
      match (compare (TubeOf.uninst args) D.zero, compare (TubeOf.inst args) m) with
      | Neq, _ -> raise (Failure "Non-fully-instantiated type in equality-checking")
      | _, Neq -> raise (Failure "Instantiation mismatch in equality-checking")
      | Eq, Eq ->
          let Eq = D.plus_uniq (TubeOf.plus args) (D.zero_plus m) in
          (* Create variables for all the boundary domains. *)
          let newlvl, newargs = dom_vars n doms in
          (* TODO: This code is copy-and-pasted from apply_neu.  Factor it out. *)
          let out_args =
            TubeOf.mmap
              {
                map =
                  (fun fa [ afn ] ->
                    let k = dom_tface fa in
                    apply afn
                      (CubeOf.build k
                         {
                           build =
                             (fun fc -> CubeOf.find newargs (comp_sface (sface_of_tface fa) fc));
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
        (compare (TubeOf.inst a1) (TubeOf.inst a2), compare (TubeOf.uninst a1) (TubeOf.uninst a2))
      with
      | Eq, Eq ->
          let Eq = D.plus_uniq (TubeOf.plus a1) (TubeOf.plus a2) in
          let open TubeOf.Monadic (Monad.Maybe) in
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
  | Neu { fn = fn1; args = args1; ty = _ }, Neu { fn = fn2; args = args2; ty = _ } ->
      (* To check two neutral applications are equal, with their types, we first check if the functions are equal, including their types and hence also their domains and codomains (and also they have the same insertion applied outside). *)
      let* () = equal_head lvl fn1 fn2 in
      (* Then we recursively check that all their arguments are equal. *)
      equal_args lvl args1 args2
  | Pi (dom1s, cod1s), Pi (dom2s, cod2s) -> (
      (* If two pi-types have the same dimension, equal domains, and equal codomains, they are equal and have the same type (an instantiation of the universe of that dimension at pi-types formed from the lower-dimensional domains and codomains). *)
      let k = CubeOf.dim dom1s in
      match compare (CubeOf.dim dom2s) k with
      | Eq ->
          let open CubeOf.Monadic (Monad.Maybe) in
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

(* Synthesizing equality check for heads.  Again equality of types is part of the conclusion, not a hypothesis. *)
and equal_head : int -> head -> head -> unit option =
 fun _ x y ->
  match (x, y) with
  | Var { level = l1; deg = d1 }, Var { level = l2; deg = d2 } ->
      (* Two equal variables with the same degeneracy applied are equal, including their types because that variable has only one type. *)
      let* () = guard (l1 = l2) in
      deg_equiv d1 d2
  | Const { name = c1; dim = n1 }, Const { name = c2; dim = n2 } -> (
      let* () = guard (c1 = c2) in
      match compare n1 n2 with
      | Eq -> return ()
      | Neq ->
          msg "Unequal constants";
          fail)
  | _, _ ->
      msg "Unequal heads";
      fail

(* Check that the arguments of two entire application spines of equal functions are equal.  This is basically a left fold, but we make sure to iterate from left to right, and fail rather than raising an exception if the lists have different lengths.  *)
and equal_args : int -> app Bwd.t -> app Bwd.t -> unit option =
 fun lvl args1 args2 ->
  match (args1, args2) with
  | Emp, Emp -> return ()
  | Snoc (rest1, arg1), Snoc (rest2, arg2) ->
      (* Iterating from left to right is important because it ensures that at the point of checking equality for any pair of arguments, we know that they have the same type, since they are valid arguments of equal functions with all previous arguments equal.  *)
      let* () = equal_args lvl rest1 rest2 in
      equal_arg lvl arg1 arg2
  | Emp, Snoc _ | Snoc _, Emp ->
      msg "Unequal lengths of application spines";
      fail

(* Check that two application arguments are equal, including their outer insertions as well as their values.  As noted above, here we can go back to *assuming* that they have equal types, and thus passing off to the eta-expanding equality check. *)
and equal_arg : int -> app -> app -> unit option =
 fun n (App (a1, i1)) (App (a2, i2)) ->
  let* () = deg_equiv (perm_of_ins i1) (perm_of_ins i2) in
  match compare (CubeOf.dim a1) (CubeOf.dim a2) with
  | Eq ->
      let open CubeOf.Monadic (Monad.Maybe) in
      miterM { it = (fun _ [ x; y ] -> (equal_nf n) x y) } [ a1; a2 ]
  (* If the dimensions don't match, it is a bug rather than a user error, since they are supposed to both be valid arguments of the same function, and any function has a unique dimension. *)
  | Neq -> raise (Failure "Unequal dimensions of application in equality-check")
