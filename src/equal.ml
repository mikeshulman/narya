open Dim
open Value
open Norm
open Monoid
open Monad.ZeroOps (Monad.Maybe)
open Mlist.Monadic (Monad.Maybe)
open Bwd

(* Strictly speaking, equality-checking functions only need to be given the *number* of the current De Bruijn level, not the whole context of level variables with their types.  However, having them take contexts instead allows equality-checking and type-checking to use the same "dom_vars" function to create new level variables. *)

let msg _ = ()

(* Eta-expanding equality checks.  In all functions, the integer is the current De Bruijn level, i.e. the length of the current context (we don't need any other information about the context). *)

(* Compare two normal forms that are *assumed* to have the same type. *)
let rec equal_nf : type a. a Ctx.t -> normal -> normal -> unit option =
 fun n x y ->
  (* Thus, we can do an eta-expanding check at either one of their stored types, since they are assumed equal.  *)
  equal_at n x.tm y.tm x.ty

(* Eta-expanding compare two values at a type, which they are both assumed to belong to. *)
and equal_at : type a. a Ctx.t -> value -> value -> value -> unit option =
 fun n x y ty ->
  (* The type must be fully instantiated. *)
  let (Fullinst (ty, tyargs)) = full_inst ty "equal_at" in
  match ty with
  (* The only interesting thing here happens when the type is one with an eta-rule, such as a pi-type. *)
  | Pi (doms, cods) -> (
      let k = CubeOf.dim doms in
      (* The pi-type must be instantiated at the correct dimension. *)
      match compare (TubeOf.inst tyargs) k with
      | Neq -> raise (Failure "Instantiation mismatch in equality-checking")
      | Eq ->
          (* Create variables for all the boundary domains. *)
          let (Faces df) = count_faces k in
          let (Plus af) = N.plus (faces_out df) in
          let newlvl, newargs = Ctx.dom_vars n df af doms in
          (* Calculate the output type of the application to those variables *)
          let output = tyof_app cods tyargs newargs in
          (* If both terms have the given pi-type, then when applied to variables of the domains, they will both have the computed output-type, so we can recurse back to eta-expanding equality at that type. *)
          equal_at newlvl (apply x newargs) (apply y newargs) output)
  | Neu (Const { name; dim }, args) -> (
      (* This is kind of copied from tyof_field. *)
      match compare (TubeOf.inst tyargs) dim with
      | Neq -> raise (Failure "Dimension mismatch in eta-equality for record")
      | Eq -> (
          match Hashtbl.find_opt Global.records name with
          | Some (Record (Eta, k, fields)) ->
              let env = take_args (Emp dim) (N.improper_subset k) args (N.zero_plus k) in
              (* It suffices to use the fields of x when computing the types of the fields, since we proceed to check the fields for equality *in order* and thus by the time we are checking equality of any particulary field of x and y, the previous fields of x and y are already known to be equal, and the type of the current field can only depend on these.  (This is a semantic constraint on the kinds of generalized records that can sensibly admit eta-conversion.) *)
              let env = Ext (env, TubeOf.plus_cube (val_of_norm_tube tyargs) (CubeOf.singleton x)) in
              miterM
                (fun [ (fld, fldty) ] ->
                  equal_at n (field x fld) (field y fld)
                    (inst (eval env fldty)
                       (TubeOf.mmap
                          {
                            map =
                              (fun _ [ arg ] ->
                                let tm = field arg.tm fld in
                                let ty = tyof_field arg.tm arg.ty fld in
                                { tm; ty });
                          }
                          [ tyargs ])))
                [ fields ]
          | _ -> equal_val n x y))
  (* If the type is not one that has an eta-rule, then we pass off to a synthesizing equality-check, forgetting about our assumption that the two terms had the same type.  This is the equality-checking analogue of the conversion rule for checking a synthesizing term, but since equality requires no evidence we don't have to actually synthesize a type at which they are equal or verify that it equals the type we assumed them to have. *)
  | _ -> equal_val n x y

(* "Synthesizing" equality check of two values, now *not* assumed a priori to have the same type.  If this function concludes that they are equal, then the equality of their types is part of that conclusion. *)
and equal_val : type a. a Ctx.t -> value -> value -> unit option =
 fun n x y ->
  match (x, y) with
  (* Since an Inst has a positive amount of instantiation, it can never equal an Uninst.  We don't need to check that the types agree, since equal_uninst concludes equality of types rather than assumes it. *)
  | Uninst (u, _), Uninst (v, _) -> equal_uninst n u v
  | Inst { tm = tm1; dim = _; args = a1; tys = _ }, Inst { tm = tm2; dim = _; args = a2; tys = _ }
    -> (
      let* () = equal_uninst n tm1 tm2 in
      (* If tm1 and tm2 are equal and have the same type, that type must be an instantiation of a universe of the same dimension, itself instantiated at the same arguments.  So for the instantiations to be equal (including their types), it suffices for the instantiation dimensions and arguments to be equal. *)
      match
        (compare (TubeOf.inst a1) (TubeOf.inst a2), compare (TubeOf.uninst a1) (TubeOf.uninst a2))
      with
      | Eq, Eq ->
          let Eq = D.plus_uniq (TubeOf.plus a1) (TubeOf.plus a2) in
          let open TubeOf.Monadic (Monad.Maybe) in
          (* Because instantiation arguments are stored as normals, we use type-sensitive equality to compare them. *)
          miterM { it = (fun _ [ x; y ] -> equal_nf n x y) } [ a1; a2 ]
      | _ ->
          msg "Unequal dimensions of instantiation";
          fail)
  | Lam _, _ | _, Lam _ -> raise (Failure "Unexpected lambda in synthesizing equality-check")
  | Struct _, _ | _, Struct _ -> raise (Failure "Unexpected struct in synthesizing equality-check")
  | _, _ ->
      msg "Unequal terms in synthesizing equality-check";
      fail

(* Subroutine of equal_val.  Like it, equality of the types is part of the conclusion, not a hypothesis.  *)
and equal_uninst : type a. a Ctx.t -> uninst -> uninst -> unit option =
 fun lvl x y ->
  match (x, y) with
  | UU m, UU n -> (
      (* Two universes are equal precisely when they have the same dimension, in which case they also automatically have the same type (a standard instantiation of a (higher) universe of that same dimension). *)
      match compare m n with
      | Eq -> return ()
      | _ ->
          msg "Unequal dimensions of universese";
          fail)
  | Neu (fn1, args1), Neu (fn2, args2) ->
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
          let (Faces df) = count_faces k in
          let (Plus af) = N.plus (faces_out df) in
          let newlvl, newargs = Ctx.dom_vars lvl df af dom1s in
          let open BindCube.Monadic (Monad.Maybe) in
          miterM
            {
              it =
                (fun s [ cod1; cod2 ] ->
                  let sargs = CubeOf.subcube s newargs in
                  equal_val newlvl (apply_binder cod1 sargs) (apply_binder cod2 sargs));
            }
            [ cod1s; cod2s ]
      | Neq ->
          msg "Unequal dimensions of pi-type";
          fail)
  | _ ->
      msg "Unequal uninstantiated terms";
      fail

(* Synthesizing equality check for heads.  Again equality of types is part of the conclusion, not a hypothesis. *)
and equal_head : type a. a Ctx.t -> head -> head -> unit option =
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
and equal_args : type a. a Ctx.t -> app Bwd.t -> app Bwd.t -> unit option =
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
and equal_arg : type a. a Ctx.t -> app -> app -> unit option =
 fun n (App (a1, i1)) (App (a2, i2)) ->
  let* () = deg_equiv (perm_of_ins i1) (perm_of_ins i2) in
  match (a1, a2) with
  | Arg a1, Arg a2 -> (
      match compare (CubeOf.dim a1) (CubeOf.dim a2) with
      | Eq ->
          let open CubeOf.Monadic (Monad.Maybe) in
          miterM { it = (fun _ [ x; y ] -> (equal_nf n) x y) } [ a1; a2 ]
      (* If the dimensions don't match, it is a bug rather than a user error, since they are supposed to both be valid arguments of the same function, and any function has a unique dimension. *)
      | Neq -> raise (Failure "Unequal dimensions of application in equality-check"))
  | Field f1, Field f2 -> if f1 = f2 then return () else fail
  | _, _ -> fail
