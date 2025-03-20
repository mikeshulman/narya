open Util
open Tbwd
open Dim
open Term
open Value
open Norm

(* To typecheck a lambda, do an eta-expanding equality check, check pi-types for equality, or read back a pi-type or a term at a pi-type, we must create one new variable for each argument in the boundary.  Sometimes we need these variables as values and other times as normals.  The function dom_vars creates these variables and returns them in two cubes.  It, and the function ext_tel below that follows from it, are in a separate file because it depends on Inst and Ctx and is used in Equal, Readback, and Check, and doesn't seem to be placed naturally in any of those files. *)

let dom_vars : type m.
    int -> (m, kinetic value) CubeOf.t -> (m, kinetic value) CubeOf.t * (m, Ctx.Binding.t) CubeOf.t
    =
 fun i doms ->
  (* To make these variables into values, we need to annotate them with their types, which in general are instantiations of the domains at previous variables.  Thus, we assemble them in a hashtable as we create them for random access to the previous ones. *)
  let argtbl = Hashtbl.create 10 in
  let j = ref 0 in
  let [ args; nfs ] =
    CubeOf.pmap
      {
        map =
          (fun fa [ dom ] ->
            let ty =
              inst dom
                (TubeOf.build D.zero
                   (D.zero_plus (dom_sface fa))
                   {
                     build =
                       (fun fc ->
                         Hashtbl.find argtbl (SFace_of (comp_sface fa (sface_of_tface fc))));
                   }) in
            let level = (i, !j) in
            j := !j + 1;
            let v = { tm = var level ty; ty } in
            Hashtbl.add argtbl (SFace_of fa) v;
            [ v.tm; Ctx.Binding.make (Some level) v ]);
      }
      [ doms ] (Cons (Cons Nil)) in
  (args, nfs)

(* Extend a context by a finite number of cubes of new visible variables at some dimension, with boundaries, whose types are specified by the evaluation of some telescope in some (possibly higher-dimensional) environment (and hence may depend on the earlier ones).  Also return the new variables in a list of Cubes, and the new environment extended by the *top-dimensional variables only*. *)

let rec ext_tel : type a b c ac bc e ec n.
    (a, e) Ctx.t ->
    (n, b) env ->
    (* Note that c is a Fwn, since it is the length of a telescope. *)
    (a, c, ac) Raw.Namevec.t ->
    (b, c, bc) Telescope.t ->
    (e, c, n, ec) Tbwd.snocs ->
    (ac, ec) Ctx.t
    * (n, bc) env
    * (n, kinetic value) CubeOf.t list
    * (n, Ctx.Binding.t) CubeOf.t list =
 fun ctx env xs tel ec ->
  match (xs, tel, ec) with
  | [], Emp, Zero -> (ctx, env, [], [])
  | x :: xs, Ext (x', rty, rest), Suc ec ->
      let m = dim_env env in
      let newvars, newnfs =
        dom_vars (Ctx.length ctx)
          (CubeOf.build m { build = (fun fa -> Norm.eval_term (act_env env (op_of_sface fa)) rty) })
      in
      let x =
        match x with
        | Some x -> Some x
        | None -> x' in
      let ctx, env, vars, nfs =
        ext_tel (Ctx.cube_vis ctx x newnfs) (Ext (env, D.plus_zero m, Ok newvars)) xs rest ec in
      (ctx, env, newvars :: vars, newnfs :: nfs)
