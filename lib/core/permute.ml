open Util
open Tbwd
open Dim
open Syntax
open Value
open Act

(* Permute environments eagerly rather than lazily.  This is currently (May 2024) used only to read back environments into "term environments", which is only done when reading back terms involving metavariables.  *)

(* Decompose an env into either Emp or Ext, by pushing Acts through. *)
type (_, _) env_decomp =
  | Emp : 'n D.t -> ('n, emp) env_decomp
  | Ext :
      ('n, 'b) env * ('k, ('n, kinetic value) CubeOf.t) CubeOf.t
      -> ('n, ('b, 'k) snoc) env_decomp

let rec env_top : type n a. (n, a) env -> (n, a) env_decomp = function
  | Emp n -> Emp n
  | Ext (env, xs) -> Ext (env, xs)
  | Act (env, (Op (fb, fa) as fba)) -> (
      match env_top env with
      | Emp _ -> Emp (dom_deg fa)
      | Ext (env, xs) ->
          Ext
            ( Act (env, fba),
              CubeOf.mmap
                { map = (fun _ [ ys ] -> act_value_cube (CubeOf.subcube fb ys) fa) }
                [ xs ] ))
  | Permute (p, env) -> env_top (permute_env p env)

(* Note that the return entry is n-dimensional, since all the operator actions have to be applied as we pull it out. *)
and select_env :
    type a b n k.
    (a, k, b) Tbwd.insert -> (n, b) env -> (n, a) env * (k, (n, kinetic value) CubeOf.t) CubeOf.t =
 fun ins env ->
  match ins with
  | Now ->
      let (Ext (env, top)) = env_top env in
      (env, top)
  | Later ins ->
      let (Ext (env, top)) = env_top env in
      let env, sel = select_env ins env in
      (Ext (env, top), sel)

(* Permute an environment.  The delayed actions in the input environment are preserved in the leftmost part of the permutation that's the identity, but all the others are applied to the terms in the process of permuting. *)
and permute_env : type a b n. (a, b) Tbwd.permute -> (n, b) env -> (n, a) env =
 fun perm env ->
  match perm with
  | Id -> env
  | Insert (perm, ins) ->
      let env, sel = select_env ins env in
      Ext (permute_env perm env, sel)
