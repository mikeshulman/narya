open Util
open Dim
open Syntax
open Term

(* When "linking" a pre-compiled file with the current run, we need to walk the unmarshaled terms and replace the old autonumbers of compilation units, from when the file was compiled, with the current ones. *)

let rec term : type a s. (Compunit.t -> Compunit.t) -> (a, s) term -> (a, s) term =
 fun f tm ->
  match tm with
  | Var i -> Var i
  | Const c -> Const (Constant.remake f c)
  | Meta (m, s) -> Meta (Meta.remake f m, s)
  | MetaEnv (m, e) -> MetaEnv (Meta.remake f m, env f e)
  | Field (tm, fld) -> Field (term f tm, fld)
  | UU n -> UU n
  | Inst (tm, args) -> Inst (term f tm, TubeOf.mmap { map = (fun _ [ x ] -> term f x) } [ args ])
  | Pi (x, doms, cods) ->
      Pi
        ( x,
          CubeOf.mmap { map = (fun _ [ x ] -> term f x) } [ doms ],
          CodCube.mmap { map = (fun _ [ x ] -> term f x) } [ cods ] )
  | App (fn, args) -> App (term f fn, CubeOf.mmap { map = (fun _ [ x ] -> term f x) } [ args ])
  | Constr (c, n, args) ->
      Constr
        (c, n, List.map (fun arg -> CubeOf.mmap { map = (fun _ [ x ] -> term f x) } [ arg ]) args)
  | Act (tm, s) -> Act (term f tm, s)
  | Let (x, v, body) -> Let (x, term f v, term f body)
  | Lam (x, body) -> Lam (x, term f body)
  | Struct (eta, dim, flds, energy) ->
      Struct (eta, dim, Abwd.map (fun (x, l) -> (term f x, l)) flds, energy)
  | Match { tm; dim; branches } ->
      Match { tm = term f tm; dim; branches = Constr.Map.map (branch f) branches }
  | Realize tm -> Realize (term f tm)
  | Canonical can -> Canonical (canonical f can)

and branch : type a n. (Compunit.t -> Compunit.t) -> (a, n) branch -> (a, n) branch =
 fun f br ->
  match br with
  | Branch (ab, p, tm) -> Branch (ab, p, term f tm)
  | Refute -> Refute

and canonical : type a. (Compunit.t -> Compunit.t) -> a canonical -> a canonical =
 fun f can ->
  match can with
  | Data { indices; constrs; discrete } ->
      Data { indices; constrs = Abwd.map (dataconstr f) constrs; discrete }
  | Codata { eta; opacity; dim; fields } ->
      Codata { eta; opacity; dim; fields = Abwd.map (term f) fields }

and dataconstr : type p i. (Compunit.t -> Compunit.t) -> (p, i) dataconstr -> (p, i) dataconstr =
 fun f (Dataconstr { args; indices }) ->
  Dataconstr { args; indices = Vec.mmap (fun [ x ] -> term f x) [ indices ] }

and env : type a n b. (Compunit.t -> Compunit.t) -> (a, n, b) env -> (a, n, b) env =
 fun f e ->
  match e with
  | Emp n -> Emp n
  | Ext (e, xss) ->
      Ext
        ( env f e,
          CubeOf.mmap
            { map = (fun _ [ xs ] -> CubeOf.mmap { map = (fun _ [ x ] -> term f x) } [ xs ]) }
            [ xss ] )
