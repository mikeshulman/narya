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
  | Field (tm, fld, fldins) -> Field (term f tm, fld, fldins)
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
      Struct
        ( eta,
          dim,
          Abwd.map
            (fun (PbijmapOf.Wrap m) ->
              PbijmapOf.Wrap
                (PbijmapOf.mmap
                   {
                     map =
                       (fun _ [ x ] ->
                         match x with
                         | Some (x, l) -> Some (term f x, l)
                         | None -> None);
                   }
                   [ m ]))
            flds,
          energy )
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
      Codata { eta; opacity; dim; fields = Abwd.map (codatafield f) fields }

and codatafield : type a n. (Compunit.t -> Compunit.t) -> (a, n) codatafield -> (a, n) codatafield =
 fun f fld ->
  match fld with
  | Lower_codatafield tm -> Lower_codatafield (term f tm)
  | Higher_codatafield (k, ka, tm) -> Higher_codatafield (k, ka, term f tm)

and dataconstr : type p i. (Compunit.t -> Compunit.t) -> (p, i) dataconstr -> (p, i) dataconstr =
 fun f (Dataconstr { args; indices }) ->
  Dataconstr { args = tel f args; indices = Vec.mmap (fun [ x ] -> term f x) [ indices ] }

and tel : type a b ab. (Compunit.t -> Compunit.t) -> (a, b, ab) tel -> (a, b, ab) tel =
 fun f t ->
  match t with
  | Emp -> Emp
  | Ext (x, ty, t) -> Ext (x, term f ty, tel f t)

and env : type a n b. (Compunit.t -> Compunit.t) -> (a, n, b) env -> (a, n, b) env =
 fun f e ->
  match e with
  | Emp n -> Emp n
  | Ext (e, nk, xs) -> Ext (env f e, nk, CubeOf.mmap { map = (fun _ [ x ] -> term f x) } [ xs ])

let entry :
    type b f mn. (Compunit.t -> Compunit.t) -> (b, f, mn) Termctx.entry -> (b, f, mn) Termctx.entry
    =
 fun f e ->
  match e with
  | Vis v ->
      let bindings =
        CubeOf.mmap
          {
            map =
              (fun _ [ (b : (b, mn) Tbwd.snoc Termctx.binding) ] : (b, mn) Tbwd.snoc Termctx.binding ->
                { ty = term f b.ty; tm = Option.map (term f) b.tm });
          }
          [ v.bindings ] in
      Vis { v with bindings }
  | Invis bindings ->
      let bindings =
        CubeOf.mmap
          {
            map =
              (fun _ [ (b : (b, mn) Tbwd.snoc Termctx.binding) ] : (b, mn) Tbwd.snoc Termctx.binding ->
                { ty = term f b.ty; tm = Option.map (term f) b.tm });
          }
          [ bindings ] in
      Invis bindings

let rec termctx_ordered :
    type a b. (Compunit.t -> Compunit.t) -> (a, b) Termctx.Ordered.t -> (a, b) Termctx.Ordered.t =
 fun f ctx ->
  match ctx with
  | Emp -> Emp
  | Snoc (ctx, e, ax) -> Snoc (termctx_ordered f ctx, entry f e, ax)
  | Lock ctx -> Lock (termctx_ordered f ctx)

let termctx : type a b. (Compunit.t -> Compunit.t) -> (a, b) Termctx.t -> (a, b) Termctx.t =
 fun f (Permute (p, ctx)) -> Permute (p, termctx_ordered f ctx)

let metadef : type x y z. (Compunit.t -> Compunit.t) -> (x, y, z) Metadef.t -> (x, y, z) Metadef.t =
 fun f data ->
  let termctx = termctx f data.termctx in
  let ty = term f data.ty in
  let tm =
    match data.tm with
    | `Defined tm -> `Defined (term f tm)
    | x -> x in
  { data with tm; termctx; ty }
