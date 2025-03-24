open Util
open Dim
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
          Mbwd.map
            (fun (Term.StructfieldAbwd.Entry (fld, x)) ->
              Term.StructfieldAbwd.Entry (fld, structfield f x))
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
  | Codata { eta; opacity; dim; termctx = tc; fields } ->
      Codata
        {
          eta;
          opacity;
          dim;
          termctx = Option.map (termctx f) tc;
          fields =
            Mbwd.map
              (fun (CodatafieldAbwd.Entry (fld, x)) -> CodatafieldAbwd.Entry (fld, codatafield f x))
              fields;
        }

and structfield : type n a s i et.
    (Compunit.t -> Compunit.t) ->
    (i, n * a * s * et) Term.Structfield.t ->
    (i, n * a * s * et) Term.Structfield.t =
 fun f fld ->
  match fld with
  | Lower (x, l) -> Lower (term f x, l)
  | Higher m ->
      Higher
        (PlusPbijmap.mmap
           {
             map =
               (fun _ [ x ] ->
                 match x with
                 | PlusFam (Some (rb, x)) -> PlusFam (Some (rb, term f x))
                 | PlusFam None -> PlusFam None);
           }
           [ m ])

and codatafield : type a n i et.
    (Compunit.t -> Compunit.t) -> (i, a * n * et) Codatafield.t -> (i, a * n * et) Codatafield.t =
 fun f fld ->
  match fld with
  | Lower tm -> Lower (term f tm)
  | Higher (ka, tm) -> Higher (ka, term f tm)

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

and entry : type b f mn. (Compunit.t -> Compunit.t) -> (b, f, mn) entry -> (b, f, mn) entry =
 fun f e ->
  match e with
  | Vis v ->
      let bindings =
        CubeOf.mmap
          {
            map =
              (fun _ [ (b : (b, mn) Tbwd.snoc binding) ] : (b, mn) Tbwd.snoc binding ->
                { ty = term f b.ty; tm = Option.map (term f) b.tm });
          }
          [ v.bindings ] in
      Vis { v with bindings }
  | Invis bindings ->
      let bindings =
        CubeOf.mmap
          {
            map =
              (fun _ [ (b : (b, mn) Tbwd.snoc binding) ] : (b, mn) Tbwd.snoc binding ->
                { ty = term f b.ty; tm = Option.map (term f) b.tm });
          }
          [ bindings ] in
      Invis bindings

and termctx_ordered : type a b.
    (Compunit.t -> Compunit.t) -> (a, b) ordered_termctx -> (a, b) ordered_termctx =
 fun f ctx ->
  match ctx with
  | Emp -> Emp
  | Ext (ctx, e, ax) -> Ext (termctx_ordered f ctx, entry f e, ax)
  | Lock ctx -> Lock (termctx_ordered f ctx)

and termctx : type a b. (Compunit.t -> Compunit.t) -> (a, b) termctx -> (a, b) termctx =
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
