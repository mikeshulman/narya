(* This module should not be opened, but used qualified. *)

open Util
open Tbwd
open Reporter
open Syntax
open Term

(* The global environment of constants and definition-local metavariables. *)

(* Each global constant either is an axiom or has a definition (a case tree).  The latter includes canonical types.  An axiom can be either parametric, which means it is always accessible, or nonparametric, which means it is not accessible behind context locks for external parametricity.  (In the future, this should be customizable on a per-direction basis.) *)
type definition = Axiom of [ `Parametric | `Nonparametric ] | Defined of (emp, potential) term

type data = {
  constants : ((emp, kinetic) term * definition, Code.t) Result.t Constant.Map.t;
  metas : unit Metadef.Map.t;
  locked : bool;
}

let empty : data = { constants = Constant.Map.empty; metas = Metadef.Map.empty; locked = false }

module S = Algaeff.State.Make (struct
  type t = data
end)

let find c =
  let d = S.get () in
  match (Constant.Map.find_opt c d.constants, d.locked) with
  | Some (Ok (_, Axiom `Nonparametric)), true -> fatal (Locked_axiom (PConstant c))
  | Some (Ok (ty, tm)), _ -> (ty, tm)
  | Some (Error e), _ -> fatal e
  | None, _ -> fatal (Undefined_constant (PConstant c))

(* Don't use this directly!  Call Eternity.find, which checks this first and then the eternal metas. *)
let find_meta_opt m = Metadef.Map.find_opt (MetaKey m) (S.get ()).metas

let to_channel_unit chan i flags =
  let d = S.get () in
  Constant.Map.to_channel_unit chan i d.constants flags;
  Metadef.Map.to_channel_unit chan i d.metas flags

let from_channel_unit f chan i =
  let d = S.get () in
  let constants =
    Constant.Map.from_channel_unit chan
      (Result.map (fun (tm, df) -> (Link.term f tm, df)))
      i d.constants in
  let metas =
    Metadef.Map.from_channel_unit chan { map = (fun df -> Link.metainfo f df) } i d.metas in
  S.set { d with constants; metas }

let locked () = (S.get ()).locked

let add_to c ty df (d : data) =
  { d with constants = d.constants |> Constant.Map.add c (Ok (ty, df)) }

let add c ty df = S.modify @@ add_to c ty df

let add_error c e =
  S.modify @@ fun d -> { d with constants = d.constants |> Constant.Map.add c (Error e) }

let add_meta m ~vars ~termctx ~ty ~tm ~energy =
  S.modify @@ fun d ->
  {
    d with
    metas = d.metas |> Metadef.Map.add (MetaKey m) (Metainfo { vars; termctx; ty; tm; energy });
  }

let run_empty f = S.run ~init:empty f

let run_with c ty df f =
  let d = S.get () in
  S.run ~init:(add_to c ty df d) f

let run_with_definition c df f =
  let d = S.get () in
  S.run
    ~init:
      {
        d with
        constants =
          d.constants |> Constant.Map.update c (Option.map (Result.map (fun (ty, _) -> (ty, df))));
      }
    f

let run_with_meta_definition m tm f =
  let d = S.get () in
  S.run
    ~init:
      {
        d with
        metas =
          d.metas
          |> Metadef.Map.update (MetaKey m)
               (Option.map (fun (Metadef.Metainfo df) -> Metadef.Metainfo { df with tm }));
      }
    f

let run_locked f =
  let d = S.get () in
  S.run ~init:{ d with locked = true } f

let get = S.get
let run = S.run
