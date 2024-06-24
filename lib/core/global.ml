(* This module should not be opened, but used qualified. *)

open Util
open Tbwd
open Reporter
open Syntax
open Term

(* The global environment of constants and definition-local metavariables. *)

(* Each global constant either is an axiom or has a definition (a case tree).  The latter includes canonical types.  An axiom can be either parametric, which means it is always accessible, or nonparametric, which means it is not accessible behind context locks for external parametricity.  (In the future, this should be customizable on a per-direction basis.) *)
type definition = Axiom of [ `Parametric | `Nonparametric ] | Defined of (emp, potential) term

module Metamap = Meta.Map.Make (struct
  type ('x, 'bs) t = ('x, 'bs) Metadef.t
end)

type data = {
  constants : ((emp, kinetic) term * definition, Code.t) Result.t Constant.Map.t;
  metas : unit Metamap.t;
  locked : bool;
}

let empty : data = { constants = Constant.Map.empty; metas = Metamap.empty; locked = false }

module S = Algaeff.State.Make (struct
  type t = data
end)

let () =
  S.register_printer (function
    | `Get -> Some "unhandled Global get effect"
    | `Set _ -> Some "unhandled Global set effect")

let find c =
  let d = S.get () in
  match (Constant.Map.find_opt c d.constants, d.locked) with
  | Some (Ok (_, Axiom `Nonparametric)), true -> fatal (Locked_axiom (PConstant c))
  | Some (Ok (ty, tm)), _ -> (ty, tm)
  | Some (Error e), _ -> fatal e
  | None, _ -> fatal (Undefined_constant (PConstant c))

type eternity = {
  find_opt : 'b 's. ('b, 's) Meta.t -> (unit, 'b * 's) Metadef.t option;
  add :
    'a 'b 's.
    ('b, 's) Meta.t ->
    (string option, 'a) Bwv.t option ->
    ('a, 'b) Termctx.t ->
    ('b, kinetic) term ->
    's energy ->
    unit;
  end_command : unit -> int;
}

let eternity : eternity ref =
  ref
    {
      find_opt = (fun _ -> raise (Failure "eternity not set"));
      add = (fun _ _ _ _ _ -> raise (Failure "eternity not set"));
      end_command = (fun _ -> raise (Failure "eternity not set"));
    }

let find_meta m =
  match !eternity.find_opt m with
  | Some d -> d
  | None -> (
      match Metamap.find_opt (MetaKey m) (S.get ()).metas with
      | Some d -> d
      | None -> fatal (Anomaly "undefined metavariable"))

let to_channel_unit chan i flags =
  let d = S.get () in
  Constant.Map.to_channel_unit chan i d.constants flags;
  Metamap.to_channel_unit chan i d.metas flags

let from_channel_unit f chan i =
  let d = S.get () in
  let constants =
    Constant.Map.from_channel_unit chan
      (Result.map (fun (tm, df) -> (Link.term f tm, df)))
      i d.constants in
  let metas = Metamap.from_channel_unit chan { map = (fun df -> Link.metadef f df) } i d.metas in
  S.set { d with constants; metas }

let locked () = (S.get ()).locked

let add_to c ty df (d : data) =
  { d with constants = d.constants |> Constant.Map.add c (Ok (ty, df)) }

let add c ty df = S.modify @@ add_to c ty df

let add_error c e =
  S.modify @@ fun d -> { d with constants = d.constants |> Constant.Map.add c (Error e) }

let add_meta m ~termctx ~ty ~tm ~energy =
  S.modify @@ fun d ->
  {
    d with
    metas = d.metas |> Metamap.add (MetaKey m) (Metadef { vars = None; termctx; ty; tm; energy });
  }

let add_eternal_meta m ~vars ~termctx ~ty ~energy = !eternity.add m (Some vars) termctx ty energy
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
          |> Metamap.update (MetaKey m)
               (Option.map (fun (Metadef.Metadef df) -> Metadef.Metadef { df with tm }));
      }
    f

let run_locked f =
  let d = S.get () in
  S.run ~init:{ d with locked = true } f

let get = S.get
let run = S.run
let end_command () = !eternity.end_command ()
