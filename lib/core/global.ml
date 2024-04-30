(* This module should not be opened, but used qualified. *)

open Util
open Tbwd
open Reporter
open Syntax
open Term

(* The global environment of constants. *)

(* Each global constant either is an axiom or has a definition (a case tree).  The latter includes canonical types. *)
type definition = Axiom | Defined of (emp, potential) term

module ConstantMap = Map.Make (Constant)

type data = { constants : ((emp, kinetic) term * definition) ConstantMap.t; locked : bool }

let empty : data = { constants = ConstantMap.empty; locked = false }

module S = Algaeff.State.Make (struct
  type t = data
end)

let find_opt c =
  let d = S.get () in
  match (ConstantMap.find_opt c d.constants, d.locked) with
  | Some (_, Axiom), true -> fatal (Locked_axiom (PConstant c))
  | Some (ty, tm), _ -> Some (ty, tm)
  | None, _ -> None

let locked () = (S.get ()).locked
let add_to c ty df (d : data) = { d with constants = d.constants |> ConstantMap.add c (ty, df) }
let add c ty df = S.modify @@ add_to c ty df
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
        constants = d.constants |> ConstantMap.update c (Option.map (fun (ty, _) -> (ty, df)));
      }
    f

let run_locked f =
  let d = S.get () in
  S.run ~init:{ d with locked = true } f
