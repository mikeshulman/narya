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

let empty = { constants = ConstantMap.empty; locked = false }

module State = Algaeff.State.Make (struct
  type t = data
end)

let find_type_opt c =
  let d = State.get () in
  match (ConstantMap.find_opt c d.constants, d.locked) with
  | Some (_, Axiom), true -> fatal (Locked_axiom (PConstant c))
  | Some (ty, _), _ -> Some ty
  | None, _ -> None

let find_definition_opt c = Option.map snd (ConstantMap.find_opt c (State.get ()).constants)
let locked () = (State.get ()).locked
let add_to c ty df d = { d with constants = d.constants |> ConstantMap.add c (ty, df) }
let add c ty df = State.modify @@ add_to c ty df
let run_empty f = State.run ~init:empty f

let run_with c ty df f =
  let d = State.get () in
  State.run ~init:(add_to c ty df d) f

let run_with_definition c df f =
  let d = State.get () in
  State.run
    ~init:
      {
        d with
        constants = d.constants |> ConstantMap.update c (Option.map (fun (ty, _) -> (ty, df)));
      }
    f

let run_locked f =
  let d = State.get () in
  State.run ~init:{ d with locked = true } f
