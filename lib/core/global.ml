(* This module should not be opened, but used qualified. *)

open Util
open Tbwd
open Reporter
open Syntax
open Term

(* The global environment of constants. *)

(* Each global constant either is an axiom or has a definition (a case tree).  The latter includes canonical types.  An axiom can be either parametric, which means it is always accessible, or nonparametric, which means it is not accessible behind context locks for external parametricity.  (In the future, this should be customizable on a per-direction basis.) *)
type definition = Axiom of [ `Parametric | `Nonparametric ] | Defined of (emp, potential) term

module ConstantMap = Map.Make (Constant)

type data = {
  constants : ((emp, kinetic) term * definition, Code.t) Result.t ConstantMap.t;
  locked : bool;
}

let empty : data = { constants = ConstantMap.empty; locked = false }

module S = Algaeff.State.Make (struct
  type t = data
end)

let find_opt c =
  let d = S.get () in
  match (ConstantMap.find_opt c d.constants, d.locked) with
  | Some (Ok (_, Axiom `Nonparametric)), true -> fatal (Locked_axiom (PConstant c))
  | Some (Ok (ty, tm)), _ -> Some (ty, tm)
  | Some (Error e), _ -> fatal e
  | None, _ -> None

let locked () = (S.get ()).locked

let add_to c ty df (d : data) =
  { d with constants = d.constants |> ConstantMap.add c (Ok (ty, df)) }

let add c ty df = S.modify @@ add_to c ty df

let add_error c e =
  S.modify @@ fun d -> { d with constants = d.constants |> ConstantMap.add c (Error e) }

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
          d.constants |> ConstantMap.update c (Option.map (Result.map (fun (ty, _) -> (ty, df))));
      }
    f

let run_locked f =
  let d = S.get () in
  S.run ~init:{ d with locked = true } f
