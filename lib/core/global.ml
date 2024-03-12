(* This module should not be opened, but used qualified. *)

open Util
open Tbwd
open Syntax
open Term

(* The global environment of constants. *)

(* Each global constant either is an axiom or has a definition (a case tree).  The latter includes canonical types. *)
type definition = Axiom | Defined of (emp, potential) term

module ConstantMap = Map.Make (Constant)

type data = { types : (emp, kinetic) term ConstantMap.t; definitions : definition ConstantMap.t }

let empty = { types = ConstantMap.empty; definitions = ConstantMap.empty }

module State = Algaeff.State.Make (struct
  type t = data
end)

let find_type_opt c = ConstantMap.find_opt c (State.get ()).types
let find_definition_opt c = ConstantMap.find_opt c (State.get ()).definitions

let add_to c ty df d =
  { types = d.types |> ConstantMap.add c ty; definitions = d.definitions |> ConstantMap.add c df }

let remove_from c d =
  { types = d.types |> ConstantMap.remove c; definitions = d.definitions |> ConstantMap.remove c }

let add c ty df = State.modify @@ add_to c ty df
let remove c = State.modify @@ remove_from c
let run_empty f = State.run ~init:empty f

let run_with c ty df f =
  let d = State.get () in
  State.run ~init:(add_to c ty df d) f
