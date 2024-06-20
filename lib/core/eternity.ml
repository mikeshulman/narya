(* This module should not be opened, but used qualified. *)

open Util
open Syntax
open Term
open Reporter

(* In contrast to the "Global" state which stores constants and their definitions, the "Eternal" state stores metavariables and their definitions.  Like its Asimovian namesake, Eternity exists outside the ordinary timestream.  Eternal metavariables aren't scoped and aren't affected by import and sectioning commands, but even more importantly, each such metavariable stores its own copy of the Global state when it was created.  This way we can "go back in time" to when that metavariable was created and be sure that any solution of that metavariable would have been valid in its original location.  However, since it must also store its parsing state, we do all that storing in the parsing functions.

   This has nothing to do with undo, which undoes changes to the eternal state as well as the global one.  Rather, it's about ordinary commands that reach back in time, e.g. to fill previously created holes. *)

(* We also track whether there are still any unsolved metavariables, and the number of holes created by the current command. *)
module StateData = struct
  type t = { map : unit Metadef.Map.t; solved : [ `Solved | `Unsolved ]; current : int }
end

module S = Algaeff.State.Make (StateData)

let find meta =
  match Global.find_meta_opt meta with
  | Some x -> Metadef.def_of_info x
  | None ->
      Metadef.def_of_info
        (Metadef.Map.find_opt (MetaKey meta) (S.get ()).map <|> Undefined_metavariable (PMeta meta))

let add :
    type a b s.
    (b, s) Meta.t ->
    (string option, a) Bwv.t ->
    (a, b) Termctx.t ->
    (b, kinetic) term ->
    s energy ->
    unit =
 fun meta vars termctx ty energy ->
  S.modify (fun { map; solved = _; current } ->
      {
        map =
          Metadef.Map.add (MetaKey meta)
            (Metainfo { vars = Some vars; termctx; ty; tm = `None; energy })
            map;
        solved = `Unsolved;
        current = current + 1;
      })

let unsolved () = (S.get ()).solved = `Unsolved

let _update meta f =
  S.modify (fun data -> { data with map = Metadef.Map.update (MetaKey meta) f data.map })

let run_empty f = S.run ~init:{ map = Metadef.Map.empty; solved = `Solved; current = 0 } f

(* At the end of a command, we get the number of holes that were created by that command, and reset the counter to 0 for the next command. *)
let end_command () =
  let data = S.get () in
  let current = data.current in
  S.set { data with current = 0 };
  current
