(* This module should not be opened, but used qualified. *)

open Util
open Core

(* In contrast to the "Global" state which stores constants and their definitions, the "Eternal" state stores metavariables and their definitions.  Like its Asimovian namesake, Eternity exists outside the ordinary timestream.  Eternal metavariables aren't scoped and aren't affected by import and sectioning commands, but even more importantly, each such metavariable stores its own copy of the Global state, as well as the Scope and variable scope when it was created.  This way we can "go back in time" to when that metavariable was created and be sure that any solution of that metavariable would have been valid in its original location.

   This has nothing to do with undo, which undoes changes to the eternal state as well as the global one.  Rather, it's about ordinary commands that reach back in time, e.g. to fill previously created holes. *)

module Data = struct
  type ('x, 'bs) data = { global : Global.data }
  type ('x, 'bs) t = { def : ('x, 'bs) Metadef.t; homewhen : ('x, 'bs) data }
end

module Metamap = Meta.Map.Make (Data)

(* We also track whether there are still any unsolved eternal metavariables, and the number of holes created by the current command. *)

module StateData = struct
  type t = { map : unit Metamap.t; solved : [ `Solved | `Unsolved ]; current : int }
end

module S = Algaeff.State.Make (StateData)

let () =
  S.register_printer (function
    | `Get -> Some "unhandled eternity get effect"
    | `Set _ -> Some "unhandled eternity set effect")

let () =
  Global.eternity :=
    {
      find_opt =
        (fun m ->
          let open Monad.Ops (Monad.Maybe) in
          let* x = Metamap.find_opt (MetaKey m) (S.get ()).map in
          return x.def);
      add =
        (fun m vars termctx ty energy ->
          S.modify (fun { map; solved = _; current } ->
              {
                map =
                  Metamap.add (MetaKey m)
                    {
                      def = Metadef { vars; termctx; ty; tm = `None; energy };
                      homewhen = { global = Global.get () };
                    }
                    map;
                solved = `Unsolved;
                current = current + 1;
              }));
      (* At the end of a command, we get the number of holes that were created by that command, and reset the counter to 0 for the next command. *)
      end_command =
        (fun () ->
          let data = S.get () in
          let current = data.current in
          S.set { data with current = 0 };
          current);
    }

let unsolved () = (S.get ()).solved = `Unsolved
let run_empty f = S.run ~init:{ map = Metamap.empty; solved = `Solved; current = 0 } f
