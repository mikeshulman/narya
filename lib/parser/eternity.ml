(* This module should not be opened, but used qualified. *)

open Util
open Core
open Syntax
open Term
open Reporter

(* In contrast to the "Global" state which stores constants and their definitions, the "Eternal" state stores metavariables and their definitions.  Like its Asimovian namesake, Eternity exists outside the ordinary timestream.  Eternal metavariables aren't scoped and aren't affected by import and sectioning commands, but even more importantly, each such metavariable stores its own copy of the Global state, as well as the Scope and variable scope when it was created.  This way we can "go back in time" to when that metavariable was created and be sure that any solution of that metavariable would have been valid in its original location.

   This has nothing to do with undo, which undoes changes to the eternal state as well as the global one.  Rather, it's about ordinary commands that reach back in time, e.g. to fill previously created holes. *)

type data = { global : Global.data; scope : Scope.trie; discrete : bool Constant.Map.t }

module Data = struct
  type ('x, 'bs) t = { def : ('x, 'bs) Metadef.t; homewhen : data }
end

module Metamap = Meta.Map.Make (Data)
module IntMap = Map.Make (Int)
(* We also keep a list of the unsolved holes, and the number of holes created by the current command. *)

module StateData = struct
  type t = { map : Metadef.undef Metamap.t; holes : Meta.wrapped IntMap.t; current : int }
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
          return (Metadef.Wrap x.def));
      add =
        (fun m vars termctx ty status ->
          S.modify (fun { map; holes; current } ->
              {
                map =
                  Metamap.add (MetaKey m)
                    {
                      def = Metadef { data = Undef_meta { vars; status }; termctx; ty };
                      homewhen =
                        {
                          global = Global.get ();
                          scope = Scope.get_visible ();
                          discrete = Syntax.Discrete.get ();
                        };
                    }
                    map;
                holes = IntMap.add (Meta.hole_number m) (Meta.Wrap m) holes;
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

let unsolved () = not (IntMap.is_empty (S.get ()).holes)
let run_empty f = S.run ~init:{ map = Metamap.empty; holes = IntMap.empty; current = 0 } f

let hole_of_number : int -> Meta.wrapped =
 fun i -> IntMap.find_opt i (S.get ()).holes <|> No_such_hole i

let find : type b s. (b, s) Meta.t -> (b, s) Metadef.wrapped * data =
 fun m ->
  let ({ def; homewhen } : (Metadef.undef, b * s) Data.t) =
    Metamap.find_opt (MetaKey m) (S.get ()).map <|> Anomaly "missing hole" in
  (Wrap def, homewhen)

let solve : type b s. (b, s) Meta.t -> (b, s) term -> unit =
 fun h tm ->
  S.modify (fun data ->
      {
        data with
        map =
          Metamap.update (MetaKey h)
            (Option.map
               (fun
                 ({ def; homewhen } : (Metadef.undef, b * s) Data.t)
                 :
                 (Metadef.undef, b * s) Data.t
               -> { def = Metadef.define tm def; homewhen }))
            data.map;
        holes = IntMap.remove (Meta.hole_number h) data.holes;
      })
