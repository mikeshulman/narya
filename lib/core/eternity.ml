(* This module should not be opened, but used qualified. *)

open Util
open Syntax
open Term

(* In contrast to the "Global" state which stores constants and their definitions, the "Eternal" state stores metavariables and their definitions.  Like its Asimovian namesake, Eternity exists outside the ordinary timestream.  Eternal metavariables aren't scoped and aren't affected by import and sectioning commands, but even more importantly, each such metavariable stores its own copy of the Global state when it was created.  This way we can "go back in time" to when that metavariable was created and be sure that any solution of that metavariable would have been valid in its original location. *)

type ('b, 's) meta_value = [ `None | `Nonrec of ('b, 's) term ]

type (_, _) metadef =
  | Metadef : {
      vars : (string option, 'a) Bwv.t option;
      (* TODO: Global state. *)
      termctx : ('a, 'b) Termctx.t;
      ty : ('b, kinetic) term;
      tm : ('b, 's) meta_value;
      energy : 's energy;
    }
      -> (unit, 'b * 's) metadef

(* As with Global, we track Galactic state using a State effect.  In this case, the state is an intrinsically well-typed map, since metavariables are parametrized by their context length and energy. *)

module Map = Meta.Map.Make (struct
  type ('x, 'bs) t = ('x, 'bs) metadef
end)

(* We also track whether there are still any unsolved metavariables, and the number of holes created by the current command. *)

module StateData = struct
  type t = { map : unit Map.t; solved : [ `Solved | `Unsolved ]; current : int }
end

module S = Algaeff.State.Make (StateData)

(* Don't use this directly!  Call Global.find_meta_opt, which passes off to this if it doesn't find a definitional-local metavariable. *)
let find_opt meta = Map.find_opt (MetaKey meta) (S.get ()).map

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
          Map.add (MetaKey meta) (Metadef { vars = Some vars; termctx; ty; tm = `None; energy }) map;
        solved = `Unsolved;
        current = current + 1;
      })

let unsolved () = (S.get ()).solved = `Unsolved
let _update meta f = S.modify (fun data -> { data with map = Map.update (MetaKey meta) f data.map })
let run_empty f = S.run ~init:{ map = Map.empty; solved = `Solved; current = 0 } f

(* At the end of a command, we get the number of holes that were created by that command, and reset the counter to 0 for the next command. *)
let end_command () =
  let data = S.get () in
  let current = data.current in
  S.set { data with current = 0 };
  current
