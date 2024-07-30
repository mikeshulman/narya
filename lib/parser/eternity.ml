(* This module should not be opened, but used qualified. *)

open Util
open Core
open Status
open Syntax
open Term
open Reporter

(* In contrast to the "Global" state which stores constants and their definitions, the "Eternal" state stores metavariables and their definitions.  Like its Asimovian namesake, Eternity exists outside the ordinary timestream.  Eternal metavariables aren't scoped and aren't affected by import and sectioning commands, but even more importantly, each such metavariable stores its own copy of the Global state, as well as the Scope and variable scope when it was created.  This way we can "go back in time" to when that metavariable was created and be sure that any solution of that metavariable would have been valid in its original location.

   This has nothing to do with undo, which undoes changes to the eternal state as well as the global one.  Rather, it's about ordinary commands that reach back in time, e.g. to fill previously created holes. *)

type ('b, 's) homewhen = {
  global : Global.data;
  scope : Scope.trie;
  discrete : bool Constant.Map.t;
  status : ('b, 's) status;
}

(* We store the definition of a hole as a reference cell, so that if it is solved in a later eternal moment, the solution affects all earlier moments that might be undone to. *)
module MetaData = struct
  type ('x, 'b, 's) t = { def : ('b, 's) Metadef.t ref; homewhen : ('b, 's) homewhen }
end

module Metamap = Meta.Map.Make (MetaData)
module IntMap = Map.Make (Int)

type data = { map : unit Metamap.t }

module StateData = struct
  type t = data
end

let empty : data = { map = Metamap.empty }

module S = State.Make (StateData)

let run = S.run
let try_with = S.try_with

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
          let* x = Metamap.find_opt m (S.get ()).map in
          return !(x.def));
      add =
        (fun m vars termctx ty status ->
          S.modify (fun { map } ->
              {
                map =
                  Metamap.add m
                    {
                      def =
                        ref
                          (Metadef.Metadef
                             { tm = `Undefined vars; termctx; ty; energy = Status.energy status });
                      homewhen =
                        {
                          global = Global.get ();
                          scope = Scope.get_visible ();
                          discrete = Syntax.Discrete.get ();
                          status;
                        };
                    }
                    map;
              }));
    }

let unsolved () =
  Metamap.fold
    {
      fold =
        (fun _ { def; _ } count ->
          match !def with
          | Metadef { tm = `Undefined _; _ } -> count + 1
          | _ -> count);
    }
    (S.get ()).map 0

let find : type b s. (b, s) Meta.t -> (b, s) Metadef.t * (b, s) homewhen =
 fun m ->
  let ({ def; homewhen } : (unit, b, s) MetaData.t) =
    Metamap.find_opt m (S.get ()).map <|> Anomaly "missing hole" in
  (!def, homewhen)

type find_number =
  | Find_number : ('b, 's) Meta.t * ('b, 's) Metadef.t * ('b, 's) homewhen -> find_number

(* We assume here that we want the hole with that number in the current compilation unit. *)
let find_number : int -> find_number =
 fun i ->
  let (Entry (m, { def; homewhen })) =
    Metamap.find_hole_opt (Compunit.Current.read ()) i (S.get ()).map <|> Anomaly "missing hole"
  in
  Find_number (m, !def, homewhen)

let all_holes () =
  Metamap.fold
    {
      fold =
        (fun m { def; homewhen } holes ->
          match !def with
          | Metadef { tm = `Undefined _; _ } -> Find_number (m, !def, homewhen) :: holes
          | _ -> holes);
    }
    (S.get ()).map []

let solve : type b s. (b, s) Meta.t -> (b, s) term -> unit =
 fun h tm ->
  S.modify (fun data ->
      {
        map =
          Metamap.update h
            (Option.map (fun (d : (unit, b, s) MetaData.t) ->
                 d.def := Metadef.define tm !(d.def);
                 d))
            data.map;
      })
