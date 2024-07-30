(* This module should not be opened, but used qualified. *)

open Util
open Core
open Syntax
open Term
open Reporter

(* In contrast to the "Global" state which stores constants and their definitions, the "Eternal" state stores metavariables and their definitions.  Like its Asimovian namesake, Eternity exists outside the ordinary timestream.  Eternal metavariables aren't scoped and aren't affected by import and sectioning commands, but even more importantly, each such metavariable stores its own copy of the Global state, as well as the Scope and variable scope when it was created.  This way we can "go back in time" to when that metavariable was created and be sure that any solution of that metavariable would have been valid in its original location.

   This has nothing to do with undo, which undoes changes to the eternal state as well as the global one.  Rather, it's about ordinary commands that reach back in time, e.g. to fill previously created holes. *)

type homewhen = { global : Global.data; scope : Scope.trie; discrete : bool Constant.Map.t }

module MetaData = struct
  type ('x, 'bs) t = { def : ('x, 'bs) Metadef.t; homewhen : homewhen }
end

module Metamap = Meta.Map.Make (MetaData)
module IntMap = Map.Make (Int)

(* In addition to the types and possibly-definitions of all holes, we keep a list of the unsolved holes. *)
type data = { map : Metadef.undef Metamap.t; holes : Meta.wrapped IntMap.t }

module StateData = struct
  type t = data
end

let empty : data = { map = Metamap.empty; holes = IntMap.empty }

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
          let* x = Metamap.find_opt (MetaKey m) (S.get ()).map in
          return (Metadef.Wrap x.def));
      add =
        (fun m vars termctx ty status ->
          S.modify (fun { map; holes } ->
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
              }));
    }

let unsolved () = IntMap.cardinal (S.get ()).holes

let find : type b s. (b, s) Meta.t -> (b, s) Metadef.wrapped * homewhen =
 fun m ->
  let ({ def; homewhen } : (Metadef.undef, b * s) MetaData.t) =
    Metamap.find_opt (MetaKey m) (S.get ()).map <|> Anomaly "missing hole" in
  (Wrap def, homewhen)

type find_number =
  | Find_number : ('b, 's) Meta.t * ('b, 's) Metadef.wrapped * homewhen -> find_number

let find_number : int -> find_number =
 fun i ->
  let (Wrap (type b s) (m : (b, s) Meta.t)) =
    IntMap.find_opt i (S.get ()).holes <|> No_such_hole i in
  let ({ def; homewhen } : (Metadef.undef, b * s) MetaData.t) =
    Metamap.find_opt (MetaKey m) (S.get ()).map <|> Anomaly "missing hole" in
  Find_number (m, Wrap def, homewhen)

let all_holes () =
  List.map
    (fun (_, Meta.Wrap (type b s) (m : (b, s) Meta.t)) ->
      let ({ def; homewhen } : (Metadef.undef, b * s) MetaData.t) =
        Metamap.find_opt (MetaKey m) (S.get ()).map <|> Anomaly "missing hole" in
      Find_number (m, Wrap def, homewhen))
    (IntMap.bindings (S.get ()).holes)

let solve : type b s. (b, s) Meta.t -> (b, s) term -> unit =
 fun h tm ->
  S.modify (fun data ->
      {
        map =
          Metamap.update (MetaKey h)
            (Option.map
               (fun
                 ({ def; homewhen } : (Metadef.undef, b * s) MetaData.t)
                 :
                 (Metadef.undef, b * s) MetaData.t
               -> { def = Metadef.define (Some tm) def; homewhen }))
            data.map;
        holes = IntMap.remove (Meta.hole_number h) data.holes;
      })
