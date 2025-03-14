(* This module should not be opened, but used qualified. *)

open Util
open Core
open Status
open Term
open Reporter

(* Like its Asimovian namesake, Eternity exists outside the ordinary timestream.  Eternal metavariables aren't scoped and aren't affected by import and sectioning commands, but even more importantly, each such metavariable stores its own copy of the Global state, as well as the Scope and variable scope when it was created.  This way we can "go back in time" to when that metavariable was created and be sure that any solution of that metavariable would have been valid in its original location.  Changes to eternal metavariables are also not subject to undo. *)

type ('a, 'b, 's) homewhen = {
  global : Global.data;
  scope : Scope.trie;
  options : Options.t;
  status : ('b, 's) status;
  vars : (string option, 'a) Bwv.t;
}

module MetaData = struct
  type ('x, 'a, 'b, 's) t = { def : ('a, 'b, 's) Metadef.t; homewhen : ('a, 'b, 's) homewhen }
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
          return x.def);
      add =
        (fun m vars termctx ty status li ri ->
          S.modify (fun { map } ->
              {
                map =
                  Metamap.add m
                    {
                      def =
                        Metadef.make ~tm:`Undefined ~termctx ~ty ~energy:(Status.energy status) ~li
                          ~ri;
                      homewhen =
                        {
                          global = Global.get ();
                          scope = Scope.get_visible ();
                          status;
                          vars;
                          options = Scope.get_options ();
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
          match def with
          | { tm = `Undefined; _ } -> count + 1
          | _ -> count);
    }
    (S.get ()).map 0

let notify_holes () =
  let n = unsolved () in
  if n > 0 then Reporter.emit (Open_holes n)

(* Throw away holes that don't exist at the current time, according to Global. *)
let filter_now () =
  S.modify (fun { map } ->
      { map = Metamap.filter { filter = (fun m _ -> Global.hole_exists m) } map })

let find : type a b s. (a, b, s) Meta.t -> (a, b, s) Metadef.t * (a, b, s) homewhen =
 fun m ->
  let ({ def; homewhen } : (unit, a, b, s) MetaData.t) =
    Metamap.find_opt m (S.get ()).map <|> Anomaly "missing hole" in
  (def, homewhen)

type find_number =
  | Find_number :
      ('a, 'b, 's) Meta.t * ('a, 'b, 's) Metadef.t * ('a, 'b, 's) homewhen
      -> find_number

(* We assume here that we want the hole with that number in the current compilation unit. *)
let find_number : int -> find_number =
 fun i ->
  let (Entry (m, { def; homewhen })) =
    Metamap.find_hole_opt (Compunit.Current.read ()) i (S.get ()).map <|> Anomaly "missing hole"
  in
  Find_number (m, def, homewhen)

let all_holes () =
  Metamap.fold
    {
      fold =
        (fun m { def; homewhen } holes ->
          match def with
          | { tm = `Undefined; _ } -> Find_number (m, def, homewhen) :: holes
          | _ -> holes);
    }
    (S.get ()).map []

let solve : type a b s. (a, b, s) Meta.t -> (b, s) term -> unit =
 fun h tm ->
  S.modify (fun data ->
      {
        map =
          Metamap.update h
            (Option.map (fun (d : (unit, a, b, s) MetaData.t) ->
                 { d with def = Metadef.define tm d.def }))
            data.map;
      })
