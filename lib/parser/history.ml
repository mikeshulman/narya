open Bwd
open Util
open Core
open Reporter
module Trie = Yuujinchou.Trie

(* History manages the global state, eternal state, namespace scopes, and notation situations with a single state effect, and recording past versions of this state for "undo" purposes. *)

type moment = { global : Global.data; scope : Scope.t; situation : Situation.t }

(* The length of 'past' is the number of undoable commands.  It starts out as empty, with 'present' being the state at the beginning of interactive commands. *)
module Recorded = struct
  type t = { past : moment Bwd.t; present : moment }
end

module S = State.Make (Recorded)

let run_empty : type a. (unit -> a) -> a =
 fun f ->
  S.run
    ~init:
      {
        past = Emp;
        present = { global = Global.empty; scope = Scope.empty; situation = !Builtins.builtins };
      }
  @@ fun () ->
  Global.try_with
    ~get:(fun () -> (S.get ()).present.global)
    ~set:(fun global -> S.modify (fun d -> { d with present = { d.present with global } }))
  @@ fun () ->
  Scope.run_with
    ~get:(fun () -> (S.get ()).present.scope)
    ~set:(fun scope -> S.modify (fun d -> { d with present = { d.present with scope } }))
  @@ fun () ->
  Situation.try_with
    ~get:(fun () -> (S.get ()).present.situation)
    ~set:(fun situation -> S.modify (fun d -> { d with present = { d.present with situation } }))
    f

(* Every undoable command (e.g. def, axiom, notation, import, export) should be wrapped in this. *)
let do_command f =
  (* First we save the state at the end of the previous command to the past, freeing up the present to be modified by the current command. *)
  S.modify (fun d -> { d with past = Snoc (d.past, d.present) });
  try f ()
  with e ->
    (* If the current command fails, we restore the state at the end of the previous command. *)
    S.modify (fun d ->
        match d.past with
        | Snoc (past, present) -> { past; present }
        | Emp -> fatal (Anomaly "nothing to unsave"));
    raise e

(* This is run *by* the 'undo' command.  Since 'undo' is not undoable, it is *not* wrapped in 'do_command'. *)
let undo n =
  (try
     S.modify (fun d ->
         match Bwd_extra.remove d.past (n - 1) with
         | Snoc (past, present) -> { past; present }
         | Emp -> fatal Not_enough_to_undo)
   with Failure _ -> fatal Not_enough_to_undo);
  Eternity.filter_now ()

(* Set the visible namespace, e.g. before going into interactive mode. *)
let set_visible visible =
  Scope.set_visible visible;
  let situation = Situation.add_users !Builtins.builtins visible in
  S.modify (fun d -> { d with present = { d.present with situation } })

(* Put a given starting visible namespace into the scope, and also extract the notations from it.  Since this uses Scope.run and Situation.run_on, it *overrides* (dynamically, locally) the "actual" namespace and notations in the outer state.  It is used for loading files and strings, which are atomic undo units, and for "going back in time" temporarily to solve an old hole. *)
let run_with_scope ~init_visible f =
  Scope.run ~init_visible @@ fun () ->
  Situation.run_on (Situation.add_users !Builtins.builtins init_visible) @@ f
