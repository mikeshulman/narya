open Bwd
open Core
open Reporter
module Trie = Yuujinchou.Trie

(* Compilation units (i.e. files).  This module is called "Units" because "Unit" is the module "struct type t = unit end".  (-: *)

type trie = (Scope.P.data, Scope.P.tag) Trie.t

(* For separate compilation, we expect the executable to know how to load compilation units and compute their resulting export namespaces.  We wrap this in an effect, so that it can also be invoked *during* the loading of some other unit, with a 'require' command.  We also include an effect that combines all the top-level namespaces (i.e. those not only loaded "transitively" through require) so far into a single one.  The boolean argument to load_unit indicates whether it is being invoked from top level, and the namespace is a starting visible one to override the default.  *)

type _ Effect.t +=
  | Load_unit :
      [ `File of string * bool | `String of string option * string * trie option ]
      -> trie Effect.t
  | All_units : trie Effect.t

(* These are the versions that are called by the executable, since it doesn't have any use for the resulting namespace, and it is always loading at top-level. *)
let load_file file =
  let _ = Effect.perform (Load_unit (`File (file, true))) in
  ()

let load_string title content init =
  let _ = Effect.perform (Load_unit (`String (title, content, init))) in
  ()

(* This version is called by the 'import' command, which is not at top-level, and cares about the namespace. *)
let get_file file = Effect.perform (Load_unit (`File (file, false)))

(* Get the top-level namespace *)
let all () = Effect.perform All_units

(* We store effectually the current directory and a list of all files whose loading is currently in progress, i.e. the path of imports that led us to the current file.  The former is used for making filenames absolute; the latter is used to check for circular imports. *)

module Loadstate = struct
  type t = {
    cwd : FilePath.filename;
    parents : FilePath.filename Bwd.t;
    imports : (Compunit.t * FilePath.filename) Bwd.t;
  }
end

module Loading = Algaeff.State.Make (Loadstate)

(* This is how the executable supplies a callback that loads files.  It will always be passed a reduced absolute filename.  We take care of calling that function as needed and caching the results in a hashtable for future calls.  We also compute the result of combining all the units, but lazily since we'll only need it if there are command-line strings, stdin, or interactive.  The first argument is a default initial visible namespace, which can be overridden. *)
let with_execute :
    type a. trie -> (trie -> Compunit.t -> Asai.Range.source -> trie) -> (unit -> a) -> a =
 fun init execute f ->
  let table : (FilePath.filename, trie * Compunit.t * bool) Hashtbl.t = Hashtbl.create 20 in
  let all : trie Lazy.t ref = ref (Lazy.from_val Trie.empty) in
  let add_to_all trie =
    let old = !all in
    all := lazy (Scope.M.union ~prefix:Emp (Lazy.force old) trie) in
  (* We use an inner recursive function so that we can re-wrap calls to "compute" in the same effect handler. *)
  let rec go : type a. (unit -> a) -> a =
   fun f ->
    let open Effect.Deep in
    try_with f ()
      {
        effc =
          (fun (type a) (eff : a Effect.t) ->
            match eff with
            | Load_unit source -> (
                Option.some @@ fun (k : (a, _) continuation) ->
                match source with
                | `File (file, top) -> (
                    (* We normalize the file path to a reduced absolute one, so we can use it for a hashtable key. *)
                    let file =
                      if FilePath.is_relative file then
                        FilePath.make_absolute (Loading.get ()).cwd file
                      else file in
                    let file = FilePath.reduce file in
                    match Hashtbl.find_opt table file with
                    | Some (trie, compunit, top') ->
                        (* If we already loaded that file, we just return its saved export namespace, but we may need to add it to the 'all' namespace if it wasn't already there. *)
                        if top && not top' then (
                          add_to_all trie;
                          Hashtbl.add table file (trie, compunit, true));
                        Loading.modify (fun s ->
                            { s with imports = Snoc (s.imports, (compunit, file)) });
                        continue k trie
                    | None ->
                        (* Otherwise, we have to load it.  First we check for circular dependencies. *)
                        (let parents = (Loading.get ()).parents in
                         if Bwd.exists (fun x -> x = file) parents then
                           fatal (Circular_import (Bwd.to_list (Snoc (parents, file)))));
                        (* Then we load it, in its directory and with itself added to the list of parents. *)
                        if not top then emit (Loading_file file);
                        let compunit = Compunit.make file in
                        let trie =
                          Loading.run
                            ~init:
                              {
                                cwd = FilePath.dirname file;
                                parents = Snoc ((Loading.get ()).parents, file);
                                imports = Emp;
                              }
                          @@ fun () ->
                          go @@ fun () -> execute init compunit (`File file) in
                        (* Then we add it to the table and (possibly) 'all'. *)
                        if not top then emit (File_loaded file);
                        Hashtbl.add table file (trie, compunit, top);
                        if top then add_to_all trie;
                        (* And we save it as a file that was imported by the current file. *)
                        Loading.modify (fun s ->
                            { s with imports = Snoc (s.imports, (compunit, file)) });
                        continue k trie)
                | `String (title, content, start) ->
                    (* In the case of a string input there is no caching and no change of state, since it can't be "required" from another file.  But a string is always at top-level, so we always add it to 'all'.  *)
                    let trie =
                      go @@ fun () ->
                      execute
                        (Option.value start ~default:init)
                        Compunit.basic
                        (`String { title; content }) in
                    add_to_all trie;
                    continue k trie)
            | All_units ->
                Option.some @@ fun (k : (a, _) continuation) -> continue k (Lazy.force !all)
            | _ -> None);
      } in
  Loading.run ~init:{ cwd = Sys.getcwd (); parents = Emp; imports = Emp } @@ fun () -> go f

let run ~(init_visible : trie) f =
  Scope.run ~init_visible @@ fun () ->
  State.run_on
    (Seq.fold_left
       (fun state (_, (data, _)) ->
         match data with
         | `Notation (user, _) -> fst (State.add_user user state)
         | _ -> state)
       !Builtins.builtins
       (Trie.to_seq (Trie.find_subtree [ "notation" ] init_visible)))
    f
