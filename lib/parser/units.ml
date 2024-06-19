open Bwd
open Core
open Reporter
module Trie = Yuujinchou.Trie

type trie = (Scope.P.data, Scope.P.tag) Trie.t

(* For separate compilation, we expect the executable to know how to load compilation units and compute their resulting export namespaces.  We wrap this in an effect, so that it can also be invoked *during* the loading of some other unit, with a 'require' command.  We also include an effect that combines all the top-level namespaces (i.e. those not only loaded "transitively" through require) so far into a single one.  The boolean argument to load_unit indicates whether it is being invoked from top level, and the namespace is a starting visible one to override the default.  *)

type _ Effect.t +=
  | Load_unit : Asai.Range.source * trie option * bool -> trie Effect.t
  | All_units : trie Effect.t

let get ?init source top = Effect.perform (Load_unit (source, init, top))

(* This is the version that is called *by* the executable, since it doesn't have any use for the resulting namespace, and it is always loading at top-level. *)
let load ?init source =
  let _ = get ?init source true in
  ()

let all () = Effect.perform All_units

module Loadstate = struct
  type t = { cwd : FilePath.filename; parents : FilePath.filename Bwd.t }
end

module Loading = Algaeff.Reader.Make (Loadstate)

(* This is how the executable supplies a callback that loads files.  We take care of calling that function as needed and caching the results in a hashtable for future calls.  We also compute the result of combining all the units, but lazily since we'll only need it if there are command-line strings, stdin, or interactive.  The first argument is a default initial visible namespace, which can be overridden. *)
let with_compile : type a. trie -> (trie -> Asai.Range.source -> trie) -> (unit -> a) -> a =
 fun init compute f ->
  let table : (FilePath.filename, trie * bool) Hashtbl.t = Hashtbl.create 20 in
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
            | Load_unit (source, start, top) -> (
                let start = Option.value start ~default:init in
                Option.some @@ fun (k : (a, _) continuation) ->
                match source with
                | `File file -> (
                    (* We normalize the file path to a reduced absolute one, so we can use it for a hashtable key. *)
                    let file =
                      if FilePath.is_relative file then
                        FilePath.make_absolute (Loading.read ()).cwd file
                      else file in
                    let file = FilePath.reduce file in
                    match Hashtbl.find_opt table file with
                    | Some (trie, top') ->
                        (* If we already loaded that file, we just return its saved export namespace, but we may need to add it to the 'all' namespace if it wasn't already there. *)
                        if top && not top' then (
                          add_to_all trie;
                          Hashtbl.add table file (trie, true));
                        continue k trie
                    | None ->
                        (* Otherwise, we have to load it.  First we check for circular dependencies. *)
                        (let parents = (Loading.read ()).parents in
                         if Bwd.exists (fun x -> x = file) parents then
                           fatal (Circular_import (Bwd.to_list (Snoc (parents, file)))));
                        (* Then we load it, in its directory and with itself added to the list of parents, and then add it to the table and (possibly) 'all'. *)
                        if not top then emit (Loading_file file);
                        let trie =
                          Loading.scope (fun s ->
                              { cwd = FilePath.dirname file; parents = Snoc (s.parents, file) })
                          @@ fun () ->
                          go @@ fun () -> compute start source in
                        if not top then emit (File_loaded file);
                        Hashtbl.add table file (trie, top);
                        if top then add_to_all trie;
                        continue k trie)
                | `String _ ->
                    (* In the case of a string input there is no caching and no change of state, since it can't be "required" from another file.  But we still have the option of adding it to "all".  *)
                    let trie = go @@ fun () -> compute start source in
                    if top then add_to_all trie;
                    continue k trie)
            | All_units ->
                Option.some @@ fun (k : (a, _) continuation) -> continue k (Lazy.force !all)
            | _ -> None);
      } in
  Loading.run ~env:{ cwd = Sys.getcwd (); parents = Emp } @@ fun () -> go f

let run ~(init_visible : trie) f =
  Scope.run ~init_visible @@ fun () ->
  State.run_on
    (Seq.fold_left
       (fun state (_, (data, _)) ->
         match data with
         | `Notation (key, notn) -> state |> State.add_with_print key notn
         | _ -> state)
       !Builtins.builtins
       (Trie.to_seq (Trie.find_subtree [ "notation" ] init_visible)))
    f
