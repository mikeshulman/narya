open Bwd
open Util
open Core
open Reporter
open User
module Trie = Yuujinchou.Trie

(* Compilation units (i.e. files).  This module is called "Units" because "Unit" is the module "struct type t = unit end".  (-: *)

let __COMPILE_VERSION__ = 1

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
    actions : bool;
  }
end

module Loading = Algaeff.State.Make (Loadstate)

module FlagData = struct
  type t = { marshal : Out_channel.t -> unit; unmarshal : In_channel.t -> (unit, string) Result.t }
end

module Flags = Algaeff.Reader.Make (FlagData)

let marshal (compunit : Compunit.t) (file : FilePath.filename) (trie : trie) =
  let ofile = FilePath.replace_extension file "nyo" in
  Out_channel.with_open_bin ofile @@ fun chan ->
  Marshal.to_channel chan __COMPILE_VERSION__ [];
  (Flags.read ()).marshal chan;
  Marshal.to_channel chan compunit [];
  Marshal.to_channel chan (Loading.get ()).imports [];
  Global.to_channel_unit chan compunit [];
  Marshal.to_channel chan
    (Trie.map
       (fun _ -> function
         | `Constant c, tag -> (`Constant c, tag)
         | `Notation (u, _), tag -> (`Notation u, tag))
       trie)
    [];
  Marshal.to_channel chan (Loading.get ()).actions []

let unmarshal (compunit : Compunit.t) (lookup : FilePath.filename -> Compunit.t)
    (file : FilePath.filename) =
  let ofile = FilePath.replace_extension file "nyo" in
  (* To load a compiled file, first of all both the compiled file and its source file must exist, and the compiled file must be newer than the source. *)
  if FileUtil.test Is_file file && FileUtil.test (Is_newer_than file) ofile then
    (* Now we can start loading things. *)
    In_channel.with_open_bin ofile @@ fun chan ->
    (* We check it was compiled with the same version as us. *)
    let old_version = (Marshal.from_channel chan : int) in
    if old_version = __COMPILE_VERSION__ then (
      (* We also check it was compiled with the same type theory flags as us. *)
      match (Flags.read ()).unmarshal chan with
      | Ok () ->
          let old_compunit = (Marshal.from_channel chan : Compunit.t) in
          (* Now we make sure none of the files *it* imports have been modified more recently than the compilation, and that they have all been compiled. *)
          let old_imports = (Marshal.from_channel chan : (Compunit.t * FilePath.filename) Bwd.t) in
          if
            Bwd.for_all
              (fun (_, ifile) ->
                let oifile = FilePath.replace_extension file "nyo" in
                FileUtil.test Is_file oifile
                && FileUtil.test (Is_newer_than ifile) oifile
                && FileUtil.test (Is_older_than ofile) ifile)
              old_imports
          then (
            (* If so, we load all those files.  We don't need their returned namespaces, since we aren't typechecking our compiled file. *)
            Mbwd.miter
              (fun [ (_, ifile) ] ->
                let _ = get_file ifile in
                ())
              [ old_imports ];
            (* We create a hashtable mapping the old compunits to new ones. *)
            let table = Hashtbl.create 20 in
            Mbwd.miter (fun [ (i, ifile) ] -> Hashtbl.add table i (lookup ifile)) [ old_imports ];
            Hashtbl.add table old_compunit compunit;
            (* Now we load the definitions from the compiled file, replacing all the old compunits by the new ones. *)
            Global.from_channel_unit (Hashtbl.find table) chan compunit;
            let trie =
              Trie.map
                (fun _ (data, tag) ->
                  match data with
                  | `Constant c -> (`Constant (Constant.remake (Hashtbl.find table) c), tag)
                  | `Notation (User u) ->
                      (* We also have to re-make the notation objects since they contain constant names (print keys) and their own autonumbers (but those are only used for comparison locally so don't need to be walked elsewhere). *)
                      let key =
                        match u.key with
                        | `Constant c -> `Constant (Constant.remake (Hashtbl.find table) c)
                        | `Constr (c, i) -> `Constr (c, i) in
                      let u = User { u with key } in
                      (`Notation (u, State.make_user u), tag))
                (Marshal.from_channel chan
                  : ([ `Constant of Constant.t | `Notation of user_notation ], Scope.P.tag) Trie.t)
            in
            (* We check whether the compiled file had any actions, and issue a warning if so *)
            if (Marshal.from_channel chan : bool) then emit (Actions_in_compiled_file ofile);
            Some trie)
          else None
      | Error flags ->
          emit (Incompatible_flags (file, flags));
          None)
    else None
  else None

(* This is how the executable supplies a callback that loads files.  It will always be passed a reduced absolute filename.  We take care of calling that function as needed and caching the results in a hashtable for future calls.  We also compute the result of combining all the units, but lazily since we'll only need it if there are command-line strings, stdin, or interactive.  The first argument is a default initial visible namespace, which can be overridden. *)
let with_execute :
    type a. bool -> trie -> (trie -> Compunit.t -> Asai.Range.source -> trie) -> (unit -> a) -> a =
 fun source_only init execute f ->
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
                    if not (FilePath.check_extension file "ny") then fatal (Invalid_filename file);
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
                        let compunit = Compunit.make file in
                        let rename i =
                          let _, c, _ = Hashtbl.find table i in
                          c in
                        let trie =
                          Loading.run
                            ~init:
                              {
                                cwd = FilePath.dirname file;
                                parents = Snoc ((Loading.get ()).parents, file);
                                imports = Emp;
                                actions = false;
                              }
                          @@ fun () ->
                          (* If there's a compiled version, and we aren't in source-only mode, we load that; otherwise we load it from source. *)
                          let trie, which =
                            go @@ fun () ->
                            match if source_only then None else unmarshal compunit rename file with
                            | Some trie -> (trie, `Compiled)
                            | None ->
                                if not top then emit (Loading_file file);
                                (execute init compunit (`File file), `Source) in
                          (* Then we add it to the table and (possibly) 'all'. *)
                          if not top then emit (File_loaded (file, which));
                          Hashtbl.add table file (trie, compunit, top);
                          if top then add_to_all trie;
                          (* We save the compiled version *)
                          marshal compunit file trie;
                          trie in
                        (* Now we record it as a file that was imported by the current file. *)
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
  Loading.run ~init:{ cwd = Sys.getcwd (); parents = Emp; imports = Emp; actions = false }
  @@ fun () -> go f

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
