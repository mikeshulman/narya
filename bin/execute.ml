open Bwd
open Util
open Core
open Reporter
open Parser
open User2
open Format
module Trie = Yuujinchou.Trie

(* Execution of files (and strings), including marshaling and unmarshaling, and managing compilation units and imports. *)

let __COMPILE_VERSION__ = 2

(* This state module is for data that gets restarted when loading a new file. *)
module Loadstate = struct
  type t = {
    (* The current directory.  Used for making filenames absolute. *)
    cwd : FilePath.filename;
    (* All files whose loading is currently in progress, i.e. the path of imports that led us to the current file.  Used to check for circular imports. *)
    parents : FilePath.filename Bwd.t;
    (* All the files imported so far by the current file.  Stored in compiled files to ensure they are recompiled whenever any dependencies change. *)
    imports : (Compunit.t * FilePath.filename) Bwd.t;
    (* Whether the current file has performed any effectual actions like 'echo'.  Stored in compiled files to produce a warning. *)
    actions : bool;
  }
end

module Loading = Algaeff.State.Make (Loadstate)

let () =
  Loading.register_printer (function
    | `Get -> Some "unhandled Loading.get effect"
    | `Set _ -> Some "unhandled Loading.set effect")

(* This reader module is for data that's supplied by the executable, mostly from the command-line, and doesn't change. *)
module FlagData = struct
  type t = {
    (* Marshal all the command-line type theory flags to disk. *)
    marshal : Out_channel.t -> unit;
    (* Unmarshal all the command-line type theory flags from a disk file and check that they agree with the current ones, returning the unmarshaled ones if not. *)
    unmarshal : In_channel.t -> (unit, string) Result.t;
    (* Execute commands (don't just reformat)? *)
    execute : bool;
    (* Load files from source only (not compiled versions)? *)
    source_only : bool;
    (* All the filenames given explicitly on the command line. *)
    top_files : string list;
    (* The initial visible namespace, e.g. the builtin Π. *)
    init_visible : Scope.trie;
    (* Whether to reformat. *)
    reformat : bool;
  }
end

module Flags = Algaeff.Reader.Make (FlagData)

let () = Flags.register_printer (function `Read -> Some "unhandled Flags.read effect")
let reformat_maybe f = if (Flags.read ()).reformat then f std_formatter else ()
let reformat_maybe_ws f = if (Flags.read ()).reformat then f std_formatter else []

(* All the files that have been loaded so far in this run of the program, along with their export namespaces, compilation unit identifiers, and whether they were explicitly invoked on the command line. *)
let loaded_files : (FilePath.filename, Scope.trie * Compunit.t * bool) Hashtbl.t = Hashtbl.create 20

(* The complete merged namespace of all the files explicitly given on the command line so far.  Imported into -e and -i.  We compute it lazily because if there is no -e or -i we don't need it.  (And also so that we won't try to read the flags before they're set.) *)
let loaded_contents : Scope.trie Lazy.t ref = ref (lazy (Flags.read ()).init_visible)

(* Add something to the complete merged namespace. *)
let add_to_all trie =
  let old = !loaded_contents in
  loaded_contents := lazy (Scope.Mod.union ~prefix:Emp (Lazy.force old) trie)

let get_all () = Lazy.force !loaded_contents

(* Save all the definitions from a given loaded compilation unit to a compiled disk file, along with other data such as the command-line type theory flags, the imported files, and the (supplied) export namespace. *)
let marshal (compunit : Compunit.t) (file : FilePath.filename) (trie : Scope.trie) =
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
         | (`Constant c, loc), tag -> ((`Constant c, loc), tag)
         | (`Notation (u, _), loc), tag -> ((`Notation u, loc), tag))
       trie)
    [];
  Marshal.to_channel chan (Loading.get ()).actions []

(* Load a compilation unit from a compiled disk file, if possible.  Returns its export namespace, or None if loading from a compiled file failed. *)
let rec unmarshal (compunit : Compunit.t) (lookup : FilePath.filename -> Compunit.t)
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
            (* If so, we load all those files right away.  We don't need their returned namespaces, since we aren't typechecking our compiled file. *)
            Mbwd.miter
              (fun [ (_, ifile) ] ->
                let _ = load_file ifile false in
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
                  | `Constant c, loc ->
                      ((`Constant (Constant.remake (Hashtbl.find table) c), loc), tag)
                  | `Notation (User.User u), loc ->
                      (* We also have to re-make the notation objects since they contain constant names (print keys) and their own autonumbers (but those are only used for comparison locally so don't need to be walked elsewhere). *)
                      let key =
                        match u.key with
                        | `Constant c -> `Constant (Constant.remake (Hashtbl.find table) c)
                        | `Constr (c, i) -> `Constr (c, i) in
                      let u = User.User { u with key } in
                      ((`Notation (u, make_user u), loc), tag))
                (Marshal.from_channel chan
                  : ( [ `Constant of Constant.t | `Notation of User.prenotation ]
                      * Asai.Range.t option,
                      Scope.Param.tag )
                    Trie.t) in
            (* We check whether the compiled file had any actions, and issue a warning if so *)
            if (Marshal.from_channel chan : bool) then emit (Actions_in_compiled_file ofile);
            Some trie)
          else None
      | Error flags ->
          emit (Incompatible_flags (file, flags));
          None)
    else None
  else None

(* Load a file, possibly one specified on the command line, either from source or from a compiled version. *)
and load_file file top =
  if not (FilePath.check_extension file "ny") then fatal (Invalid_filename file);
  (* We normalize the file path to a reduced absolute one, so we can use it for a hashtable key. *)
  let file =
    if FilePath.is_relative file then FilePath.make_absolute (Loading.get ()).cwd file else file
  in
  let file = FilePath.reduce file in
  match Hashtbl.find_opt loaded_files file with
  | Some (trie, compunit, top') ->
      (* If we already loaded that file, we just return its saved export namespace, but we may need to add it to the 'all' namespace if it wasn't already there. *)
      if top && not top' then (
        add_to_all trie;
        Hashtbl.add loaded_files file (trie, compunit, true));
      (* We also add it to the list of things imported by the current ambient file.  TODO: Should that go in execute_command Import? *)
      Loading.modify (fun s -> { s with imports = Snoc (s.imports, (compunit, file)) });
      trie
  | None ->
      (* Otherwise, we have to load it.  First we check for circular dependencies. *)
      (let parents = (Loading.get ()).parents in
       if Bwd.exists (fun x -> x = file) parents then
         fatal (Circular_import (Bwd.to_list (Snoc (parents, file)))));
      (* We make a name for it *)
      let compunit = Compunit.make file in
      (* Now we record it as a file that was imported by the current file. *)
      Loading.modify (fun s -> { s with imports = Snoc (s.imports, (compunit, file)) });
      (* Then we load it, in its directory and with itself added to the list of parents. *)
      let rename i =
        let _, c, _ = Hashtbl.find loaded_files i in
        c in
      Loading.run
        ~init:
          {
            cwd = FilePath.dirname file;
            parents = Snoc ((Loading.get ()).parents, file);
            imports = Emp;
            actions = false;
          }
      @@ fun () ->
      (* If there's a compiled version, and we aren't in source-only mode, and this file wasn't specified explicitly on the command-line, we try loading the compiled version. *)
      let trie, which =
        let flags = Flags.read () in
        match
          if flags.source_only || List.mem file flags.top_files then None
          else unmarshal compunit rename file
        with
        | Some trie -> (trie, `Compiled)
        | None ->
            (* If we are in source-only mode, or this file was specified explicitly on the command-line, or if unmarshal failed (e.g. the compiled file is outdated), we load it from source. *)
            if not top then emit (Loading_file file);
            (execute_source compunit (`File file), `Source) in
      (* Then we add it to the table of loaded files and (possibly) the content of top-level files. *)
      if not top then emit (File_loaded (file, which));
      Hashtbl.add loaded_files file (trie, compunit, top);
      if top then add_to_all trie;
      (* We save the compiled version *)
      marshal compunit file trie;
      trie

(* Load an -e string or stdin. *)
and load_string ?init_visible title content =
  (* There is no caching and no change of state, since it can't be "required" from another file.  The caller specifies whether to use a special initial namespace. *)
  let trie = execute_source ?init_visible Compunit.basic (`String { title; content }) in
  (* A string is always at top-level, so we always add it to 'all'. *)
  add_to_all trie;
  trie

(* Given a source (file or string), parse and execute all the commands in it, in a local scope that starts with either the supplied scope or a default one. *)
and execute_source ?(init_visible = (Flags.read ()).init_visible) compunit
    (source : Asai.Range.source) =
  reformat_maybe (fun ppf -> Format.pp_open_vbox ppf 0);
  History.run_with_scope ~init_visible @@ fun () ->
  let p, src = Parser.Command.Parse.start_parse source in
  Compunit.Current.run ~env:compunit @@ fun () ->
  Reporter.try_with
    (fun () ->
      batch true [] p src;
      if Eternity.unsolved () > 0 then Reporter.fatal (Open_holes_remaining source))
    ~fatal:(fun d ->
      match d.message with
      | Quit _ ->
          let src =
            match source with
            | `File name -> Some name
            | `String { title; _ } -> title in
          Reporter.emit (Quit src)
      | _ -> Reporter.fatal_diagnostic d);
  Scope.get_export ()

(* Subroutine that parses and executes all the commands in a source. *)
and batch first ws p src =
  let reformat_end () =
    reformat_maybe (fun ppf ->
        let ws = Whitespace.ensure_ending_newlines 2 ws in
        Print.pp_ws `None ppf ws;
        Format.pp_close_box ppf ()) in
  let cmd = Parser.Command.Parse.final p in
  if cmd = Eof then reformat_end ()
  else (
    Fun.protect
      (fun () -> if (Flags.read ()).execute then execute_command cmd)
      ~finally:reformat_end;
    let ws =
      reformat_maybe_ws @@ fun ppf ->
      let ws = if first then ws else Whitespace.ensure_starting_newlines 2 ws in
      Print.pp_ws `None ppf ws;
      Parser.Command.pp_command ppf cmd in
    let p, src = Parser.Command.Parse.restart_parse p src in
    batch false ws p src)

(* Wrapper around Parser.Command.execute that passes it the correct callbacks. *)
and execute_command cmd =
  let action_taken () = Loading.modify (fun s -> { s with actions = true }) in
  let get_file file = load_file file false in
  Parser.Command.execute ~action_taken ~get_file cmd
