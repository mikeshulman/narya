open Bwd
open Util
open Core
open Reporter
open Parser
open PPrint
open Print
open User2
module Trie = Yuujinchou.Trie

(* Execution of files (and strings), including marshaling and unmarshaling, and managing compilation units and imports. *)

let __COMPILE_VERSION__ = 4

(* This state module is for data that gets restarted when loading a new file. *)
module Loadstate = struct
  type t = {
    (* The current directory.  Used for making filenames absolute. *)
    cwd : FilePath.filename;
    (* All files whose loading is currently in progress, i.e. the path of imports that led us to the current file.  Used to check for circular imports. *)
    parents : FilePath.filename Bwd.t;
    (* All the files imported so far by the current file, *transitively* (that is, files it imports, and files *they* import, etc.).  Stored in compiled files to ensure they are recompiled whenever any dependencies change, and for linking purposes. *)
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
    (* Load files from source only (not compiled versions). *)
    source_only : bool;
    (* All the filenames given explicitly on the command line. *)
    top_files : string list;
    (* The initial visible namespace, e.g. the builtin Π. *)
    init_visible : Scope.trie;
    (* Whether to reformat explicitly-loaded files *)
    reformat : bool;
  }
end

module Flags = Algaeff.Reader.Make (FlagData)

let () = Flags.register_printer (function `Read -> Some "unhandled Flags.read effect")

module Loaded = struct
  type _ Effect.t +=
    | Add_to_files :
        FilePath.filename * Scope.trie * Global.unit_entry * Compunit.t * bool
        -> unit Effect.t
    | Get_file :
        FilePath.filename
        -> (Scope.trie * Global.unit_entry * Compunit.t * bool) option Effect.t
    | Add_to_scope : Scope.trie -> unit Effect.t
    | Get_scope : Scope.trie Effect.t

  open Effect.Deep

  let run f =
    (* All the files that have been loaded so far in this run of the program, along with their export namespaces, compilation unit identifiers, and whether they were explicitly invoked on the command line. *)
    let loaded_files :
        (FilePath.filename, Scope.trie * Global.unit_entry * Compunit.t * bool) Hashtbl.t =
      Hashtbl.create 20 in
    (* The complete merged namespace of all the files explicitly given on the command line so far.  Imported into -e and -i.  We compute it lazily because if there is no -e or -i we don't need it.  (And also so that we won't try to read the flags before they're set.) *)
    let loaded_contents : Scope.trie Lazy.t ref = ref (lazy (Flags.read ()).init_visible) in
    let effc : type b a. b Effect.t -> ((b, a) continuation -> a) option = function
      | Add_to_files (file, trie, globals, compunit, explicit) ->
          Some
            (fun k ->
              Hashtbl.add loaded_files file (trie, globals, compunit, explicit);
              continue k ())
      | Get_file file -> Some (fun k -> continue k (Hashtbl.find_opt loaded_files file))
      | Add_to_scope trie ->
          Some
            (fun k ->
              let old = !loaded_contents in
              loaded_contents := lazy (Scope.Mod.union ~prefix:Emp (Lazy.force old) trie);
              continue k ())
      (* Add something to the complete merged namespace. *)
      | Get_scope -> Some (fun k -> continue k (Lazy.force !loaded_contents))
      | _ -> None in
    try_with f () { effc }

  let add_to_scope trie = Effect.perform (Add_to_scope trie)
  let get_scope () = Effect.perform Get_scope
  let get_file file = Effect.perform (Get_file file)

  let add_to_files file trie globals compunit explicit =
    Effect.perform (Add_to_files (file, trie, globals, compunit, explicit))
end

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
  (* To load a compiled file, first of all both the compiled file and its source file must exist, and the compiled file must be not older than the source.  (If the source was reformatted at the time of compiling, they could be exactly the same age.) *)
  if
    FileUtil.test Is_file file
    && FileUtil.test Is_file ofile
    && not (FileUtil.test (Is_older_than file) ofile)
  then
    (* Now we can start loading things. *)
    In_channel.with_open_bin ofile @@ fun chan ->
    (* We check it was compiled with the same version as us. *)
    let old_version = (Marshal.from_channel chan : int) in
    if old_version = __COMPILE_VERSION__ then (
      (* We also check it was compiled with the same type theory flags as us. *)
      match (Flags.read ()).unmarshal chan with
      | Ok () ->
          let old_compunit = (Marshal.from_channel chan : Compunit.t) in
          (* Now we make sure none of the files *it* imports (transitively) have been modified more recently than the compilation, and that they have all been compiled. *)
          let old_imports = (Marshal.from_channel chan : (Compunit.t * FilePath.filename) Bwd.t) in
          if
            Bwd.for_all
              (fun (_, ifile) ->
                let oifile = FilePath.replace_extension file "nyo" in
                FileUtil.test Is_file oifile
                && (not (FileUtil.test (Is_older_than ifile) oifile))
                && not (FileUtil.test (Is_newer_than ofile) ifile))
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
            let find_in_table x =
              if x = Compunit.basic then Compunit.basic
              else
                Hashtbl.find_opt table x
                <|> Anomaly "missing compunit while unmarshaling compiled file" in
            (* Now we load the definitions from the compiled file, replacing all the old compunits by the new ones. *)
            let unit_entry = Global.from_channel_unit find_in_table chan compunit in
            let trie =
              Trie.map
                (fun _ (data, tag) ->
                  match data with
                  | `Constant c, loc -> ((`Constant (Constant.remake find_in_table c), loc), tag)
                  | `Notation (User.User u), loc ->
                      (* We also have to re-make the notation objects since they contain constant names (print keys) and their own autonumbers (but those are only used for comparison locally so don't need to be walked elsewhere). *)
                      let key =
                        match u.key with
                        | `Constant c -> `Constant (Constant.remake find_in_table c)
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
            Some (trie, unit_entry))
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
  match Loaded.get_file file with
  | Some (trie, globals, compunit, top') ->
      (* If we already loaded that file, we just add it back into Global and return its saved export namespace.  We may need to add it to the 'all' namespace if it wasn't already there. *)
      if top && not top' then (
        Loaded.add_to_scope trie;
        Loaded.add_to_files file trie globals compunit true);
      (* We also add it to the list of things imported by the current ambient file.  TODO: Should that go in execute_command Import? *)
      Loading.modify (fun s -> { s with imports = Snoc (s.imports, (compunit, file)) });
      Global.add_unit compunit globals;
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
        let _, _, c, _ = Loaded.get_file i <|> Anomaly "missing file in load_file" in
        c in
      let trie, imports =
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
        let trie, globals, which =
          let flags = Flags.read () in
          match
            if flags.source_only || List.mem file flags.top_files then None
            else unmarshal compunit rename file
          with
          | Some (trie, globals) -> (trie, globals, `Compiled)
          | None ->
              (* If we are in source-only mode, or this file was specified explicitly on the command-line, or if unmarshal failed (e.g. the compiled file is outdated), we load it from source. *)
              if not top then emit (Loading_file file);
              (* If reformatting is enabled, and this file was explicitly specified on the command line, create a buffer to hold its reformatting. *)
              let buf =
                if (Flags.read ()).reformat && List.mem file flags.top_files then
                  Some (Buffer.create 100)
                else None in
              let renderer = Option.map (PPrint.ToBuffer.pretty 1.0 (Display.columns ())) buf in
              (* Parse and execute the file and save its exported trie and global definitions *)
              let exported = execute_source compunit ?renderer (`File file) in
              (match buf with
              | None -> ()
              | Some buf -> (
                  (* If the reformatted version didn't change, do nothing. *)
                  let infile = open_in_bin file in
                  let oldstr =
                    Fun.protect ~finally:(fun () -> close_in infile) @@ fun () ->
                    really_input_string infile (in_channel_length infile) in
                  if oldstr <> Buffer.contents buf then
                    try
                      (* Back up the original file to a new backup file name. *)
                      let bakfile, n = (file ^ ".bak.", ref 0) in
                      while FileUtil.test Is_file (bakfile ^ string_of_int !n) do
                        n := !n + 1
                      done;
                      let bakfile = bakfile ^ string_of_int !n in
                      FileUtil.cp [ file ] bakfile;
                      (* Overwrite the file with its reformatted version. *)
                      let outfile = open_out file in
                      Fun.protect ~finally:(fun () -> close_out outfile) @@ fun () ->
                      output_string outfile (Buffer.contents buf)
                      (* Ignore file errors (e.g. read-only source file) *)
                    with Sys_error _ -> ()));
              (exported, Global.find_unit compunit, `Source) in
        (* Then we add it to the table of loaded files and (possibly) the content of top-level files. *)
        if not top then emit (File_loaded (file, which));
        Loaded.add_to_files file trie globals compunit top;
        if top then Loaded.add_to_scope trie;
        (* We save the compiled version *)
        marshal compunit file trie;
        (trie, (Loading.get ()).imports) in
      (* We add the files that it imports to those of the current file, since the imports list is supposed to be transitive. *)
      Loading.modify (fun s -> { s with imports = Bwd_extra.append s.imports imports });
      trie

(* Load an -e string or stdin. *)
and load_string ?init_visible title content =
  (* There is no caching and no change of state, since it can't be "required" from another file.  The caller specifies whether to use a special initial namespace. *)
  let trie = execute_source ?init_visible Compunit.basic (`String { title; content }) in
  (* A string is always at top-level, so we always add it to 'all'. *)
  Loaded.add_to_scope trie;
  trie

(* Given a source (file or string), parse and execute all the commands in it, in a local scope that starts with either the supplied scope or a default one. *)
and execute_source ?(init_visible = (Flags.read ()).init_visible) ?renderer compunit
    (source : Asai.Range.source) =
  History.run_with_scope ~init_visible @@ fun () ->
  let p, src = Parser.Command.Parse.start_parse source in
  Compunit.Current.run ~env:compunit @@ fun () ->
  Reporter.try_with
    (fun () -> batch renderer p src `None [])
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

(* Parse, execute (if requested by Flags), and reformat (if requested by Flags) all the commands in a source. *)
and batch renderer p src cdns ws =
  match Parser.Command.Parse.final p with
  | Eof -> (
      match renderer with
      | Some render -> render (pp_ws `Cut ws)
      | None -> ())
  | Bof ws ->
      let p, src = Parser.Command.Parse.restart_parse p src in
      batch renderer p src `Bof ws
  | cmd ->
      let new_cdns = Parser.Command.condense cmd in
      execute_command cmd;
      let ws =
        match renderer with
        | Some render ->
            let ws =
              if cdns = `Bof || (cdns <> `None && cdns = new_cdns) then
                Whitespace.normalize_no_blanks ws
              else Whitespace.normalize 2 ws in
            let space_before_starting_comment = if cdns = `Bof then Some 0 else None in
            let pcmd, wcmd = Parser.Command.pp_command cmd in
            render
              (pp_ws ?space_before_starting_comment (if cdns = `Bof then `None else `Cut) ws ^^ pcmd);
            wcmd
        | None -> [] in
      let p, src = Parser.Command.Parse.restart_parse p src in
      batch renderer p src new_cdns ws

(* Wrapper around Parser.Command.execute that passes it the correct callbacks.  Does NOT check flags or reformat. *)
and execute_command cmd =
  let action_taken () = Loading.modify (fun s -> { s with actions = true }) in
  let get_file file = load_file file false in
  Parser.Command.execute ~action_taken ~get_file cmd
