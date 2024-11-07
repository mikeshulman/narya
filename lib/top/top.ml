(* This file contains all the code for the main executable that doesn't specify how we interact with the user (such as parsing command-line arguments and running an interactive REPL).  Thus, it can be shared between the ordinary executable and any variants like the in-browser javascript version. *)

open Bwd
open Util
open Core
open Parser
module Execute = Execute

(* Global flags, as set for instance by command-line arguments. *)
let inputs : [ `String of string | `File of string | `Stdin ] Bwd.t ref = ref Emp
let anon_arg filename = inputs := Snoc (!inputs, `File filename)
let reformat = ref false
let verbose = ref false
let compact = ref false
let unicode = ref true
let execute = ref true
let arity = ref 2
let refl_char = ref 'e'
let refl_strings = ref [ "refl"; "Id" ]
let internal = ref true
let discreteness = ref false
let source_only = ref false

(* Marshal the current flags to a file. *)
let marshal_flags chan =
  Marshal.to_channel chan !arity [];
  Marshal.to_channel chan !refl_char [];
  Marshal.to_channel chan !refl_strings [];
  Marshal.to_channel chan !internal [];
  Marshal.to_channel chan !discreteness []

(* Unmarshal saved flags from a file and check that they agree with the current ones. *)
let unmarshal_flags chan =
  let ar = (Marshal.from_channel chan : int) in
  let rc = (Marshal.from_channel chan : char) in
  let rs = (Marshal.from_channel chan : string list) in
  let int = (Marshal.from_channel chan : bool) in
  let disc = (Marshal.from_channel chan : bool) in
  if ar = !arity && rc = !refl_char && rs = !refl_strings && int = !internal && disc = !discreteness
  then Ok ()
  else
    Error
      (Printf.sprintf "-arity %d -direction %s %s%s" ar
         (String.concat "," (String.make 1 rc :: rs))
         (if int then "-internal" else "-external")
         (if disc then " -discreteness" else ""))

(* Given a string like "r,refl,Id" as in a command-line "-direction" argument, set refl_char and refl_strings *)
let set_refls str =
  match String.split_on_char ',' str with
  | [] -> raise (Failure "Empty direction names")
  | c :: _ when String.length c <> 1 || c.[0] < 'a' || c.[0] > 'z' ->
      raise (Failure "Direction name must be a single lowercase letter")
  | c :: names ->
      refl_char := c.[0];
      refl_strings := names

(* Given a command and preceeding whitespace, execute the command (if we are executing commands), alert about open holes, and print the reformatted command if requested. *)
let do_command = function
  | ws, None -> Execute.reformat_maybe @@ fun ppf -> Print.pp_ws `None ppf ws
  | ws, Some cmd ->
      if !execute then Execute.execute_command cmd;
      let n = Eternity.unsolved () in
      if n > 0 then Reporter.emit (Open_holes n);
      Execute.reformat_maybe @@ fun ppf ->
      Print.pp_ws `None ppf ws;
      let last = Parser.Command.pp_command ppf cmd in
      Print.pp_ws `None ppf last;
      Format.pp_print_newline ppf ()

module Terminal = Asai.Tty.Make (Core.Reporter.Code)

(* This function is called to wrap whatever "interactive mode" is implemented by the caller.  It sets up the environment and all the effect handlers based on the global flags, loads all the files and strings specified in the global flags, and then runs the callback. *)
let run_top ?use_ansi ?(exiter = fun () -> exit 1) f =
  Parser.Unparse.install ();
  Parser.Scope.Mod.run @@ fun () ->
  History.run_empty @@ fun () ->
  Eternity.run ~init:Eternity.empty @@ fun () ->
  (* By default, we ignore the hole positions. *)
  Global.HolePos.try_with ~get:(fun () -> { holes = Emp }) ~set:(fun _ -> ()) @@ fun () ->
  Printconfig.run
    ~env:
      {
        style = (if !compact then `Compact else `Noncompact);
        state = `Case;
        chars = (if !unicode then `Unicode else `ASCII);
      }
  @@ fun () ->
  Readback.Display.run ~env:false @@ fun () ->
  Core.Discrete.run ~env:!discreteness @@ fun () ->
  Reporter.run
    ~emit:(fun d ->
      if !verbose || d.severity = Error || d.severity = Warning then
        Terminal.display ?use_ansi ~output:stderr d)
    ~fatal:(fun d ->
      Terminal.display ?use_ansi ~output:stderr d;
      exiter ())
  @@ fun () ->
  if !arity < 1 || !arity > 9 then Reporter.fatal (Unimplemented "arities outside [1,9]");
  if !discreteness && !arity > 1 then Reporter.fatal (Unimplemented "discreteness with arity > 1");
  Dim.Endpoints.set_len !arity;
  Dim.Endpoints.set_char !refl_char;
  Dim.Endpoints.set_names !refl_strings;
  Dim.Endpoints.set_internal !internal;
  (* The initial namespace for all compilation units. *)
  Compunit.Current.run ~env:Compunit.basic @@ fun () ->
  let top_files =
    Bwd.fold_right
      (fun input acc ->
        match input with
        | `File file -> FilePath.make_absolute (Sys.getcwd ()) file :: acc
        | _ -> acc)
      !inputs [] in
  Execute.Flags.run
    ~env:
      {
        marshal = marshal_flags;
        unmarshal = unmarshal_flags;
        execute = !execute;
        source_only = !source_only;
        init_visible = Parser.Pi.install Scope.Trie.empty;
        top_files;
        reformat = !reformat;
      }
  @@ fun () ->
  Execute.Loading.run ~init:{ cwd = Sys.getcwd (); parents = Emp; imports = Emp; actions = false }
  @@ fun () ->
  ( Core.Command.Mode.run ~env:{ interactive = false } @@ fun () ->
    Mbwd.miter
      (fun [ input ] ->
        match input with
        | `File filename ->
            let _ = Execute.load_file filename true in
            ()
        | `Stdin ->
            let content = In_channel.input_all stdin in
            let _ = Execute.load_string (Some "stdin") content in
            ()
        (* Command-line strings have all the previous units loaded without needing to import them. *)
        | `String content ->
            let _ =
              Execute.load_string ~init_visible:(Execute.get_all ())
                (Some "command-line exec string") content in
            ())
      [ !inputs ] );
  (* Interactive mode also has all the other units loaded. *)
  History.set_visible (Execute.get_all ());
  Core.Command.Mode.run ~env:{ interactive = true } @@ fun () -> f ()
