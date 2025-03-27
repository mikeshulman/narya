(* This file contains all the code for the main executable that doesn't specify how we interact with the user (such as parsing command-line arguments and running an interactive REPL).  Thus, it can be shared between the ordinary executable and any variants like the in-browser javascript version. *)

open Bwd
open Util
open Core
open Reporter
open Readback
open Parser
module Execute = Execute

(* Global flags, as set for instance by command-line arguments. *)
let inputs : [ `String of string | `File of string | `Stdin ] Bwd.t ref = ref Emp
let anon_arg filename = inputs := Snoc (!inputs, `File filename)
let verbose = ref false
let reformat = ref true
let unicode = ref true
let arity = ref 2
let refl_char = ref 'e'
let refl_names = ref [ "refl"; "Id" ]
let internal = ref true
let discreteness = ref false
let source_only = ref false
let number_metas = ref true
let parenthesize_arguments = ref false
let extra_spaces = ref true
let show_function_boundaries = ref false
let show_type_boundaries = ref false

(* Marshal the current flags to a file. *)
let marshal_flags chan =
  Marshal.to_channel chan !arity [];
  Marshal.to_channel chan !refl_char [];
  Marshal.to_channel chan !refl_names [];
  Marshal.to_channel chan !internal [];
  Marshal.to_channel chan !discreteness []

(* Unmarshal saved flags from a file and check that they agree with the current ones. *)
let unmarshal_flags chan =
  let ar = (Marshal.from_channel chan : int) in
  let rc = (Marshal.from_channel chan : char) in
  let rs = (Marshal.from_channel chan : string list) in
  let int = (Marshal.from_channel chan : bool) in
  let disc = (Marshal.from_channel chan : bool) in
  if ar = !arity && rc = !refl_char && rs = !refl_names && int = !internal && disc = !discreteness
  then Ok ()
  else
    Error
      (Printf.sprintf "-arity %d -direction %s %s%s" ar
         (String.concat "," (String.make 1 rc :: rs))
         (if int then "-internal" else "-external")
         (if disc then " -discreteness" else ""))

(* Given a string like "r,refl,Id" as in a command-line "-direction" argument, set refl_char and refl_names *)
let set_refls str =
  match String.split_on_char ',' str with
  | [] -> raise (Failure "Empty direction names")
  | c :: _ when String.length c <> 1 || c.[0] < 'a' || c.[0] > 'z' ->
      raise (Failure "Direction name must be a single lowercase letter")
  | c :: names ->
      refl_char := c.[0];
      refl_names := names

(* This exception is raised when a fatal error occurs in loading the non-interactive inputs.  The caller should catch it and perform an appropriate kind of "exit".  *)
exception Exit

(* This function is called to wrap whatever "interactive mode" is implemented by the caller.  It sets up the environment and all the effect handlers based on the global flags, loads all the files and strings specified in the global flags, and then runs the callback. *)
let run_top ?use_ansi ?onechar_ops ?digit_vars ?ascii_symbols f =
  Check.Oracle.run ~ask:(fun _ -> Ok ()) @@ fun () ->
  Lexer.Specials.run ?onechar_ops ?ascii_symbols ?digit_vars @@ fun () ->
  Parser.Unparse.install ();
  Parser.Scope.Mod.run @@ fun () ->
  History.run_empty @@ fun () ->
  Eternity.run ~init:Eternity.empty @@ fun () ->
  (* Holes are allowed in command-line files, strings, and interactive modes, although we will raise an error *after* completing any command-line files or strings that contain holes. *)
  Global.HolesAllowed.run ~env:(Ok ()) @@ fun () ->
  (* By default, we ignore the hole positions. *)
  Global.HolePos.try_with ~get:(fun () -> { holes = Emp; offset = 0 }) ~set:(fun _ -> ())
  @@ fun () ->
  Display.run
    ~init:
      {
        chars = (if !unicode then `Unicode else `ASCII);
        metas = (if !number_metas then `Numbered else `Anonymous);
        argstyle = (if !parenthesize_arguments then `Parens else `Spaces);
        spacing = (if !extra_spaces then `Wide else `Narrow);
        function_boundaries = (if !show_function_boundaries then `Show else `Hide);
        type_boundaries = (if !show_type_boundaries then `Show else `Hide);
        holes = `Without_number;
      }
  @@ fun () ->
  Annotate.run @@ fun () ->
  Readback.Displaying.run ~env:false @@ fun () ->
  Core.Discrete.run ~env:!discreteness @@ fun () ->
  if !arity < 1 || !arity > 9 then Reporter.fatal (Unimplemented "arities outside [1,9]");
  if !discreteness && !arity > 1 then Reporter.fatal (Unimplemented "discreteness with arity > 1");
  Dim.Endpoints.run ~arity:!arity ~refl_char:!refl_char ~refl_names:!refl_names ~internal:!internal
  @@ fun () ->
  (* We have to put Reporter.run inside Endpoints.run, so we can display dimensions *)
  Reporter.run
    ~emit:(fun d ->
      if !verbose || d.severity = Error || d.severity = Warning then
        Reporter.display ?use_ansi ~output:stderr d)
    ~fatal:(fun d ->
      Reporter.display ?use_ansi ~output:stderr d;
      raise Exit)
  @@ fun () ->
  (* Printing errors that happen outside of any other error should be reported as fatal errors on their own. *)
  Reporter.Code.PrintingError.run ~env:(fun d -> fatal d) @@ fun () ->
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
        source_only = !source_only;
        init_visible = Parser.Pi.install Scope.Trie.empty;
        top_files;
        reformat = !reformat;
      }
  @@ fun () ->
  Execute.Loaded.run @@ fun () ->
  Execute.Loading.run ~init:{ cwd = Sys.getcwd (); parents = Emp; imports = Emp; actions = false }
  @@ fun () ->
  ( Core.Command.Mode.run ~env:{ interactive = false } @@ fun () ->
    Mbwd.miter
      (fun [ input ] ->
        let source =
          match input with
          | `File filename ->
              let _ = Execute.load_file filename true in
              `File filename
          | `Stdin ->
              let content = In_channel.input_all stdin in
              let _ = Execute.load_string (Some "stdin") content in
              `Stdin
          (* Command-line strings have all the previous units loaded without needing to import them. *)
          | `String content ->
              let _ =
                Execute.load_string ~init_visible:(Execute.Loaded.get_scope ())
                  (Some "command-line exec string") content in
              `String in
        if Eternity.unsolved () > 0 then Reporter.fatal (Open_holes_remaining source))
      [ !inputs ] );
  (* Interactive mode also has all the other units loaded. *)
  History.set_visible (Execute.Loaded.get_scope ());
  Core.Command.Mode.run ~env:{ interactive = true } @@ fun () ->
  History.start_undoing ();
  f ()

(* Some applications may not be able to put their entire main loop inside a single call to "run_top".  Specifically, js_of_ocaml applications may need to return control to the browser periodically, but want to maintain the state that's normally stored in the effect handlers wrapped by run_top.  To accommodate this, we implement a "pausable" coroutine version of run_top, using effects, that saves a continuation inside all the handlers and returns to it whenever needed.  When our run_top callback finishes a single command, it yields control by performing the "Yield" effect, passing the output of the command it just executed.  The handler for this effect doesn't immediately continue, but stores the continuation in a global variable and returns control to the caller.  Then when we need to re-enter run_top, the continuation is resumed, passing it the code to be executed. *)

exception Halt

module Pauseable (R : Signatures.Type) = struct
  open Effect.Deep

  type _ Effect.t += Yield : R.t -> (unit -> R.t) Effect.t

  exception Halt

  (* The stored continuation, which points into the callback inside run_top. *)
  let cont : (unit -> R.t, R.t) continuation option ref = ref None

  (* The effect handler that saves the continuation and returns the output passed to 'Yield'. *)
  let effc : type b. b Effect.t -> ((b, R.t) continuation -> R.t) option = function
    | Yield output ->
        Some
          (fun k ->
            cont := Some k;
            output)
    | _ -> None

  (* The coroutine.  This calls itself with an infinite recursion and so never actually returns in an ordinary way, only by performing effects.  But it is declared to have a return type of R.t, to match that of the effects. *)
  let rec corun_top (f : unit -> R.t) : R.t =
    (* The "Yield" effect returns control to the caller until we are continued.  At that point execution resumes here with a new callback, which we then pass off to ourselves recursively. *)
    corun_top (Effect.perform (Yield (f ())))

  (* Whenever we need to restart, we discontinue the continuation, if any, and reset it. *)
  let halt () =
    try
      match !cont with
      | Some k ->
          let _ = discontinue k Halt in
          ()
      | None -> ()
    with Halt -> cont := None

  (* We initialize the setup by calling run_top inside the effect handler. *)
  let init ?use_ansi ?onechar_ops ?digit_vars ?ascii_symbols f =
    (* First we discontinue any existing continuation, to avoid leaks. *)
    halt ();
    try_with
      (fun () -> run_top ?use_ansi ?onechar_ops ?digit_vars ?ascii_symbols @@ fun () -> corun_top f)
      () { effc }

  (* After startup, the caller calls "next" with a callback to be executed inside the run_top handlers and return a value. *)
  let next (f : unit -> R.t) : R.t =
    continue (!cont <|> Anomaly "missing continuation in Pauseable.next") f
end
