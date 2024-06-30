open Bwd
open Util
open Core
open Parser
open Format
open React
open Lwt
open LTerm_text

let usage_msg = "narya [options] <file1> [<file2> ...]"
let inputs = ref Emp
let anon_arg filename = inputs := Snoc (!inputs, `File filename)
let reformat = ref false
let verbose = ref false
let compact = ref false
let unicode = ref true
let execute = ref true
let interactive = ref false
let proofgeneral = ref false
let arity = ref 2
let refl_char = ref 'e'
let refl_strings = ref [ "refl"; "Id" ]
let internal = ref true
let discreteness = ref false
let source_only = ref false
let fake_interacts = ref Emp

let set_refls str =
  match String.split_on_char ',' str with
  | [] -> raise (Failure "Empty direction names")
  | c :: _ when String.length c <> 1 || c.[0] < 'a' || c.[0] > 'z' ->
      raise (Failure "Direction name must be a single lowercase letter")
  | c :: names ->
      refl_char := c.[0];
      refl_strings := names

let speclist =
  [
    ("-interactive", Arg.Set interactive, "Enter interactive mode (also -i)");
    ("-i", Arg.Set interactive, "");
    ("-proofgeneral", Arg.Set proofgeneral, "Enter proof general interaction mode");
    ( "-exec",
      Arg.String (fun str -> inputs := Snoc (!inputs, `String str)),
      "Execute a string, after all files loaded (also -e)" );
    ("-e", Arg.String (fun str -> inputs := Snoc (!inputs, `String str)), "");
    ("-verbose", Arg.Set verbose, "Show verbose messages (also -v)");
    ("-v", Arg.Set verbose, "");
    ("-no-check", Arg.Clear execute, "Don't typecheck and execute code (only parse it)");
    ("-reformat", Arg.Set reformat, "Display reformatted code on stdout");
    ("-noncompact", Arg.Clear compact, "Reformat code noncompactly (default)");
    ("-compact", Arg.Set compact, "Reformat code compactly");
    ("-unicode", Arg.Set unicode, "Display and reformat code using Unicode for built-ins (default)");
    ("-ascii", Arg.Clear unicode, "Display and reformat code using ASCII for built-ins");
    ("-arity", Arg.Set_int arity, "Arity of parametricity (default = 2)");
    ( "-direction",
      Arg.String set_refls,
      "Names for parametricity direction and reflexivity (default = e,refl,Id)" );
    ("-internal", Arg.Set internal, "Set parametricity to internal (default)");
    ("-external", Arg.Clear internal, "Set parametricity to external");
    ("-discreteness", Arg.Set discreteness, "Enable discreteness");
    ("-source-only", Arg.Set source_only, "Load all files from source (ignore compiled versions)");
    ( "-dtt",
      Unit
        (fun () ->
          arity := 1;
          refl_char := 'd';
          refl_strings := [];
          internal := false),
      "Abbreviation for -arity 1 -direction d -external" );
    ("--help", Arg.Unit (fun () -> ()), "");
    ("-", Arg.Unit (fun () -> inputs := Snoc (!inputs, `Stdin)), "");
    ("-fake-interact", Arg.String (fun str -> fake_interacts := Snoc (!fake_interacts, str)), "");
  ]

let () =
  Arg.parse speclist anon_arg usage_msg;
  if
    Bwd.is_empty !inputs
    && (not !interactive)
    && (not !proofgeneral)
    && Bwd.is_empty !fake_interacts
  then (
    Printf.fprintf stderr "No input files specified\n";
    Arg.usage speclist usage_msg;
    exit 1)

module Terminal = Asai.Tty.Make (Core.Reporter.Code)

let ( let* ) f o = Lwt.bind f o

class read_line terminal history prompt =
  object (self)
    inherit LTerm_read_line.read_line ~history ()
    inherit [Zed_string.t] LTerm_read_line.term terminal
    method! show_box = false
    initializer self#set_prompt (S.const (eval [ B_underline true; S prompt; B_underline false ]))
  end

let rec repl terminal history buf =
  let buf, prompt =
    match buf with
    | Some buf -> (buf, "")
    | None -> (Buffer.create 70, "narya\n") in
  let* command =
    Lwt.catch
      (fun () ->
        let rl = new read_line terminal (LTerm_history.contents history) prompt in
        rl#run >|= fun command -> Some command)
      (function
        | Sys.Break -> return None
        | exn -> Lwt.fail exn) in
  match command with
  | Some command ->
      let str = Zed_string.to_utf8 command in
      if str = "" then (
        let str = Buffer.contents buf in
        let* () = Lwt_io.flush Lwt_io.stdout in
        (* In interactive mode, we display all messages verbosely, and don't quit on fatal errors except for the Quit command. *)
        Reporter.try_with
          ~emit:(fun d -> Terminal.display ~output:stdout d)
          ~fatal:(fun d ->
            Terminal.display ~output:stdout d;
            match d.message with
            | Quit _ -> exit 0
            | _ -> ())
          (fun () ->
            match Command.parse_single str with
            | ws, None -> Execute.reformat_maybe @@ fun ppf -> Print.pp_ws `None ppf ws
            | ws, Some cmd ->
                if !execute then Execute.execute_command cmd;
                Execute.reformat_maybe @@ fun ppf ->
                Print.pp_ws `None ppf ws;
                let last = Parser.Command.pp_command ppf cmd in
                Print.pp_ws `None ppf last;
                Format.pp_print_newline ppf ());
        LTerm_history.add history (Zed_string.of_utf8 (String.trim str));
        repl terminal history None)
      else (
        Buffer.add_string buf str;
        Buffer.add_char buf '\n';
        repl terminal history (Some buf))
  | None -> repl terminal history None

let history_file = Unix.getenv "HOME" ^ "/.narya_history"

let interact () =
  let* () = LTerm_inputrc.load () in
  let history = LTerm_history.create [] in
  let* () = LTerm_history.load history history_file in
  Lwt.catch
    (fun () ->
      let* terminal = Lazy.force LTerm.stdout in
      repl terminal history None)
    (function
      | LTerm_read_line.Interrupt ->
          let* () = LTerm_history.save history history_file in
          Lwt.return ()
      | exn ->
          let* () = LTerm_history.save history history_file in
          Lwt.fail exn)

let rec interact_pg () : unit =
  print_endline "[narya]";
  try
    let str = read_line () in
    Reporter.try_with
      ~emit:(fun d -> Terminal.display ~output:stdout d)
      ~fatal:(fun d -> Terminal.display ~output:stdout d)
      (fun () ->
        match Command.parse_single str with
        | ws, None -> Execute.reformat_maybe @@ fun ppf -> Print.pp_ws `None ppf ws
        | ws, Some cmd ->
            if !execute then Execute.execute_command cmd;
            Execute.reformat_maybe @@ fun ppf ->
            Print.pp_ws `None ppf ws;
            let last = Parser.Command.pp_command ppf cmd in
            Print.pp_ws `None ppf last);
    interact_pg ()
  with End_of_file -> ()

let fake_interact file =
  let p, src = Parser.Command.Parse.start_parse (`File file) in
  Reporter.try_with
    ~emit:(fun d -> Terminal.display ~output:stdout d)
    ~fatal:(fun d -> Terminal.display ~output:stdout d)
    (fun () -> Execute.batch true [] p src)

let marshal_flags chan =
  Marshal.to_channel chan !arity [];
  Marshal.to_channel chan !refl_char [];
  Marshal.to_channel chan !refl_strings [];
  Marshal.to_channel chan !internal [];
  Marshal.to_channel chan !discreteness []

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

let () =
  Parser.Unparse.install ();
  Parser.Scope.Mod.run @@ fun () ->
  History.run_empty @@ fun () ->
  Printconfig.run
    ~env:
      {
        style = (if !compact then `Compact else `Noncompact);
        state = `Case;
        chars = (if !unicode then `Unicode else `ASCII);
      }
  @@ fun () ->
  Readback.Display.run ~env:false @@ fun () ->
  Core.Syntax.Discreteness.run ~env:!discreteness @@ fun () ->
  Reporter.run
    ~emit:(fun d ->
      if !verbose || d.severity = Error || d.severity = Warning then
        Terminal.display ~output:stderr d)
    ~fatal:(fun d ->
      Terminal.display ~output:stderr d;
      exit 1)
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
        reformatter = (if !reformat then Some std_formatter else None);
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
  Core.Command.Mode.run ~env:{ interactive = true } @@ fun () ->
  Mbwd.miter (fun [ file ] -> fake_interact file) [ !fake_interacts ];
  if !interactive then Lwt_main.run (interact ()) else if !proofgeneral then interact_pg ()
