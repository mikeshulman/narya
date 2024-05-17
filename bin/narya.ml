open Bwd
open Util
open Core
open Parser
open Format
open React
open Lwt
open LTerm_text

let usage_msg = "narya [options] <file1> [<file2> ...]"
let input_files = ref Emp
let anon_arg filename = input_files := Snoc (!input_files, filename)
let reformat = ref false
let verbose = ref false
let compact = ref false
let unicode = ref true
let typecheck = ref true
let input_strings = ref Emp
let use_stdin = ref false
let interactive = ref false
let proofgeneral = ref false
let arity = ref 2
let refl_char = ref 'e'
let refl_strings = ref [ "refl"; "Id" ]
let internal = ref true

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
      Arg.String (fun str -> input_strings := Snoc (!input_strings, str)),
      "Execute a string, after all files loaded (also -e)" );
    ("-e", Arg.String (fun str -> input_strings := Snoc (!input_strings, str)), "");
    ("-verbose", Arg.Set verbose, "Show verbose messages (also -v)");
    ("-v", Arg.Set verbose, "");
    ("-no-check", Arg.Clear typecheck, "Don't typecheck and execute code (only parse it)");
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
    ( "-dtt",
      Unit
        (fun () ->
          arity := 1;
          refl_char := 'd';
          refl_strings := [];
          internal := false),
      "Abbreviation for -arity 1 -direction d -external" );
    ("--help", Arg.Unit (fun () -> ()), "");
    ("-", Arg.Set use_stdin, "");
  ]

let () =
  Arg.parse speclist anon_arg usage_msg;
  if
    Bwd.is_empty !input_files
    && (not !use_stdin)
    && Bwd.is_empty !input_strings
    && (not !interactive)
    && not !proofgeneral
  then (
    Printf.fprintf stderr "No input files specified\n";
    Arg.usage speclist usage_msg;
    exit 1)

module Terminal = Asai.Tty.Make (Core.Reporter.Code)

let rec batch first ws p src =
  let cmd = Command.Parse.final p in
  if cmd = Eof then if Galaxy.unsolved () then Reporter.fatal Open_holes else ws
  else (
    if !typecheck then Parser.Command.execute cmd;
    let ws =
      if !reformat then (
        let ws = if first then ws else Whitespace.ensure_starting_newlines 2 ws in
        Print.pp_ws `None std_formatter ws;
        Parser.Command.pp_command std_formatter cmd)
      else [] in
    let p, src = Command.Parse.restart_parse p src in
    batch false ws p src)

let execute (source : Asai.Range.source) =
  if !reformat then Format.open_vbox 0;
  let p, src = Command.Parse.start_parse source in
  let ws = batch true [] p src in
  if !reformat then (
    let ws = Whitespace.ensure_ending_newlines 2 ws in
    Print.pp_ws `None std_formatter ws;
    Format.close_box ())

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
        Reporter.try_with
          ~emit:(fun d -> Terminal.display ~output:stdout d)
          ~fatal:(fun d ->
            Terminal.display ~output:stdout d;
            match d.message with
            | Quit -> exit 0
            | _ -> ())
          (fun () ->
            match Command.parse_single str with
            | ws, None -> if !reformat then Print.pp_ws `None std_formatter ws
            | ws, Some cmd ->
                if !typecheck then Parser.Command.execute cmd;
                if !reformat then (
                  Print.pp_ws `None std_formatter ws;
                  let last = Parser.Command.pp_command std_formatter cmd in
                  Print.pp_ws `None std_formatter last;
                  Format.pp_print_newline std_formatter ()));
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

let rec interact_pg () =
  print_endline "[narya]";
  try
    let str = read_line () in
    Reporter.try_with
      ~emit:(fun d -> Terminal.display ~output:stdout d)
      ~fatal:(fun d -> Terminal.display ~output:stdout d)
      (fun () ->
        match Command.parse_single str with
        | ws, None -> if !reformat then Print.pp_ws `None std_formatter ws
        | ws, Some cmd ->
            if !typecheck then Parser.Command.execute cmd;
            if !reformat then (
              Print.pp_ws `None std_formatter ws;
              let last = Parser.Command.pp_command std_formatter cmd in
              Print.pp_ws `None std_formatter last));
    interact_pg ()
  with End_of_file -> ()

let () =
  Parser.Unparse.install ();
  Galaxy.run_empty @@ fun () ->
  Global.run_empty @@ fun () ->
  Scope.run @@ fun () ->
  Builtins.run @@ fun () ->
  Printconfig.run
    ~env:
      {
        style = (if !compact then `Compact else `Noncompact);
        state = `Case;
        chars = (if !unicode then `Unicode else `ASCII);
      }
  @@ fun () ->
  Reporter.run
    ~emit:(fun d ->
      if !verbose || d.severity = Error || d.severity = Warning then
        Terminal.display ~output:stderr d)
    ~fatal:(fun d ->
      Terminal.display ~output:stderr d;
      exit 1)
  @@ fun () ->
  Parser.Pi.install ();
  if !arity < 1 || !arity > 9 then Reporter.fatal (Unimplemented "arities outside [1,9]");
  Dim.Endpoints.set_len !arity;
  Dim.Endpoints.set_char !refl_char;
  Dim.Endpoints.set_names !refl_strings;
  Dim.Endpoints.set_internal !internal;
  (* TODO: If executing multiple files, they should be namespaced as sections.  (And eventually, using bantorra.) *)
  Mbwd.miter (fun [ filename ] -> execute (`File filename)) [ !input_files ];
  (if !use_stdin then
     let content = In_channel.input_all stdin in
     execute (`String { content; title = Some "stdin" }));
  Mbwd.miter
    (fun [ content ] -> execute (`String { content; title = Some "command-line exec string" }))
    [ !input_strings ];
  if !interactive then Lwt_main.run (interact ()) else if !proofgeneral then interact_pg ()
