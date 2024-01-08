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

let speclist =
  [
    ("-interactive", Arg.Set interactive, "Enter interactive mode (also -i)");
    ("-i", Arg.Set interactive, "");
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
    ("-unicode", Arg.Set unicode, "Reformat code using Unicode (default)");
    ( "-ascii",
      Arg.Clear unicode,
      "Reformat code using ASCII for built-ins (user-defined constants are unaffected)" );
    ("--help", Arg.Unit (fun () -> ()), "");
    ("-", Arg.Set use_stdin, "");
  ]

let () =
  Arg.parse speclist anon_arg usage_msg;
  if
    Bwd.is_empty !input_files && (not !use_stdin) && Bwd.is_empty !input_strings && not !interactive
  then (
    Printf.fprintf stderr "No input files specified\n";
    Arg.usage speclist usage_msg;
    exit 1)

module Terminal = Asai.Tty.Make (Core.Reporter.Code)

let rec batch first p src =
  let cmd = Parse.Command.final p in
  if cmd <> Eof then (
    if !typecheck then Parser.Command.execute cmd;
    if !reformat then (
      if not first then Format.print_cut ();
      Parser.Command.pp_command std_formatter cmd;
      Format.print_cut ());
    if not (Parse.Command.has_consumed_end p) then
      let p, src = Parse.Command.parse (`Restart (p, src)) in
      batch false p src)

let execute source =
  if !reformat then Format.open_vbox 0;
  let p, src = Parse.Command.parse (`New (`Partial, source)) in
  batch true p src;
  if !reformat then Format.close_box ()

let ( let* ) f o = Lwt.bind f o

class read_line terminal history prompt =
  object (self)
    inherit LTerm_read_line.read_line ~history ()
    inherit [Zed_string.t] LTerm_read_line.term terminal
    method! show_box = false
    initializer self#set_prompt (S.const (eval [ S prompt ]))
  end

let rec repl terminal history buf =
  let buf, prompt =
    match buf with
    | Some buf -> (buf, "  ...: ")
    | None -> (Buffer.create 70, "narya: ") in
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
        let content = Buffer.contents buf in
        let* () = Lwt_io.flush Lwt_io.stdout in
        Reporter.try_with
          ~emit:(fun d -> Terminal.display ~output:stdout d)
          ~fatal:(fun d -> Terminal.display ~output:stdout d)
          (fun () -> execute (`String { content; title = Some "interactive input" }));
        LTerm_history.add history (Zed_string.of_utf8 content);
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

let () =
  Reporter.run
    ~emit:(fun d -> if !verbose then Terminal.display ~output:stderr d)
    ~fatal:(fun d ->
      Terminal.display ~output:stderr d;
      raise (Failure "Fatal error"))
  @@ fun () ->
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
  Types.Nat.install ();
  Types.Sigma.install ();
  Types.Empty.install ();
  Types.Sum.install ();
  Types.Lst.install ();
  Types.Stream.install ();
  Types.Unit.install ();
  Types.Vec.install ();
  Types.Gel.install ();
  (* TODO: If executing multiple files, they should be namespaced as sections.  (And eventually, using bantorra.) *)
  Mbwd.miter (fun [ filename ] -> execute (`File filename)) [ !input_files ];
  (if !use_stdin then
     let content = In_channel.input_all stdin in
     execute (`String { content; title = Some "stdin" }));
  Mbwd.miter
    (fun [ content ] -> execute (`String { content; title = Some "command-line exec string" }))
    [ !input_strings ];
  if !interactive then Lwt_main.run (interact ())
