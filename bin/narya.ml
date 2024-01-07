open Bwd
open Util
open Core
open Parser
open Format

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

let speclist =
  [
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
  if Bwd.is_empty !input_files && (not !use_stdin) && Bwd.is_empty !input_strings then (
    Printf.fprintf stderr "No input files specified\n";
    Arg.usage speclist usage_msg;
    exit 1)

module Terminal = Asai.Tty.Make (Core.Reporter.Code)

let rec repl first p src =
  let cmd = Parse.Command.final p in
  if !typecheck then Parser.Command.execute cmd;
  if !reformat then (
    if not first then Format.print_cut ();
    Parser.Command.pp_command std_formatter cmd;
    Format.print_cut ());
  if not (Parse.Command.has_consumed_end p) then
    (* TODO: Once the notation state is changeable, carry it through. *)
    let p, src = Parse.Command.parse (`Restart (p, src)) in
    repl false p src

let execute source =
  if !reformat then Format.open_vbox 0;
  let p, src = Parse.Command.parse (`New (`Partial, source)) in
  repl true p src;
  if !reformat then Format.close_box ()

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
  (* TODO: If executing multiple files, they should be namespaced as sections.  (And eventually, using bantorra.) *)
  Mbwd.miter (fun [ filename ] -> execute (`File filename)) [ !input_files ];
  (if !use_stdin then
     let content = In_channel.input_all stdin in
     execute (`String { content; title = Some "stdin" }));
  Mbwd.miter
    (fun [ content ] -> execute (`String { content; title = Some "command-line exec string" }))
    [ !input_strings ]
