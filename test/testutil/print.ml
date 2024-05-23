open Format
open Parser
open Print
open Core

let () =
  Dim.Endpoints.set_len 2;
  Dim.Endpoints.set_internal true

let margin = ref 80
let set_margin n = margin := n

let reformat content =
  let p = Parse.Term.parse (`String { content; title = Some "user-supplied term" }) in
  let tr = Parse.Term.final p in
  pp_set_geometry std_formatter ~margin:!margin ~max_indent:(max (!margin - 12) (!margin / 2));
  pp_open_hovbox std_formatter 0;
  pp_term `None std_formatter tr;
  pp_close_box std_formatter ();
  pp_print_newline std_formatter ();
  pp_print_newline std_formatter ()

module Terminal = Asai.Tty.Make (Core.Reporter.Code)

let run f =
  Reporter.run ~emit:Terminal.display ~fatal:(fun d ->
      Terminal.display d;
      raise (Failure "Fatal error"))
  @@ fun () ->
  Builtins.run @@ fun () ->
  Global.run_empty @@ fun () -> Scope.run f
