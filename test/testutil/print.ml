open Format
open Parser
open Print
open Core

let margin = ref 80
let set_margin n = margin := n

let reformat content =
  let tr = Parse.term (`String { title = Some "user-supplied term"; content }) in
  pp_set_margin std_formatter !margin;
  pp_set_max_indent std_formatter (max (!margin - 12) (!margin / 2));
  pp_open_hovbox std_formatter 0;
  pp_term std_formatter tr;
  pp_close_box std_formatter ();
  pp_print_newline std_formatter ();
  pp_print_newline std_formatter ()

module Terminal = Asai.Tty.Make (Core.Reporter.Code)

let run f =
  Reporter.run ~emit:Terminal.display ~fatal:(fun d ->
      Terminal.display d;
      raise (Failure "Fatal error"))
  @@ fun () ->
  Scope.run @@ fun () -> Builtins.run f
