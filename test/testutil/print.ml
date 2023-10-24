open Format
open Parser
open Print

let margin = ref 80
let set_margin n = margin := n

let reformat str =
  let tr = Parse.term !Builtins.builtins str in
  pp_set_margin std_formatter !margin;
  pp_set_max_indent std_formatter (max (!margin - 12) (!margin / 2));
  pp_open_hovbox std_formatter 0;
  pp_case std_formatter tr;
  pp_close_box std_formatter ();
  pp_print_newline std_formatter ();
  pp_print_newline std_formatter ()
