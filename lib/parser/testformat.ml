(* This file provides dummy stubs to replace the formatting functions from Format that instead save a description of the commands issued to a buffer.  This can be helpful when debugging to see what sequence of formatting instructions are actually issued by a complicated arrangement of recursive formatting functions.

   To use it, open it instead of Format and Uuseg_string in the files print.ml, builtins.ml, and token.ml (and perhaps others).  Then run 'init' first, followed by the function that would ordinarily format something, then 'result' to get the desired description.

   Note that this trick does not work with pretty-printing using format strings, a.k.a. 'fprintf' and friends.  For that reason (among others), we currently avoid those entirely, using pretty-printing combinators directly. *)

(* include Format
   include Uuseg_string *)

type formatter = Format.formatter

let buf = ref (Buffer.create 0)
let sppf = ref Format.std_formatter

let init () =
  buf := Buffer.create 30;
  sppf := Format.formatter_of_buffer !buf;
  Format.pp_open_vbox !sppf 0

let result () =
  Format.pp_close_box !sppf ();
  Format.pp_print_newline !sppf ();
  Buffer.contents !buf

let boxes = ref 0
let pp_print_string _ppf str = Format.fprintf !sppf "string: \"%s\"@," str
let pp_print_char _ppf c = Format.fprintf !sppf "char: \'%c\'@," c
let pp_utf_8 _ppf str = Format.fprintf !sppf "utf8: \"%a\"@," Uuseg_string.pp_utf_8 str

let pp_open_box _ppf n =
  Format.fprintf !sppf "(open_box %dth: %d@," !boxes n;
  boxes := !boxes + 1

let pp_open_vbox _ppf n =
  Format.fprintf !sppf "(open_vbox %dth: %d@," !boxes n;
  boxes := !boxes + 1

let pp_open_hbox _ppf () =
  Format.fprintf !sppf "(open_hbox %dth@," !boxes;
  boxes := !boxes + 1

let pp_open_hvbox _ppf n =
  Format.fprintf !sppf "(open_hvbox %dth: %d@," !boxes n;
  boxes := !boxes + 1

let pp_open_hovbox _ppf n =
  Format.fprintf !sppf "(open_hovbox %dth: %d@," !boxes n;
  boxes := !boxes + 1

let pp_close_box _ppf () =
  boxes := !boxes - 1;
  Format.fprintf !sppf "close_box %dth)@," !boxes

let pp_print_space _ppf () = Format.fprintf !sppf "space@,"
let pp_print_cut _ppf () = Format.fprintf !sppf "cut@,"
let pp_print_break _ppf a b = Format.fprintf !sppf "break: %d %d@," a b

let pp_print_custom_break _ppf ~fits:(s1, n, s2) ~breaks:(s3, m, s4) =
  Format.fprintf !sppf "custom_break: (\"%s\",%d,\"%s\") (\"%s\",%d,\"%s\")@," s1 n s2 s3 m s4

let pp_force_newline _ppf () = Format.fprintf !sppf "force_newline@,"

(* Copied from format *)
let pp_print_iter ?(pp_sep = pp_print_cut) iter pp_v ppf v =
  let is_first = ref true in
  let pp_v v =
    if !is_first then is_first := false else pp_sep ppf ();
    pp_v ppf v in
  iter pp_v v

let pp_print_list ?(pp_sep = pp_print_cut) pp_v ppf v = pp_print_iter ~pp_sep List.iter pp_v ppf v
let pp_print_array ?(pp_sep = pp_print_cut) pp_v ppf v = pp_print_iter ~pp_sep Array.iter pp_v ppf v
let pp_print_seq ?(pp_sep = pp_print_cut) pp_v ppf seq = pp_print_iter ~pp_sep Seq.iter pp_v ppf seq

let pp_print_option ?(none = fun _ () -> ()) pp_v ppf = function
  | None -> none ppf ()
  | Some v -> pp_v ppf v

let pp_print_result ~ok ~error ppf = function
  | Ok v -> ok ppf v
  | Error e -> error ppf e

let pp_print_either ~left ~right ppf = function
  | Either.Left l -> left ppf l
  | Either.Right r -> right ppf r
