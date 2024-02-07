open Core
open Format
open Uuseg_string
open Reporter
open Notation
open Printconfig

(* Given an alist of lists, if it's not empty enforce that the first element has an expected key and return its value and the rest of the alist, or if it is empty return an empty list and an empty alist.  In other words, treat an alist as an infinite stream that's filled out with empty lists at the end.  This is used for destructing 'Whitespace.alist's because the parse trees produced by parsing have actual data there, while those produced by unparsing have nothing. *)
let take (tok : Token.t) (ws : Whitespace.alist) =
  match ws with
  | [] -> ([], [])
  | (t, x) :: xs ->
      if tok = t then (x, xs)
      else
        fatal
          (Anomaly
             (Printf.sprintf "unexpectedly labeled whitespace/comments: expected %s got %s"
                (Token.to_string tok) (Token.to_string t)))

let take_opt (tok : Token.t) (ws : Whitespace.alist) =
  match ws with
  | [] -> Some ([], [])
  | (t, x) :: xs -> if tok = t then Some (x, xs) else None

let must_start_with (tok : Token.t) (ws : Whitespace.alist) =
  match ws with
  | (t, _) :: _ when t = tok -> ws
  | _ -> (tok, []) :: ws

(* Ensure that we took all the elements. *)
let taken_last (ws : Whitespace.alist) =
  match ws with
  | [] -> ()
  | (tok, _) :: _ ->
      fatal (Anomaly ("unexpected whitespace/comments: token label " ^ Token.to_string tok))

(* Print a token, with arguments swapped so that it takes the token as an argument. *)
let pp_tok (ppf : formatter) (tok : Token.t) : unit = Token.pp tok ppf ()

(* Print a variable, with underscore for unnamed variables. *)
let pp_var : formatter -> string option -> unit =
 fun ppf x ->
  match x with
  | Some x -> pp_utf_8 ppf x
  | None -> Token.pp Underscore ppf ()

(* Print constructors and fields *)
let pp_constr (ppf : formatter) (c : string) : unit =
  pp_utf_8 ppf c;
  pp_print_char ppf '.'

let pp_field (ppf : formatter) (c : string) : unit =
  pp_print_char ppf '.';
  pp_utf_8 ppf c

let pp_space ppf space =
  match space with
  | `None -> ()
  | `Break -> pp_print_space ppf ()
  | `Nobreak -> pp_print_char ppf ' '
  | `Custom (fits, breaks) -> pp_print_custom_break ppf ~fits ~breaks

(* Print the comments and newlines following a token. *)
(* TODO: If this is called as the last thing in a box, then the forced newlines should come *after* the box closes, otherwise they produce undesired indentation on the next line.  I don't know how to deal with that; maybe override the pretty-printing functions with wrappers that store newlines in a buffer until they see whether the next event is a close_box? *)
let pp_ws (space : space) (ppf : formatter) (ws : Whitespace.t list) : unit =
  let pp_newlines ppf n =
    for _ = 1 to n do
      pp_force_newline ppf ()
    done in
  let rec pp (ppf : formatter) (ws : Whitespace.t list) : unit =
    match ws with
    | [] -> fatal (Anomaly "empty list in pp_ws")
    | [ `Newlines n ] ->
        pp_close_box ppf ();
        pp_newlines ppf n
    | [ `Line str ] ->
        pp_print_char ppf '`';
        pp_print_string ppf str;
        pp_close_box ppf ();
        pp_force_newline ppf ()
    | [ `Block str ] ->
        pp_print_string ppf "{`";
        pp_print_string ppf str;
        pp_print_string ppf "`}";
        pp_close_box ppf ();
        pp_force_newline ppf ()
    | `Newlines n :: ws ->
        for _ = 1 to n do
          pp_print_cut ppf ()
        done;
        pp ppf ws
    | `Line str :: ws ->
        pp_print_char ppf '`';
        pp_print_string ppf str;
        pp_print_cut ppf ();
        pp ppf ws
    | `Block str :: (`Line _ :: _ as ws) | `Block str :: (`Block _ :: _ as ws) ->
        pp_print_string ppf "{`";
        pp_print_string ppf str;
        pp_print_string ppf "`}";
        pp_print_space ppf ();
        pp ppf ws
    | `Block str :: (`Newlines _ :: _ as ws) ->
        pp_print_string ppf "{`";
        pp_print_string ppf str;
        pp_print_string ppf "`}";
        pp ppf ws in
  match ws with
  | [] -> pp_space ppf space
  | [ `Newlines n ] -> if n >= 2 then pp_newlines ppf n else pp_space ppf space
  | `Newlines n :: ws ->
      pp_newlines ppf n;
      pp_open_vbox ppf 0;
      pp ppf ws
  | _ ->
      pp_print_string ppf " ";
      pp_open_vbox ppf 0;
      pp ppf ws

(* Print a parse tree. *)
let rec pp_term (space : space) (ppf : formatter) (wtr : observation) : unit =
  let (Term tr) = wtr in
  match state () with
  | `Case -> (
      match tr.value with
      | Notn n -> pp_notn_case space ppf (notn n) (args n) (whitespace n)
      | _ -> as_term @@ fun () -> pp_term space ppf wtr)
  | `Term -> (
      match tr.value with
      | Notn n -> pp_notn space ppf (notn n) (args n) (whitespace n)
      | App _ ->
          pp_open_hovbox ppf 2;
          pp_spine `None ppf wtr;
          pp_close_box ppf ();
          pp_space ppf space
      | Placeholder w ->
          pp_tok ppf Underscore;
          pp_ws space ppf w
      | Ident (x, w) ->
          pp_utf_8 ppf (String.concat "." x);
          pp_ws space ppf w
      | Constr (c, w) ->
          pp_constr ppf c;
          pp_ws space ppf w
      | Field (f, w) ->
          pp_field ppf f;
          pp_ws space ppf w
      | Superscript (Some x, s, w) ->
          pp_term `None ppf (Term x);
          pp_utf_8 ppf (Token.to_super s);
          pp_ws space ppf w
      | Superscript (None, s, w) ->
          pp_utf_8 ppf (Token.to_super s);
          pp_ws space ppf w)

and pp_notn_case :
    type left tight right.
    space ->
    formatter ->
    (left, tight, right) notation ->
    observation list ->
    Whitespace.alist ->
    unit =
 fun space ppf n obs ws ->
  match print_as_case n with
  | Some pp -> pp space ppf obs ws
  | None -> as_term @@ fun () -> pp_notn space ppf n obs ws

and pp_notn :
    type left tight right.
    space ->
    formatter ->
    (left, tight, right) notation ->
    observation list ->
    Whitespace.alist ->
    unit =
 fun space ppf n obs ws ->
  match print n with
  | Some pp -> pp space ppf obs ws
  | None -> fatal (Anomaly (Printf.sprintf "unprintable notation: %s" (name n)))

and pp_spine (space : space) (ppf : formatter) (tr : observation) : unit =
  match tr with
  | Term { value = App { fn; arg; _ }; _ } ->
      pp_spine `Break ppf (Term fn);
      pp_term space ppf (Term arg)
  | _ -> pp_term space ppf tr
