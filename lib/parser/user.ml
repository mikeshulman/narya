open Core
open Reporter
open Notation
open Format
open Print
open Uuseg_string

type pattern =
  [ `Op of Token.t * space * Whitespace.t list
  | `Var of string * space * Whitespace.t list
  | `Ellipsis of Whitespace.t list ]
  list

let tree :
    type left tight right.
    (left, tight, right) fixity ->
    (left, tight, right) notation ->
    pattern ->
    (left, tight) notation_entry =
 fun fixity notn pattern ->
  let left, _, _ = fixprops fixity in
  let rec user_tree pattern n =
    match (pattern, left) with
    | [], Closed -> n
    | [], Open _ -> fatal (Anomaly "pattern doesn't match deduced fixity")
    | [ `Var _ ], Open _ -> n
    | [ `Var _ ], Closed -> fatal (Anomaly "pattern doesn't match deduced fixity")
    | `Op (tok, _, _) :: pat_vars, _ -> op tok (user_tree pat_vars n)
    | `Var _ :: `Op (tok, _, _) :: pat_vars, _ -> term tok (user_tree pat_vars n)
    | `Var _ :: `Var _ :: _, _ -> fatal Missing_notation_symbol
    | `Var _ :: `Ellipsis _ :: _, _ -> fatal (Unimplemented "internal ellipses in notation")
    | `Ellipsis _ :: _, _ -> fatal (Unimplemented "internal ellipses in notation") in
  match (pattern, left) with
  | [], _ -> fatal (Anomaly "empty pattern")
  | `Op (tok, _, _) :: pat_vars, Closed ->
      Closed_entry (eop tok (user_tree pat_vars (Done_closed notn)))
  | `Var _ :: `Op (tok, _, _) :: pat_vars, Open _ ->
      Open_entry (eop tok (user_tree pat_vars (done_open notn)))
  | `Var _ :: _, Closed | `Op _ :: _, Open _ ->
      fatal (Anomaly "pattern doesn't match deduced fixity")
  | `Var _ :: `Ellipsis _ :: _, _ | `Ellipsis _ :: _, _ ->
      fatal (Unimplemented "internal ellipses in notation")
  | `Var _ :: `Var _ :: _, _ -> fatal Missing_notation_symbol
  | [ `Var _ ], _ -> fatal Zero_notation_symbols

let pp_pattern : formatter -> pattern -> unit =
 fun ppf pattern ->
  pp_open_hvbox ppf 0;
  List.iter
    (function
      | `Var (x, _, ws) ->
          pp_utf_8 ppf x;
          pp_ws `Break ppf ws
      | `Op (op, _, ws) ->
          pp_print_string ppf "\"";
          pp_tok ppf op;
          pp_print_string ppf "\"";
          pp_ws `Break ppf ws
      | `Ellipsis ws ->
          pp_tok ppf Ellipsis;
          pp_ws `Break ppf ws)
    pattern;
  pp_close_box ppf ()

type key = [ `Constant of Core.Constant.t | `Constr of Core.Constr.t * int ]

type prenotation =
  | User : {
      name : string;
      fixity : ('left, 'tight, 'right) fixity;
      (* The space tag on the last element is ignored. *)
      pattern : pattern;
      key : key;
      val_vars : string list;
    }
      -> prenotation

type notation = { key : key; notn : Notation.t; pat_vars : string list; val_vars : string list }
