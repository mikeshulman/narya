open Core
open Reporter
open Notation

(* User notations *)

type pattern =
  [ `Op of Token.t * space * Whitespace.t list
  | `Var of string * space * Whitespace.t list
  | `Ellipsis of Whitespace.t list ]
  list

let user_tree :
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

type user_notation =
  | User : {
      name : string;
      fixity : ('left, 'tight, 'right) fixity;
      (* The space tag on the last element is ignored. *)
      pattern : pattern;
      key : printkey;
      val_vars : string list;
    }
      -> user_notation
