open Core
open Reporter
open Notation
open Format
open Print
open Uuseg_string

(* A user notation pattern is a nonempty sequence of operator symbols and variable names.  There must be at least one operator symbol, and any two variable names must be separated by at least one symbol.  It is left-closed if the first element is an operator symbol and left-open if the first element is a variable, and similarly for right-open and -closed and the last element.  The two opennesses in turn determine whether it is infix, prefix, postfix, or outfix, but not its associativity or tightness.  *)

module Pattern = struct
  (* Each symbol or variable is stored along with the space following it. *)
  type var = string * space * Whitespace.t list
  type op = Token.t * space * Whitespace.t list

  (* This type ensures statically that all the invariants mentioned above must hold, and is parametrized by the left- and right-openness. *)
  type (_, _) t =
    | Op_nil : op -> (closed, closed) t
    (* If a pattern ends with a variable, that variable must be immediately preceded by an operator symbol, so we include that in the corresponding "nil". *)
    | Var_nil : op * var -> (closed, 's opn) t
    | Op : op * ('left, 'right) t -> (closed, 'right) t
    | Var : var * (closed, 'right) t -> ('s opn, 'right) t

  (* List the variable names used in a pattern. *)
  let rec vars : type left right. (left, right) t -> string list = function
    | Op_nil _ -> []
    | Var_nil (_, (x, _, _)) -> [ x ]
    | Op (_, pat) -> vars pat
    | Var ((x, _, _), pat) -> x :: vars pat

  (* A pattern parametrized only by its right-openness. *)
  type _ right_t = Right : ('left, 'right) t -> 'right right_t

  (* Cons a variable on the left of any pattern, raising an error if that would put two variables next to each other. *)
  let var : type left right s. var -> (left, right) t -> (s opn, right) t =
   fun v pat ->
    match pat with
    | Op_nil _ as pat -> Var (v, pat)
    | Var_nil _ as pat -> Var (v, pat)
    | Op (_, _) as pat -> Var (v, pat)
    | _ -> fatal (Invalid_notation_pattern "missing symbol between variables")
end

(* Print a user notation, using its pattern and its observation arguments. *)
let rec pp_user :
    type left tight right l r.
    (left, right) Pattern.t ->
    (left, tight, right) notation ->
    bool ->
    Format.formatter ->
    (l, r) Pattern.t ->
    observation list ->
    Whitespace.alist ->
    space ->
    unit =
 fun pattern n first ppf pat obs ws space ->
  match (pat, obs) with
  | Op ((op, br, _), pat), _ ->
      let wsop, ws = take op ws in
      pp_tok ppf op;
      pp_ws br ppf wsop;
      pp_user pattern n false ppf pat obs ws space
  | Op_nil (op, _, _), _ ->
      let wsop, ws = take op ws in
      pp_tok ppf op;
      pp_ws space ppf wsop;
      taken_last ws
  | Var_nil ((op, opbr, _), (_, varbr, _)), [ x ] -> (
      let wsop, ws = take op ws in
      pp_tok ppf op;
      pp_ws opbr ppf wsop;
      match x with
      | Term { value = Notn m; _ } when equal (notn m) n ->
          pp_user pattern n false ppf pattern (args m) (whitespace m) varbr
      | _ ->
          pp_term space ppf x;
          taken_last ws)
  | Var ((_, br, _), pat), x :: obs ->
      (match (first, x) with
      | true, Term { value = Notn m; _ } when equal (notn m) n ->
          pp_user pattern n true ppf pattern (args m) (whitespace m) br
      | _ -> pp_term br ppf x);
      pp_user pattern n false ppf pat obs ws space
  | Var_nil _, _ | Var _, [] -> fatal (Anomaly "invalid notation arguments")

(* Convert a user notation pattern to a notation tree.  Note that our highly structured definition of the type of patterns, that enforces invariants statically, means that this function CANNOT FAIL. *)
let tree :
    type left tight right.
    (left, tight, right) notation -> (left, right) Pattern.t -> (left, tight) notation_entry =
 fun notn pattern ->
  (* We have to handle the beginning specially, since the start and end of a notation tree are different depending on whether it is left-open or left-closed.  So we have an internal recursive function that handles everything except the first operator symbol. *)
  let rec go : type left l tight. (l, right) Pattern.t -> (tight, left) tree -> (tight, left) tree =
   fun pat n ->
    match pat with
    | Op_nil (tok, _, _) -> op tok n
    | Var_nil ((tok, _, _), _) -> op tok n
    | Op ((tok, _, _), pat) -> op tok (go pat n)
    | Var (_, Op ((tok, _, _), pat)) -> term tok (go pat n)
    | Var (_, Op_nil (tok, _, _)) -> term tok n
    | Var (_, Var_nil ((tok, _, _), _)) -> term tok n in
  match pattern with
  | Op_nil (tok, _, _) -> Closed_entry (eop tok (Done_closed notn))
  | Var (_, Op ((tok, _, _), pat)) -> Open_entry (eop tok (go pat (done_open notn)))
  | Var (_, Op_nil (tok, _, _)) -> Open_entry (eop tok (done_open notn))
  | Var (_, Var_nil ((tok, _, _), _)) -> Open_entry (eop tok (done_open notn))
  | Op ((tok, _, _), pat) -> Closed_entry (eop tok (go pat (Done_closed notn)))
  | Var_nil ((tok, _, _), _) -> Closed_entry (eop tok (Done_closed notn))

(* Print a *pattern* the way the user would enter it in a "notation" command, with quotes around the operator symbols. *)
let pp_pattern : type left right. formatter -> (left, right) Pattern.t -> unit =
 fun ppf pattern ->
  let rec go : type left right. (left, right) Pattern.t -> unit = function
    | Var ((x, _, ws), pat) ->
        pp_utf_8 ppf x;
        pp_ws `Break ppf ws;
        go pat
    | Var_nil ((op, _, opws), (x, _, varws)) ->
        pp_print_string ppf "\"";
        pp_tok ppf op;
        pp_print_string ppf "\"";
        pp_ws `Break ppf opws;
        pp_utf_8 ppf x;
        pp_ws `Break ppf varws
    | Op ((op, _, ws), pat) ->
        pp_print_string ppf "\"";
        pp_tok ppf op;
        pp_print_string ppf "\"";
        pp_ws `Break ppf ws;
        go pat
    | Op_nil (op, _, ws) ->
        pp_print_string ppf "\"";
        pp_tok ppf op;
        pp_print_string ppf "\"";
        pp_ws `Break ppf ws in
  pp_open_hvbox ppf 0;
  go pattern;
  pp_close_box ppf ()

(* A user "prenotation" includes all the information from a "notation" command, parsed and validated into a pattern, fixity, and so on, but not yet compiled into a notation tree. *)

type key = [ `Constant of Core.Constant.t | `Constr of Core.Constr.t * int ]

type prenotation =
  | User : {
      name : string;
      fixity : ('left, 'tight, 'right) fixity;
      (* The space tag on the last element is ignored. *)
      pattern : ('left, 'right) Pattern.t;
      key : key;
      val_vars : string list;
    }
      -> prenotation

(* Whereas a user "notation" has been compiled into a notation tree, but remembers the variables from the pattern and the definition, so as to implement the necessary permutation. *)

type notation = { key : key; notn : Notation.t; pat_vars : string list; val_vars : string list }

(* The actual function that compiles a prenotation into a notation is in user2.ml to avoid a circular dependency, since it uses Postprocess.  *)
