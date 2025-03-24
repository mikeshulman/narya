open Core
open Reporter
open Notation
open PPrint
open Print

(* A user notation pattern is a nonempty sequence of operator symbols and variable names.  There must be at least one operator symbol, and any two variable names must be separated by at least one symbol.  It is left-closed if the first element is an operator symbol and left-open if the first element is a variable, and similarly for right-open and -closed and the last element.  The two opennesses in turn determine whether it is infix, prefix, postfix, or outfix, but not its associativity or tightness.  *)

module Pattern = struct
  (* This type ensures statically that all the invariants mentioned above must hold, and is parametrized by the left- and right-openness.
     Each symbol or variable is stored along with the type of space following it, except for those that occur last. *)
  type (_, _) t =
    | Op_nil : Token.t * Whitespace.t list -> (closed, closed) t
    (* If a pattern ends with a variable, that variable must be immediately preceded by an operator symbol, so we include that in the corresponding "nil". *)
    | Var_nil :
        (Token.t * space * Whitespace.t list) * (string * Whitespace.t list)
        -> (closed, 's opn) t
    | Op : (Token.t * space * Whitespace.t list) * ('left, 'right) t -> (closed, 'right) t
    | Var : (string * space * Whitespace.t list) * (closed, 'right) t -> ('s opn, 'right) t

  (* List the variable names used in a pattern. *)
  let rec vars : type left right. (left, right) t -> string list = function
    | Op_nil _ -> []
    | Var_nil (_, (x, _)) -> [ x ]
    | Op (_, pat) -> vars pat
    | Var ((x, _, _), pat) -> x :: vars pat

  let inner_symbols : type left right.
      (left, right) t ->
      [ `Single of Token.t | `Multiple of Token.t * Token.t option list * Token.t ] =
   fun pat ->
    let rec go : type left right. (left, right) t -> Token.t option list * Token.t = function
      | Op_nil (tok, _) -> ([], tok)
      | Var_nil ((tok, _, _), _) -> ([], tok)
      | Op ((tok, _, _), pat) ->
          let inner, last = go pat in
          (Some tok :: inner, last)
      | Var (_, pat) ->
          let inner, last = go pat in
          (None :: inner, last) in
    match go pat with
    | Some first :: inner, last -> `Multiple (first, inner, last)
    | None :: Some first :: inner, last -> `Multiple (first, inner, last)
    | None :: None :: _, _ -> fatal (Anomaly "two sequential variables in inner_symbols")
    | [ None ], tok | [], tok -> `Single tok

  (* A pattern parametrized only by its right-openness. *)
  type _ right_t = Right : ('left, 'right) t -> 'right right_t

  (* Cons a variable on the left of any pattern, raising an error if that would put two variables next to each other. *)
  let var : type left right s.
      string * space * Whitespace.t list -> (left, right) t -> (s opn, right) t =
   fun v pat ->
    match pat with
    | Op_nil _ as pat -> Var (v, pat)
    | Var_nil _ as pat -> Var (v, pat)
    | Op (_, _) as pat -> Var (v, pat)
    | _ -> fatal (Invalid_notation_pattern "missing symbol between variables")
end

(* Print a *pattern* the way the user would enter it in a "notation" command, with quotes around the operator symbols. *)
let pp_pattern : type left right. (left, right) Pattern.t -> document * Whitespace.t list =
 fun pattern ->
  let rec go : type left right.
      (left, right) Pattern.t -> Whitespace.t list option -> document * Whitespace.t list =
   fun pattern prews ->
    match pattern with
    | Var ((x, _, ws), pat) ->
        let ppat, wpat = go pat (Some ws) in
        (group (optional (pp_ws `Break) prews ^^ utf8string x) ^^ ppat, wpat)
    | Var_nil ((op, _, opws), (x, varws)) ->
        ( group (optional (pp_ws `Break) prews ^^ dquotes (Token.pp op))
          ^^ group (pp_ws `Break opws ^^ utf8string x),
          varws )
    | Op ((op, _, ws), pat) ->
        let ppat, wpat = go pat (Some ws) in
        (group (optional (pp_ws `Break) prews ^^ dquotes (Token.pp op)) ^^ ppat, wpat)
    | Op_nil (op, ws) -> (group (optional (pp_ws `Break) prews ^^ dquotes (Token.pp op)), ws) in
  go pattern None

(* A user "prenotation" includes all the information from a "notation" command, parsed and validated into a pattern, fixity, and so on, but not yet compiled into a notation tree. *)

type key = [ `Constant of Core.Constant.t | `Constr of Core.Constr.t * int ]

type ('left, 'tight, 'right) prenotation_data = {
  name : string;
  fixity : ('left, 'tight, 'right) fixity;
  pattern : ('left, 'right) Pattern.t;
  key : key;
  val_vars : string list;
}

type prenotation = User : ('left, 'tight, 'right) prenotation_data -> prenotation

(* Whereas a user "notation" has been compiled into a notation tree, but remembers the variables from the pattern and the definition, so as to implement the necessary permutation. *)

type notation = {
  key : key;
  notn : Notation.t;
  pat_vars : string list;
  val_vars : string list;
  inner_symbols : [ `Single of Token.t | `Multiple of Token.t * Token.t option list * Token.t ];
}

(* The actual function that compiles a prenotation into a notation is in user2.ml to avoid a circular dependency, since it uses Postprocess.  *)
