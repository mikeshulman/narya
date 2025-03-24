open Util
open Parser
open Notation
open Parseonly

(* Notations for arithmetic.  This has nothing to do with the Nat of type theory, it's just a way of testing the parser. *)

type (_, _, _) identity +=
  | Plus : (No.nonstrict opn, No.zero, No.strict opn) identity
  | Minus : (No.nonstrict opn, No.zero, No.strict opn) identity
  | Times : (No.nonstrict opn, No.zero No.plus, No.strict opn) identity
  | Div : (No.nonstrict opn, No.zero No.plus, No.strict opn) identity
  | Exp : (No.strict opn, No.zero No.plus No.plus, No.nonstrict opn) identity
  | Parens : (closed, No.plus_omega, closed) identity

let plus : (No.nonstrict opn, No.zero, No.strict opn) notation = (Plus, Infixl No.zero)
let minus : (No.nonstrict opn, No.zero, No.strict opn) notation = (Minus, Infixl No.zero)
let times : (No.nonstrict opn, No.zero No.plus, No.strict opn) notation = (Times, Infixl No.one)
let div : (No.nonstrict opn, No.zero No.plus, No.strict opn) notation = (Div, Infixl No.one)
let exp : (No.strict opn, No.zero No.plus No.plus, No.nonstrict opn) notation = (Exp, Infixr No.two)
let parens : (closed, No.plus_omega, closed) notation = (Parens, Outfix)

let () =
  make plus "+" (Open_entry (eop (Op "+") (done_open plus)));
  make minus "-" (Open_entry (eop (Op "-") (done_open minus)));
  make times "*" (Open_entry (eop (Op "*") (done_open times)));
  make div "/" (Open_entry (eop (Op "/") (done_open div)));
  make exp "**" (Open_entry (eop (Op "**") (done_open exp)));
  make parens "()" (Closed_entry (eop LParen (term RParen (Done_closed parens))))

let arith =
  Situation.empty
  |> Situation.add plus
  |> Situation.add minus
  |> Situation.add times
  |> Situation.add div
  |> Situation.add exp
  |> Situation.add parens

exception Syntax_error
exception Fraction

let rec pow x y =
  if x = 1 then 1
  else if x = -1 then if y mod 2 = 0 then 1 else -1
  else if y < 0 then raise Fraction
  else if y = 0 then 1
  else x * pow x (y - 1)

let rec eval : type lt ls rt rs. (lt, ls, rt, rs) parse -> int = function
  | Ident (n, _) ->
      let n = Q.of_string (String.concat "." n) in
      if n.den = Z.one then Z.to_int n.num else raise Syntax_error
  | App { fn; arg; _ } ->
      let x = eval fn.value and y = eval arg.value in
      x * y
  | Notn ((Parens, _), n) -> (
      match args n with
      | [ Term x ] -> eval x.value
      | _ -> raise (Failure "Wrong number of right arguments"))
  | Notn ((op, _), n) -> (
      match args n with
      | [ Term x; Token _; Term y ] -> (
          let x = eval x.value and y = eval y.value in
          match op with
          | Plus -> x + y
          | Minus -> x - y
          | Times -> x * y
          | Div -> if x mod y = 0 then x / y else raise Fraction
          | Exp -> pow x y
          | _ -> raise (Failure "unknown operator"))
      | _ -> raise (Failure "Wrong number of right arguments"))
  | _ -> raise Syntax_error
