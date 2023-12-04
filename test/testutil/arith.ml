open Util
open Parser
open Notation

(* Notations for arithmetic.  This has nothing to do with the Nat of type theory, it's just a way of testing the parser. *)

let plus = make "+" (Infixl No.zero)
let () = set_tree plus (Open_entry (eop (Op "+") (done_open plus)))
let minus = make "-" (Infixl No.zero)
let () = set_tree minus (Open_entry (eop (Op "-") (done_open minus)))
let times = make "*" (Infixl No.one)
let () = set_tree times (Open_entry (eop (Op "*") (done_open times)))
let div = make "/" (Infixl No.one)
let () = set_tree div (Open_entry (eop (Op "/") (done_open div)))
let exp = make "^" (Infixr No.two)
let () = set_tree exp (Open_entry (eop (Op "^") (done_open exp)))
let parens = make "()" Outfix
let () = set_tree parens (Closed_entry (eop LParen (term RParen (Done_closed parens))))

let arith =
  State.empty
  |> State.add plus
  |> State.add minus
  |> State.add times
  |> State.add div
  |> State.add exp
  |> State.add parens

exception Syntax_error
exception Fraction

let rec pow x y =
  if x = 1 then 1
  else if x = -1 then if y mod 2 = 0 then 1 else -1
  else if y < 0 then raise Fraction
  else if y = 0 then 1
  else x * pow x (y - 1)

let rec eval : type lt ls rt rs. (lt, ls, rt, rs) parse -> int = function
  | Numeral n -> if n.den = Z.one then Z.to_int n.num else raise Syntax_error
  | App { fn; arg; _ } ->
      let x = eval fn and y = eval arg in
      x * y
  | Notn { notn = op; first = Some_first x; last = Some_last y; inner = Emp; _ } ->
      let x = eval x and y = eval y in
      if equal op plus then x + y
      else if equal op minus then x - y
      else if equal op times then x * y
      else if equal op div then if x mod y = 0 then x / y else raise Fraction
      else if equal op exp then pow x y
      else raise (Failure "Wrong number of right arguments")
  | Notn { notn = op; inner = Snoc (Emp, Term x); _ } ->
      if equal op parens then eval x else raise (Failure "Wrong number of right arguments")
  | _ -> raise Syntax_error
