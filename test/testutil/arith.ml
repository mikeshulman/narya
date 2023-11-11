open Parser
open Notation

(* Notations for arithmetic.  This has nothing to do with the Nat of type theory, it's just a way of testing the parser. *)

let plus = make ~origname:"+" ~tightness:0. ~left:Open ~right:Open ~assoc:Left
let () = set_tree plus (eop (Op "+") (Done plus))
let minus = make ~origname:"-" ~tightness:0. ~left:Open ~right:Open ~assoc:Left
let () = set_tree minus (eop (Op "-") (Done minus))
let times = make ~origname:"*" ~tightness:10. ~left:Open ~right:Open ~assoc:Left
let () = set_tree times (eop (Op "*") (Done times))
let div = make ~origname:"/" ~tightness:10. ~left:Open ~right:Open ~assoc:Left
let () = set_tree div (eop (Op "/") (Done div))
let exp = make ~origname:"^" ~tightness:20. ~left:Open ~right:Open ~assoc:Right
let () = set_tree exp (eop (Op "^") (Done exp))
let parens = make ~origname:"()" ~tightness:Float.infinity ~left:Closed ~right:Closed ~assoc:Non
let () = set_tree parens (eop LParen (term RParen (Done parens)))

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

let rec eval : parse -> int = function
  | Numeral n -> if n.den = Z.one then Z.to_int n.num else raise Syntax_error
  | App (x, y) ->
      let x = eval x and y = eval y in
      x * y
  | Notn (op, [ Term x; Term y ]) ->
      let x = eval x and y = eval y in
      if equal op plus then x + y
      else if equal op minus then x - y
      else if equal op times then x * y
      else if equal op div then if x mod y = 0 then x / y else raise Fraction
      else if equal op exp then pow x y
      else raise (Failure "Wrong number of right arguments")
  | Notn (op, [ Term x ]) ->
      if equal op parens then eval x else raise (Failure "Wrong number of right arguments")
  | Notn _ -> raise (Failure "Wrong number of right arguments")
  | _ -> raise Syntax_error
