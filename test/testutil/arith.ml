open Parser
open Notations
open Compile

(* Notations for arithmetic.  This has nothing to do with the Nat of type theory, it's just a way of testing the parser. *)

let plus =
  make ~name:"+" ~tightness:0. ~left:Open ~right:Open ~assoc:Left ~tree:(fun n ->
      eop (Op "+") (Done n))

let minus =
  make ~name:"-" ~tightness:0. ~left:Open ~right:Open ~assoc:Left ~tree:(fun n ->
      eop (Op "-") (Done n))

let times =
  make ~name:"*" ~tightness:10. ~left:Open ~right:Open ~assoc:Left ~tree:(fun n ->
      eop (Op "*") (Done n))

let div =
  make ~name:"/" ~tightness:10. ~left:Open ~right:Open ~assoc:Left ~tree:(fun n ->
      eop (Op "/") (Done n))

let exp =
  make ~name:"^" ~tightness:20. ~left:Open ~right:Open ~assoc:Right ~tree:(fun n ->
      eop (Op "^") (Done n))

let parens =
  make ~name:"()" ~tightness:Float.infinity ~left:Closed ~right:Closed ~assoc:Non ~tree:(fun n ->
      eop LParen (term RParen (Done n)))

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

let rec eval : parse_tree -> int = function
  | Numeral n -> if n.den = Z.one then Z.to_int n.num else raise Syntax_error
  | App (x, y) ->
      let x = eval x and y = eval y in
      x * y
  | Notn (op, [ Term x; Term y ]) ->
      let x = eval x and y = eval y in
      if op = plus then x + y
      else if op = minus then x - y
      else if op = times then x * y
      else if op = div then if x mod y = 0 then x / y else raise Fraction
      else if op = exp then pow x y
      else raise (Failure "Wrong number of right arguments")
  | Notn (op, [ Term x ]) ->
      if op = parens then eval x else raise (Failure "Wrong number of right arguments")
  | Notn _ -> raise (Failure "Wrong number of right arguments")
  | _ -> raise Syntax_error
