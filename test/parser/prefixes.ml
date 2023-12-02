open Util
open Testutil
open Showparse
open Parser
open Notation
open Builtins

let unparse state str =
  Core.Reporter.run ~emit:(fun _ -> ()) ~fatal:(fun _ -> ()) @@ fun () ->
  let _ = parse state str in
  raise (Failure "Unexpected parse success")

(* We define a nonassociative prefix notation @ of tightness +∞, the same tightness as function application. *)
let att = make "at" (Prefix No.plus_omega)
let () = set_tree att (eop (Op "@") (Done att))

(* And also postfix notations ! and ? of tightness +∞, one left-associative and one not. *)
let bang = make "bang" (Postfix No.plus_omega)
let () = set_tree bang (eop (Op "!") (Done bang))
let query = make "query" (Postfixl No.plus_omega)
let () = set_tree query (eop (Op "?") (Done query))
let prefixes = !builtins |> State.add att |> State.add bang |> State.add query

(* Plain application *)
let () = assert (parse prefixes "@ f" = Notn ("at", [ Term (Ident "f") ]))

(* Since function application is "left-associative" and @ has the same tightness, "@ f x"  is parsed as "(@ f) x".  Since @ is not right-associative, function application can't appear in *its* argument, so "@ (f x)" is not a possible parse. *)
let () = assert (parse prefixes "@ f x" = App (Notn ("at", [ Term (Ident "f") ]), Ident "x"))

(* Since @ is a prefix notation, it can appear anywhere as an argument, so "f @ x" is parsed as "f (@ x)". *)
let () = assert (parse prefixes "f @ x" = App (Ident "f", Notn ("at", [ Term (Ident "x") ])))

(* For the same reasons, "@ f @ x" is parsed as "(@ f) (@ x)". *)
let () =
  assert (
    parse prefixes "@ f @ x"
    = App (Notn ("at", [ Term (Ident "f") ]), Notn ("at", [ Term (Ident "x") ])))

(* Of course we can parenthesize its argument. *)
let () =
  assert (
    parse prefixes "@ (f x)"
    = Notn
        ("at", [ Term (Notn ("parens", [ Flag Explicit_pi; Term (App (Ident "f", Ident "x")) ])) ]))

(* And again, since @ is a prefix notation, it can appear anyhere on the right, including inside itself. *)
let () = assert (parse prefixes "@ @ x" = Notn ("at", [ Term (Notn ("at", [ Term (Ident "x") ])) ]))

(* Same for field projections, which are literally parsed as applications (and compiled later to something else) *)
let () = assert (parse prefixes "@ f .x" = App (Notn ("at", [ Term (Ident "f") ]), Field "x"))

(* But we can't apply @ *to* a field projection, since that's not a valid term on its own. *)
let () = unparse prefixes "f @ .x"

(* Now we experiment with the postfix ones *)
let () = assert (parse prefixes "x !" = Notn ("bang", [ Term (Ident "x") ]))
let () = assert (parse prefixes "x ?" = Notn ("query", [ Term (Ident "x") ]))
let () = assert (parse prefixes "f x ?" = Notn ("query", [ Term (App (Ident "f", Ident "x")) ]))

(* It's not possible to get "f x !" to parse as "f (x !)", since function application is not right-associative and nothing is strictly tighter than it. *)
let () = unparse prefixes "f x !"

(* Now we try the operator in the middle.  This works since function application is left-associative. *)
let () = assert (parse prefixes "f ! x" = App (Notn ("bang", [ Term (Ident "f") ]), Ident "x"))
let () = assert (parse prefixes "f ? x" = App (Notn ("query", [ Term (Ident "f") ]), Ident "x"))

let () =
  assert (
    parse prefixes "f ? x ?"
    = Notn ("query", [ Term (App (Notn ("query", [ Term (Ident "f") ]), Ident "x")) ]))

(* We define nonassociative prefix, infix, and postfix operators of the same tightness. *)
let twiddle = make "twiddle" (Prefix No.zero)
let () = set_tree twiddle (eop (Op "~") (Done twiddle))
let star = make "star" (Postfix No.zero)
let () = set_tree star (eop (Op "*") (Done star))
let perc = make "perc" (Infix No.zero)
let () = set_tree perc (eop (Op "%") (Done perc))
let prefixes = !builtins |> State.add twiddle |> State.add star |> State.add perc

let () =
  unparse prefixes "~ x % y";
  assert (parse prefixes "f ~ x" = App (Ident "f", Notn ("twiddle", [ Term (Ident "x") ])));
  unparse prefixes "f ~ x % y";
  unparse prefixes "x % y *";
  assert (parse prefixes "f * x" = App (Notn ("star", [ Term (Ident "f") ]), Ident "x"));
  unparse prefixes "x % f * y";
  assert (
    parse prefixes "f * ~ x"
    = App (Notn ("star", [ Term (Ident "f") ]), Notn ("twiddle", [ Term (Ident "x") ])))

let () =
  assert (
    parse prefixes "f % x ↦ y"
    = Notn ("perc", [ Term (Ident "f"); Term (Abs (`Normal, [ Some "x" ], Ident "y")) ]))
