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
let att = make ~origname:"at" ~tightness:Float.infinity ~left:Closed ~right:Open ~assoc:Non
let () = set_tree att (eop (Op "@") (Done att))

(* And also postfix notations ! and ? of tightness +∞, one left-associative and one not. *)
let bang = make ~origname:"bang" ~tightness:Float.infinity ~left:Open ~right:Closed ~assoc:Non
let () = set_tree bang (eop (Op "!") (Done bang))
let query = make ~origname:"query" ~tightness:Float.infinity ~left:Open ~right:Closed ~assoc:Left
let () = set_tree query (eop (Op "?") (Done query))
let prefixes = !builtins |> State.add att |> State.add bang |> State.add query

(* Plain application *)
let () = assert (parse prefixes "@ f" = Notn ("at", [ Term (Name "f") ]))

(* Since function application is "left-associative" and @ has the same tightness, "@ f x"  is parsed as "(@ f) x".  Since @ is not right-associative, function application can't appear in *its* argument, so "@ (f x)" is not a possible parse. *)
let () = assert (parse prefixes "@ f x" = App (Notn ("at", [ Term (Name "f") ]), Name "x"))

(* Since @ is a prefix notation, it can appear anywhere as an argument, so "f @ x" is parsed as "f (@ x)". *)
let () = assert (parse prefixes "f @ x" = App (Name "f", Notn ("at", [ Term (Name "x") ])))

(* For the same reasons, "@ f @ x" is parsed as "(@ f) (@ x)". *)
let () =
  assert (
    parse prefixes "@ f @ x"
    = App (Notn ("at", [ Term (Name "f") ]), Notn ("at", [ Term (Name "x") ])))

(* Of course we can parenthesize its argument. *)
let () =
  assert (
    parse prefixes "@ (f x)"
    = Notn ("at", [ Term (Notn ("parens", [ Flag Explicit_pi; Term (App (Name "f", Name "x")) ])) ]))

(* And again, since @ is a prefix notation, it can appear anyhere on the right, including inside itself. *)
let () = assert (parse prefixes "@ @ x" = Notn ("at", [ Term (Notn ("at", [ Term (Name "x") ])) ]))

(* Same for field projections, which are literally parsed as applications (and compiled later to something else) *)
let () = assert (parse prefixes "@ f .x" = App (Notn ("at", [ Term (Name "f") ]), Field "x"))

(* But we can't apply @ *to* a field projection, since that's not a valid term on its own. *)
let () = unparse prefixes "f @ .x"

(* Now we experiment with the postfix ones *)
let () = assert (parse prefixes "x !" = Notn ("bang", [ Term (Name "x") ]))
let () = assert (parse prefixes "x ?" = Notn ("query", [ Term (Name "x") ]))
let () = assert (parse prefixes "f x ?" = Notn ("query", [ Term (App (Name "f", Name "x")) ]))

(* It's not possible to get "f x !" to parse as "f (x !)", since function application is not right-associative and nothing is strictly tighter than it. *)
let () = unparse prefixes "f x !"

(* Now we try the operator in the middle.  This works since function application is left-associative. *)
let () = assert (parse prefixes "f ! x" = App (Notn ("bang", [ Term (Name "f") ]), Name "x"))
let () = assert (parse prefixes "f ? x" = App (Notn ("query", [ Term (Name "f") ]), Name "x"))

let () =
  assert (
    parse prefixes "f ? x ?"
    = Notn ("query", [ Term (App (Notn ("query", [ Term (Name "f") ]), Name "x")) ]))

(* We define nonassociative prefix, infix, and postfix operators of the same tightness. *)
let twiddle = make ~origname:"twiddle" ~tightness:0. ~left:Closed ~right:Open ~assoc:Non
let () = set_tree twiddle (eop (Op "~") (Done twiddle))
let star = make ~origname:"star" ~tightness:0. ~left:Open ~right:Closed ~assoc:Non
let () = set_tree star (eop (Op "*") (Done star))
let perc = make ~origname:"perc" ~tightness:0. ~left:Open ~right:Open ~assoc:Non
let () = set_tree perc (eop (Op "%") (Done perc))
let prefixes = !builtins |> State.add twiddle |> State.add star |> State.add perc

let () =
  unparse prefixes "~ x % y";
  assert (parse prefixes "f ~ x" = App (Name "f", Notn ("twiddle", [ Term (Name "x") ])));
  unparse prefixes "f ~ x % y";
  unparse prefixes "x % y *";
  assert (parse prefixes "f * x" = App (Notn ("star", [ Term (Name "f") ]), Name "x"));
  unparse prefixes "x % f * y";
  assert (
    parse prefixes "f * ~ x"
    = App (Notn ("star", [ Term (Name "f") ]), Notn ("twiddle", [ Term (Name "x") ])))
