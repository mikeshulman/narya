open Util
open Testutil
open Showparse
open Parser
open Notation

let unparse str =
  Core.Reporter.run ~emit:(fun _ -> ()) ~fatal:(fun _ -> ()) @@ fun () ->
  let _ = parse str in
  raise (Failure "Unexpected parse success")

(* We define a nonassociative prefix notation @ of tightness +∞, the same tightness as function application. *)
let att = make "at" (Prefix No.plus_omega)
let () = set_tree att (Closed_entry (eop (Op "@") (Done_closed att)))

(* And also postfix notations ! and !! of tightness +∞, one left-associative and one not. *)
let bang = make "bang" (Postfix No.plus_omega)
let () = set_tree bang (Open_entry (eop (Op "!") (done_open bang)))
let query = make "query" (Postfixl No.plus_omega)
let () = set_tree query (Open_entry (eop (Op "!!") (done_open query)))

let () =
  Builtins.run @@ fun () ->
  State.Current.add att;
  State.Current.add bang;
  State.Current.add query (* Plain application *);

  assert (parse "@ f" = Notn ("at", [ Term (Ident [ "f" ]) ]))
  (* Since function application is "left-associative" and @ has the same tightness, "@ f x"  is parsed as "(@ f) x".  Since @ is not right-associative, function application can't appear in *its* argument, so "@ (f x)" is not a possible parse. *);

  assert (parse "@ f x" = App (Notn ("at", [ Term (Ident [ "f" ]) ]), Ident [ "x" ]))
  (* Since @ is a prefix notation, it can appear anywhere as an argument, so "f @ x" is parsed as "f (@ x)", and "f @ x y" is parsed as "f (@ x) y". *);

  assert (parse "f @ x" = App (Ident [ "f" ], Notn ("at", [ Term (Ident [ "x" ]) ])));

  assert (
    parse "f @ x y" = App (App (Ident [ "f" ], Notn ("at", [ Term (Ident [ "x" ]) ])), Ident [ "y" ]))
  (* For the same reasons, "@ f @ x" is parsed as "(@ f) (@ x)". *);

  assert (
    parse "@ f @ x"
    = App (Notn ("at", [ Term (Ident [ "f" ]) ]), Notn ("at", [ Term (Ident [ "x" ]) ])))
  (* Of course we can parenthesize its argument. *);

  assert (
    parse "@ (f x)"
    = Notn ("at", [ Term (Notn ("parens", [ Term (App (Ident [ "f" ], Ident [ "x" ])) ])) ]))
  (* And again, since @ is a prefix notation, it can appear anyhere on the right, including inside itself. *);

  assert (parse "@ @ x" = Notn ("at", [ Term (Notn ("at", [ Term (Ident [ "x" ]) ])) ]))
  (* Same for field projections, which are literally parsed as applications (and compiled later to something else) *);

  assert (parse "@ f .x" = App (Notn ("at", [ Term (Ident [ "f" ]) ]), Field "x"))
  (* But we can't apply @ *to* a field projection, since that's not a valid term on its own. *);

  unparse "f @ .x" (* Now we experiment with the postfix ones *);

  assert (parse "x !" = Notn ("bang", [ Term (Ident [ "x" ]) ]));
  assert (parse "x !!" = Notn ("query", [ Term (Ident [ "x" ]) ]));

  assert (parse "f x !!" = Notn ("query", [ Term (App (Ident [ "f" ], Ident [ "x" ])) ]))
  (* It's not possible to get "f x !" to parse as "f (x !)", since function application is not right-associative and nothing is strictly tighter than it. *);

  unparse "f x !"
  (* Now we try the operator in the middle.  This works since function application is left-associative. *);

  assert (parse "f ! x" = App (Notn ("bang", [ Term (Ident [ "f" ]) ]), Ident [ "x" ]));

  assert (parse "f !! x" = App (Notn ("query", [ Term (Ident [ "f" ]) ]), Ident [ "x" ]));

  assert (
    parse "f !! x !!"
    = Notn ("query", [ Term (App (Notn ("query", [ Term (Ident [ "f" ]) ]), Ident [ "x" ])) ]))

(* We define nonassociative prefix, infix, and postfix operators of the same tightness. *)
let twiddle = make "twiddle" (Prefix No.zero)
let () = set_tree twiddle (Closed_entry (eop (Op "~") (Done_closed twiddle)))
let star = make "star" (Postfix No.zero)
let () = set_tree star (Open_entry (eop (Op "*") (done_open star)))
let perc = make "perc" (Infix No.zero)
let () = set_tree perc (Open_entry (eop (Op "%") (done_open perc)))

let () =
  Builtins.run @@ fun () ->
  State.Current.add twiddle;
  State.Current.add star;
  State.Current.add perc;
  unparse "~ x % y";
  assert (parse "f ~ x" = App (Ident [ "f" ], Notn ("twiddle", [ Term (Ident [ "x" ]) ])));
  unparse "f ~ x % y";
  unparse "x % y *";
  assert (parse "f * x" = App (Notn ("star", [ Term (Ident [ "f" ]) ]), Ident [ "x" ]));
  unparse "x % f * y";
  assert (
    parse "f * ~ x"
    = App (Notn ("star", [ Term (Ident [ "f" ]) ]), Notn ("twiddle", [ Term (Ident [ "x" ]) ])));

  assert (
    parse "a % b ~ c"
    = Notn
        ( "perc",
          [
            Term (Ident [ "a" ]);
            Term (App (Ident [ "b" ], Notn ("twiddle", [ Term (Ident [ "c" ]) ])));
          ] ))

(* A right-associative infix operator of tightness -ω can have an abstraction on its right. *)
let atat = make "atat" (Infixr No.minus_omega)
let () = set_tree atat (Open_entry (eop (Op "@@") (done_open atat)))

let () =
  Builtins.run @@ fun () ->
  State.Current.add atat;
  assert (
    parse "f @@ x ↦ y"
    = Notn
        ( "atat",
          [
            Term (Ident [ "f" ]);
            Term (Notn ("abstraction", [ Term (Ident [ "x" ]); Term (Ident [ "y" ]) ]));
          ] ))
