open Testutil
open Showparse
open Arith

let () =
  Parser.Lexer.Specials.run @@ fun () ->
  Parser.Situation.run_on arith @@ fun () ->
  assert (parse "x" = Ident [ "x" ]);
  assert (parse "x + y" = Notn ("+", [ Term (Ident [ "x" ]); Term (Ident [ "y" ]) ]));

  assert (
    parse "x + y + z"
    = Notn
        ( "+",
          [
            Term (Notn ("+", [ Term (Ident [ "x" ]); Term (Ident [ "y" ]) ])); Term (Ident [ "z" ]);
          ] ));

  assert (
    parse "x ** y ** z"
    = Notn
        ( "**",
          [
            Term (Ident [ "x" ]); Term (Notn ("**", [ Term (Ident [ "y" ]); Term (Ident [ "z" ]) ]));
          ] ));

  assert (
    parse "x * y + z"
    = Notn
        ( "+",
          [
            Term (Notn ("*", [ Term (Ident [ "x" ]); Term (Ident [ "y" ]) ])); Term (Ident [ "z" ]);
          ] ));

  assert (
    parse "x + y * z"
    = Notn
        ( "+",
          [
            Term (Ident [ "x" ]); Term (Notn ("*", [ Term (Ident [ "y" ]); Term (Ident [ "z" ]) ]));
          ] ));

  assert (
    parse "x + y - z"
    = Notn
        ( "-",
          [
            Term (Notn ("+", [ Term (Ident [ "x" ]); Term (Ident [ "y" ]) ])); Term (Ident [ "z" ]);
          ] ));

  assert (
    parse "x - y + z"
    = Notn
        ( "+",
          [
            Term (Notn ("-", [ Term (Ident [ "x" ]); Term (Ident [ "y" ]) ])); Term (Ident [ "z" ]);
          ] ));

  assert (
    parse "x + y ** z * w"
    = Notn
        ( "+",
          [
            Term (Ident [ "x" ]);
            Term
              (Notn
                 ( "*",
                   [
                     Term (Notn ("**", [ Term (Ident [ "y" ]); Term (Ident [ "z" ]) ]));
                     Term (Ident [ "w" ]);
                   ] ));
          ] ));

  assert (
    parse "x * y ** z + w"
    = Notn
        ( "+",
          [
            Term
              (Notn
                 ( "*",
                   [
                     Term (Ident [ "x" ]);
                     Term (Notn ("**", [ Term (Ident [ "y" ]); Term (Ident [ "z" ]) ]));
                   ] ));
            Term (Ident [ "w" ]);
          ] ));

  assert (parse "(x)" = Notn ("()", [ Term (Ident [ "x" ]) ]));

  assert (
    parse "(x+y)"
    = Notn ("()", [ Term (Notn ("+", [ Term (Ident [ "x" ]); Term (Ident [ "y" ]) ])) ]));

  assert (
    parse "x + (y+z)"
    = Notn
        ( "+",
          [
            Term (Ident [ "x" ]);
            Term
              (Notn ("()", [ Term (Notn ("+", [ Term (Ident [ "y" ]); Term (Ident [ "z" ]) ])) ]));
          ] ));

  assert (parse "x y" = App (Ident [ "x" ], Ident [ "y" ]));
  assert (parse "x (y)" = App (Ident [ "x" ], Notn ("()", [ Term (Ident [ "y" ]) ])));
  assert (parse "(x) y" = App (Notn ("()", [ Term (Ident [ "x" ]) ]), Ident [ "y" ]));

  assert (
    parse "x y + z" = Notn ("+", [ Term (App (Ident [ "x" ], Ident [ "y" ])); Term (Ident [ "z" ]) ]));

  assert (
    parse "x + y z" = Notn ("+", [ Term (Ident [ "x" ]); Term (App (Ident [ "y" ], Ident [ "z" ])) ]));

  assert (parse "x y z" = App (App (Ident [ "x" ], Ident [ "y" ]), Ident [ "z" ]));

  assert (
    parse "x (y z)" = App (Ident [ "x" ], Notn ("()", [ Term (App (Ident [ "y" ], Ident [ "z" ])) ])));

  assert (
    parse "x + (v (y + z) * w) u"
    = Notn
        ( "+",
          [
            Term (Ident [ "x" ]);
            Term
              (App
                 ( Notn
                     ( "()",
                       [
                         Term
                           (Notn
                              ( "*",
                                [
                                  Term
                                    (App
                                       ( Ident [ "v" ],
                                         Notn
                                           ( "()",
                                             [
                                               Term
                                                 (Notn
                                                    ( "+",
                                                      [ Term (Ident [ "y" ]); Term (Ident [ "z" ]) ]
                                                    ));
                                             ] ) ));
                                  Term (Ident [ "w" ]);
                                ] ));
                       ] ),
                   Ident [ "u" ] ));
          ] ));

  assert (parse "a. b c" = App (App (Constr "a", Ident [ "b" ]), Ident [ "c" ]));
  assert (parse "a .b c" = App (App (Ident [ "a" ], Field ("b", [])), Ident [ "c" ]))

(* Parsing the church numeral 500, or even 1000, takes a near-negligible amount of time.  I think it helps that we have minimized backtracking. *)
let rec cnat n = if n <= 0 then "x" else "(f " ^ cnat (n - 1) ^ ")"

let _ =
  Parser.Lexer.Specials.run @@ fun () ->
  Parser.Situation.run_on arith @@ fun () -> parse (cnat 500)
