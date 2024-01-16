open Testutil
open Showparse
open Parser

let () =
  Builtins.run @@ fun () ->
  assert (
    parse "(x : y) -> z"
    = Notn
        ( "arrow",
          [
            Term
              (Notn
                 ( "parens",
                   [ Term (Notn ("ascription", [ Term (Ident [ "x" ]); Term (Ident [ "y" ]) ])) ] ));
            Term (Ident [ "z" ]);
          ] ));

  assert (
    parse "(x w : y) -> z"
    = Notn
        ( "arrow",
          [
            Term
              (Notn
                 ( "parens",
                   [
                     Term
                       (Notn
                          ( "ascription",
                            [ Term (App (Ident [ "x" ], Ident [ "w" ])); Term (Ident [ "y" ]) ] ));
                   ] ));
            Term (Ident [ "z" ]);
          ] ));

  assert (
    parse "x y |-> z"
    = Notn ("abstraction", [ Term (App (Ident [ "x" ], Ident [ "y" ])); Term (Ident [ "z" ]) ]));

  assert (
    parse "x y |=> z"
    = Notn ("cube_abstraction", [ Term (App (Ident [ "x" ], Ident [ "y" ])); Term (Ident [ "z" ]) ]));

  assert (
    parse "x y |-> (z : w)"
    = Notn
        ( "abstraction",
          [
            Term (App (Ident [ "x" ], Ident [ "y" ]));
            Term
              (Notn
                 ( "parens",
                   [ Term (Notn ("ascription", [ Term (Ident [ "z" ]); Term (Ident [ "w" ]) ])) ] ));
          ] ));

  assert (
    parse "(x y |-> z) : w"
    = Notn
        ( "ascription",
          [
            Term
              (Notn
                 ( "parens",
                   [
                     Term
                       (Notn
                          ( "abstraction",
                            [ Term (App (Ident [ "x" ], Ident [ "y" ])); Term (Ident [ "z" ]) ] ));
                   ] ));
            Term (Ident [ "w" ]);
          ] ));

  assert (
    parse "let x := y in z"
    = Notn ("let", [ Term (Ident [ "x" ]); Term (Ident [ "y" ]); Term (Ident [ "z" ]) ]));

  assert (
    parse "let x := y in let a ≔ b in c"
    = Notn
        ( "let",
          [
            Term (Ident [ "x" ]);
            Term (Ident [ "y" ]);
            Term
              (Notn ("let", [ Term (Ident [ "a" ]); Term (Ident [ "b" ]); Term (Ident [ "c" ]) ]));
          ] ));

  assert (
    parse "let x : a := y in z"
    = Notn
        ( "let",
          [ Term (Ident [ "x" ]); Term (Ident [ "a" ]); Term (Ident [ "y" ]); Term (Ident [ "z" ]) ]
        ))
  (* The parsing of "(X:Type)->Y" is technically ambiguous: in addition to a dependent function-type, it could be a non-dependent function type with ascribed domain.  We always interpret it as a dependent function-type, but to get the non-dependent version you can add extra parentheses.  *);

  assert (
    parse "((x:A)) -> B"
    = Notn
        ( "arrow",
          [
            Term
              (Notn
                 ( "parens",
                   [
                     Term
                       (Notn
                          ( "parens",
                            [
                              Term
                                (Notn ("ascription", [ Term (Ident [ "x" ]); Term (Ident [ "A" ]) ]));
                            ] ));
                   ] ));
            Term (Ident [ "B" ]);
          ] ));

  assert (
    parse "((x):A) -> B"
    = Notn
        ( "arrow",
          [
            Term
              (Notn
                 ( "parens",
                   [
                     Term
                       (Notn
                          ( "ascription",
                            [
                              Term (Notn ("parens", [ Term (Ident [ "x" ]) ])); Term (Ident [ "A" ]);
                            ] ));
                   ] ));
            Term (Ident [ "B" ]);
          ] ));

  assert (parse "()" = Notn ("parens", []));

  assert (
    parse "(x := y)"
    = Notn ("parens", [ Term (Notn ("coloneq", [ Term (Ident [ "x" ]); Term (Ident [ "y" ]) ])) ]));

  assert (parse "[.x |-> y]" = Notn ("comatch", [ Term (Field "x"); Term (Ident [ "y" ]) ]));

  assert (
    parse "(x := y , z := w)"
    = Notn
        ( "parens",
          [
            Term (Notn ("coloneq", [ Term (Ident [ "x" ]); Term (Ident [ "y" ]) ]));
            Term (Notn ("coloneq", [ Term (Ident [ "z" ]); Term (Ident [ "w" ]) ]));
          ] ));

  assert (parse "(x , y)" = Notn ("parens", [ Term (Ident [ "x" ]); Term (Ident [ "y" ]) ]));

  assert (
    parse "[.x ↦ y | .z ↦ w]"
    = Notn
        ( "comatch",
          [ Term (Field "x"); Term (Ident [ "y" ]); Term (Field "z"); Term (Ident [ "w" ]) ] ));

  assert (
    parse "(x := y , z := w,)"
    = Notn
        ( "parens",
          [
            Term (Notn ("coloneq", [ Term (Ident [ "x" ]); Term (Ident [ "y" ]) ]));
            Term (Notn ("coloneq", [ Term (Ident [ "z" ]); Term (Ident [ "w" ]) ]));
          ] ));

  assert (
    parse "(x := y , z := w, a ≔ b)"
    = Notn
        ( "parens",
          [
            Term (Notn ("coloneq", [ Term (Ident [ "x" ]); Term (Ident [ "y" ]) ]));
            Term (Notn ("coloneq", [ Term (Ident [ "z" ]); Term (Ident [ "w" ]) ]));
            Term (Notn ("coloneq", [ Term (Ident [ "a" ]); Term (Ident [ "b" ]) ]));
          ] ));

  Types.Sigma.install_notations () (*  *);

  assert (parse "A><B" = Notn ("prod", [ Term (Ident [ "A" ]); Term (Ident [ "B" ]) ]));

  assert (
    parse "A >< B >< C"
    = Notn
        ( "prod",
          [
            Term (Ident [ "A" ]);
            Term (Notn ("prod", [ Term (Ident [ "B" ]); Term (Ident [ "C" ]) ]));
          ] ));

  assert (
    parse "(x:A) >< B x"
    = Notn
        ( "prod",
          [
            Term
              (Notn
                 ( "parens",
                   [ Term (Notn ("ascription", [ Term (Ident [ "x" ]); Term (Ident [ "A" ]) ])) ] ));
            Term (App (Ident [ "B" ], Ident [ "x" ]));
          ] ));

  assert (
    parse "(x:A) >< (y:B x) >< C x y"
    = Notn
        ( "prod",
          [
            Term
              (Notn
                 ( "parens",
                   [ Term (Notn ("ascription", [ Term (Ident [ "x" ]); Term (Ident [ "A" ]) ])) ] ));
            Term
              (Notn
                 ( "prod",
                   [
                     Term
                       (Notn
                          ( "parens",
                            [
                              Term
                                (Notn
                                   ( "ascription",
                                     [
                                       Term (Ident [ "y" ]);
                                       Term (App (Ident [ "B" ], Ident [ "x" ]));
                                     ] ));
                            ] ));
                     Term (App (App (Ident [ "C" ], Ident [ "x" ]), Ident [ "y" ]));
                   ] ));
          ] ))
