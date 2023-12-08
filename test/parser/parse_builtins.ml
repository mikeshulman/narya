open Testutil
open Showparse
open Parser
open Builtins

let () =
  assert (
    parse !builtins "(x : y) -> z"
    = Notn
        ( "arrow",
          [
            Term
              (Notn
                 ("parens", [ Term (Notn ("ascription", [ Term (Ident "x"); Term (Ident "y") ])) ]));
            Term (Ident "z");
          ] ))

let () =
  assert (
    parse !builtins "(x w : y) -> z"
    = Notn
        ( "arrow",
          [
            Term
              (Notn
                 ( "parens",
                   [
                     Term
                       (Notn ("ascription", [ Term (App (Ident "x", Ident "w")); Term (Ident "y") ]));
                   ] ));
            Term (Ident "z");
          ] ))

let () =
  assert (
    parse !builtins "x y |-> z"
    = Notn ("abstraction", [ Term (App (Ident "x", Ident "y")); Term (Ident "z") ]))

let () =
  assert (
    parse !builtins "x y |=> z"
    = Notn ("cube_abstraction", [ Term (App (Ident "x", Ident "y")); Term (Ident "z") ]))

let () =
  assert (
    parse !builtins "x y |-> (z : w)"
    = Notn
        ( "abstraction",
          [
            Term (App (Ident "x", Ident "y"));
            Term
              (Notn
                 ("parens", [ Term (Notn ("ascription", [ Term (Ident "z"); Term (Ident "w") ])) ]));
          ] ))

let () =
  assert (
    parse !builtins "(x y |-> z) : w"
    = Notn
        ( "ascription",
          [
            Term
              (Notn
                 ( "parens",
                   [
                     Term
                       (Notn ("abstraction", [ Term (App (Ident "x", Ident "y")); Term (Ident "z") ]));
                   ] ));
            Term (Ident "w");
          ] ))

let () =
  assert (
    parse !builtins "let x := y in z"
    = Notn ("let", [ Term (Ident "x"); Term (Ident "y"); Term (Ident "z") ]))

let () =
  assert (
    parse !builtins "let x := y in let a ≔ b in c"
    = Notn
        ( "let",
          [
            Term (Ident "x");
            Term (Ident "y");
            Term (Notn ("let", [ Term (Ident "a"); Term (Ident "b"); Term (Ident "c") ]));
          ] ))

let () =
  assert (
    parse !builtins "let x : a := y in z"
    = Notn ("let", [ Term (Ident "x"); Term (Ident "a"); Term (Ident "y"); Term (Ident "z") ]))

(* let () =
     assert (
       parse !builtins "(x:A){y:B}(z w:C){u : D := M} -> N"
       = Notn
           ( "pi",
             [

               Ident (Some "x");
               Term (Ident "A");

               Ident (Some "y");
               Term (Ident "B");

               Ident (Some "z");
               Ident (Some "w");
               Term (Ident "C");

               Ident (Some "u");
               Term (Ident "D");
               Flag Default_pi;
               Term (Ident "M");
               Term (Ident "N");
             ] )) *)

(* The parsing of "(X:Type)->Y" is technically ambiguous: in addition to a dependent function-type, it could be a non-dependent function type with ascribed domain.  We always interpret it as a dependent function-type, but to get the non-dependent version you can add extra parentheses.  *)
let () =
  assert (
    parse !builtins "((x:A)) -> B"
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
                            [ Term (Notn ("ascription", [ Term (Ident "x"); Term (Ident "A") ])) ]
                          ));
                   ] ));
            Term (Ident "B");
          ] ))

let () =
  assert (
    parse !builtins "((x):A) -> B"
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
                            [ Term (Notn ("parens", [ Term (Ident "x") ])); Term (Ident "A") ] ));
                   ] ));
            Term (Ident "B");
          ] ))

let () = assert (parse !builtins "{}" = Notn ("struc", []))

let () =
  assert (parse !builtins "{x := y}" = Notn ("struc", [ Term (Ident "x"); Term (Ident "y") ]))

let () =
  assert (parse !builtins "{.x |-> y}" = Notn ("struc", [ Term (Field "x"); Term (Ident "y") ]))

let () =
  assert (
    parse !builtins "{x := y ; z := w}"
    = Notn ("struc", [ Term (Ident "x"); Term (Ident "y"); Term (Ident "z"); Term (Ident "w") ]))

let () =
  assert (
    parse !builtins "{.x ↦ y ; .z ↦ w}"
    = Notn ("struc", [ Term (Field "x"); Term (Ident "y"); Term (Field "z"); Term (Ident "w") ]))

let () =
  assert (
    parse !builtins "{x := y ; z := w;}"
    = Notn ("struc", [ Term (Ident "x"); Term (Ident "y"); Term (Ident "z"); Term (Ident "w") ]))

let () =
  assert (
    parse !builtins "{x := y ; z := w; a ≔ b}"
    = Notn
        ( "struc",
          [
            Term (Ident "x");
            Term (Ident "y");
            Term (Ident "z");
            Term (Ident "w");
            Term (Ident "a");
            Term (Ident "b");
          ] ))

let () = Types.Sigma.install_notations ()

(*  *)
let () = assert (parse !builtins "A><B" = Notn ("prod", [ Term (Ident "A"); Term (Ident "B") ]))

let () =
  assert (
    parse !builtins "A >< B >< C"
    = Notn
        ("prod", [ Term (Ident "A"); Term (Notn ("prod", [ Term (Ident "B"); Term (Ident "C") ])) ]))

let () =
  assert (
    parse !builtins "(x:A) >< B x"
    = Notn
        ( "prod",
          [
            Term
              (Notn
                 ("parens", [ Term (Notn ("ascription", [ Term (Ident "x"); Term (Ident "A") ])) ]));
            Term (App (Ident "B", Ident "x"));
          ] ))

let () =
  assert (
    parse !builtins "(x:A) >< (y:B x) >< C x y"
    = Notn
        ( "prod",
          [
            Term
              (Notn
                 ("parens", [ Term (Notn ("ascription", [ Term (Ident "x"); Term (Ident "A") ])) ]));
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
                                     [ Term (Ident "y"); Term (App (Ident "B", Ident "x")) ] ));
                            ] ));
                     Term (App (App (Ident "C", Ident "x"), Ident "y"));
                   ] ));
          ] ))
