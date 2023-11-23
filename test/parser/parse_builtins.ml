open Testutil
open Showparse
open Parser
open Builtins

let () =
  assert (
    parse !builtins "(x : y) -> z"
    = Notn ("pi", [ Flag Explicit_pi; Ident (Some "x"); Term (Ident "y"); Term (Ident "z") ]))

let () =
  assert (
    parse !builtins "(x w : y) -> z"
    = Notn
        ( "pi",
          [
            Flag Explicit_pi; Ident (Some "x"); Ident (Some "w"); Term (Ident "y"); Term (Ident "z");
          ] ))

let () = assert (parse !builtins "x y |-> z" = Abs (`Normal, [ Some "x"; Some "y" ], Ident "z"))
let () = assert (parse !builtins "x y |=> z" = Abs (`Cube, [ Some "x"; Some "y" ], Ident "z"))

let () =
  assert (
    parse !builtins "x y |-> (z : w)"
    = Abs
        ( `Normal,
          [ Some "x"; Some "y" ],
          Notn
            ( "parens",
              [
                (* Flag is ignored, since the eventual notation is not a pi. *)
                Flag Explicit_pi;
                Term (Notn ("ascription", [ Term (Ident "z"); Term (Ident "w") ]));
              ] ) ))

let () =
  assert (
    parse !builtins "(x y |-> z) : w"
    = Notn
        ( "ascription",
          [
            Term
              (Notn
                 ( "parens",
                   [ Flag Explicit_pi; Term (Abs (`Normal, [ Some "x"; Some "y" ], Ident "z")) ] ));
            Term (Ident "w");
          ] ))

let () =
  assert (
    parse !builtins "let x := y in z"
    = Notn ("let", [ Ident (Some "x"); Term (Ident "y"); Term (Ident "z") ]))

let () =
  assert (
    parse !builtins "let x := y in let a ≔ b in c"
    = Notn
        ( "let",
          [
            Ident (Some "x");
            Term (Ident "y");
            Term (Notn ("let", [ Ident (Some "a"); Term (Ident "b"); Term (Ident "c") ]));
          ] ))

let () =
  assert (
    parse !builtins "let x : a := y in z"
    = Notn ("let", [ Ident (Some "x"); Term (Ident "a"); Term (Ident "y"); Term (Ident "z") ]))

let () =
  assert (
    parse !builtins "(x:A){y:B}(z w:C){u : D := M} -> N"
    = Notn
        ( "pi",
          [
            Flag Explicit_pi;
            Ident (Some "x");
            Term (Ident "A");
            Flag Implicit_pi;
            Ident (Some "y");
            Term (Ident "B");
            Flag Explicit_pi;
            Ident (Some "z");
            Ident (Some "w");
            Term (Ident "C");
            Flag Implicit_pi;
            Ident (Some "u");
            Term (Ident "D");
            Flag Default_pi;
            Term (Ident "M");
            Term (Ident "N");
          ] ))

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
                     Flag Explicit_pi;
                     Term
                       (Notn
                          ( "parens",
                            [
                              Flag Explicit_pi;
                              Term (Notn ("ascription", [ Term (Ident "x"); Term (Ident "A") ]));
                            ] ));
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
                     Flag Explicit_pi;
                     Term
                       (Notn
                          ( "ascription",
                            [
                              Term (Notn ("parens", [ Flag Explicit_pi; Term (Ident "x") ]));
                              Term (Ident "A");
                            ] ));
                   ] ));
            Term (Ident "B");
          ] ))

let () =
  assert (
    parse !builtins "{}"
    = Notn
        ( "struc",
          [ (* Flag is ignored, since the eventual notation is not a pi *) Flag Implicit_pi ] ))

let () =
  assert (
    parse !builtins "{x := y}"
    = Notn ("struc", [ (* flag ignored *) Flag Implicit_pi; Ident (Some "x"); Term (Ident "y") ]))

let () =
  assert (
    parse !builtins "{.x |-> y}"
    = Notn ("struc", [ (* flag ignored *) Flag Implicit_pi; Field "x"; Term (Ident "y") ]))

let () =
  assert (
    parse !builtins "{x := y ; z := w}"
    = Notn
        ( "struc",
          [
            (* flag ignored *)
            Flag Implicit_pi;
            Ident (Some "x");
            Term (Ident "y");
            Ident (Some "z");
            Term (Ident "w");
          ] ))

let () =
  assert (
    parse !builtins "{.x ↦ y ; .z ↦ w}"
    = Notn
        ( "struc",
          [
            (* flag ignored *)
            Flag Implicit_pi;
            Field "x";
            Term (Ident "y");
            Field "z";
            Term (Ident "w");
          ] ))

let () =
  assert (
    parse !builtins "{x := y ; z := w;}"
    = Notn
        ( "struc",
          [
            (* flag ignored *)
            Flag Implicit_pi;
            Ident (Some "x");
            Term (Ident "y");
            Ident (Some "z");
            Term (Ident "w");
          ] ))

let () =
  assert (
    parse !builtins "{x := y ; z := w; a ≔ b}"
    = Notn
        ( "struc",
          [
            (* flag ignored *)
            Flag Implicit_pi;
            Ident (Some "x");
            Term (Ident "y");
            Ident (Some "z");
            Term (Ident "w");
            Ident (Some "a");
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
        ( "sigma",
          [
            (* ignored flag *)
            Flag Explicit_pi;
            Ident (Some "x");
            Term (Ident "A");
            Term (App (Ident "B", Ident "x"));
          ] ))

let () =
  assert (
    parse !builtins "(x:A) >< (y:B x) >< C x y"
    = Notn
        ( "sigma",
          [
            Flag Explicit_pi;
            Ident (Some "x");
            Term (Ident "A");
            Term
              (Notn
                 ( "sigma",
                   [
                     Flag Explicit_pi;
                     Ident (Some "y");
                     Term (App (Ident "B", Ident "x"));
                     Term (App (App (Ident "C", Ident "x"), Ident "y"));
                   ] ));
          ] ))
