open Testutil
open Showparse
open Parser
open Builtins

let () =
  assert (
    parse !builtins "(x : y) -> z"
    = Notn ("pi", [ Flag Explicit_pi; Name (Some "x"); Term (Name "y"); Term (Name "z") ]))

let () =
  assert (
    parse !builtins "(x w : y) -> z"
    = Notn
        ( "pi",
          [ Flag Explicit_pi; Name (Some "x"); Name (Some "w"); Term (Name "y"); Term (Name "z") ]
        ))

let () = assert (parse !builtins "x y |-> z" = Abs (`Normal, [ Some "x"; Some "y" ], Name "z"))
let () = assert (parse !builtins "x y |=> z" = Abs (`Cube, [ Some "x"; Some "y" ], Name "z"))

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
                Term (Notn ("ascription", [ Term (Name "z"); Term (Name "w") ]));
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
                   [ Flag Explicit_pi; Term (Abs (`Normal, [ Some "x"; Some "y" ], Name "z")) ] ));
            Term (Name "w");
          ] ))

let () =
  assert (
    parse !builtins "let x := y in z"
    = Notn ("let", [ Name (Some "x"); Term (Name "y"); Term (Name "z") ]))

let () =
  assert (
    parse !builtins "let x := y in let a ≔ b in c"
    = Notn
        ( "let",
          [
            Name (Some "x");
            Term (Name "y");
            Term (Notn ("let", [ Name (Some "a"); Term (Name "b"); Term (Name "c") ]));
          ] ))

let () =
  assert (
    parse !builtins "let x : a := y in z"
    = Notn ("let", [ Name (Some "x"); Term (Name "a"); Term (Name "y"); Term (Name "z") ]))

let () =
  assert (
    parse !builtins "(x:A){y:B}(z w:C){u : D := M} -> N"
    = Notn
        ( "pi",
          [
            Flag Explicit_pi;
            Name (Some "x");
            Term (Name "A");
            Flag Implicit_pi;
            Name (Some "y");
            Term (Name "B");
            Flag Explicit_pi;
            Name (Some "z");
            Name (Some "w");
            Term (Name "C");
            Flag Implicit_pi;
            Name (Some "u");
            Term (Name "D");
            Flag Default_pi;
            Term (Name "M");
            Term (Name "N");
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
                              Term (Notn ("ascription", [ Term (Name "x"); Term (Name "A") ]));
                            ] ));
                   ] ));
            Term (Name "B");
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
                              Term (Notn ("parens", [ Flag Explicit_pi; Term (Name "x") ]));
                              Term (Name "A");
                            ] ));
                   ] ));
            Term (Name "B");
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
    = Notn ("struc", [ (* flag ignored *) Flag Implicit_pi; Name (Some "x"); Term (Name "y") ]))

let () =
  assert (
    parse !builtins "{.x |-> y}"
    = Notn ("struc", [ (* flag ignored *) Flag Implicit_pi; Field "x"; Term (Name "y") ]))

let () =
  assert (
    parse !builtins "{x := y ; z := w}"
    = Notn
        ( "struc",
          [
            (* flag ignored *)
            Flag Implicit_pi;
            Name (Some "x");
            Term (Name "y");
            Name (Some "z");
            Term (Name "w");
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
            Term (Name "y");
            Field "z";
            Term (Name "w");
          ] ))

let () =
  assert (
    parse !builtins "{x := y ; z := w;}"
    = Notn
        ( "struc",
          [
            (* flag ignored *)
            Flag Implicit_pi;
            Name (Some "x");
            Term (Name "y");
            Name (Some "z");
            Term (Name "w");
          ] ))

let () =
  assert (
    parse !builtins "{x := y ; z := w; a ≔ b}"
    = Notn
        ( "struc",
          [
            (* flag ignored *)
            Flag Implicit_pi;
            Name (Some "x");
            Term (Name "y");
            Name (Some "z");
            Term (Name "w");
            Name (Some "a");
            Term (Name "b");
          ] ))

let () = Types.Sigma.install_notations ()

(*  *)
let () = assert (parse !builtins "A><B" = Notn ("prod", [ Term (Name "A"); Term (Name "B") ]))

let () =
  assert (
    parse !builtins "A >< B >< C"
    = Notn ("prod", [ Term (Name "A"); Term (Notn ("prod", [ Term (Name "B"); Term (Name "C") ])) ]))

let () =
  assert (
    parse !builtins "(x:A) >< B x"
    = Notn
        ( "sigma",
          [
            (* ignored flag *)
            Flag Explicit_pi;
            Name (Some "x");
            Term (Name "A");
            Term (App (Name "B", Name "x"));
          ] ))

let () =
  assert (
    parse !builtins "(x:A) >< (y:B x) >< C x y"
    = Notn
        ( "sigma",
          [
            Flag Explicit_pi;
            Name (Some "x");
            Term (Name "A");
            Term
              (Notn
                 ( "sigma",
                   [
                     Flag Explicit_pi;
                     Name (Some "y");
                     Term (App (Name "B", Name "x"));
                     Term (App (App (Name "C", Name "x"), Name "y"));
                   ] ));
          ] ))
