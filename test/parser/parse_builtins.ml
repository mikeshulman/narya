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

let () = assert (parse !builtins "x y |-> z" = Abs ([ Some "x"; Some "y" ], Name "z"))

let () =
  assert (
    parse !builtins "x y |-> (z : w)"
    = Abs
        ( [ Some "x"; Some "y" ],
          Notn
            ( "()",
              [
                (* Flag is ignored, since the eventual notation is not a pi. *)
                Flag Explicit_pi;
                Term (Notn (":", [ Term (Name "z"); Term (Name "w") ]));
              ] ) ))

let () =
  assert (
    parse !builtins "(x y |-> z) : w"
    = Notn
        ( ":",
          [
            Term (Notn ("()", [ Flag Explicit_pi; Term (Abs ([ Some "x"; Some "y" ], Name "z")) ]));
            Term (Name "w");
          ] ))

let () =
  assert (
    parse !builtins "let x := y in z"
    = Notn ("let", [ Name (Some "x"); Flag Unasc_let; Term (Name "y"); Term (Name "z") ]))

let () =
  assert (
    parse !builtins "let x := y in let a ≔ b in c"
    = Notn
        ( "let",
          [
            Name (Some "x");
            Flag Unasc_let;
            Term (Name "y");
            Term
              (Notn ("let", [ Name (Some "a"); Flag Unasc_let; Term (Name "b"); Term (Name "c") ]));
          ] ))

let () =
  assert (
    parse !builtins "let x : a := y in z"
    = Notn
        ("let", [ Name (Some "x"); Flag Asc_let; Term (Name "a"); Term (Name "y"); Term (Name "z") ]))

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
let () = assert (parse !builtins "A><B" = Notn ("><", [ Term (Name "A"); Term (Name "B") ]))

let () =
  assert (
    parse !builtins "A >< B >< C"
    = Notn ("><", [ Term (Name "A"); Term (Notn ("><", [ Term (Name "B"); Term (Name "C") ])) ]))

let () =
  assert (
    parse !builtins "(x:A) >< B x"
    = Notn
        ( "sig",
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
        ( "sig",
          [
            Flag Explicit_pi;
            Name (Some "x");
            Term (Name "A");
            Term
              (Notn
                 ( "sig",
                   [
                     Flag Explicit_pi;
                     Name (Some "y");
                     Term (App (Name "B", Name "x"));
                     Term (App (App (Name "C", Name "x"), Name "y"));
                   ] ));
          ] ))
