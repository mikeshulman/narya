open Testutil
open Showparse
open Parser
open Builtins

let () =
  assert (
    parse !builtins "(x : y) -> z"
    = Left (Notn ("pi", [ Flag Explicit_pi; Name (Some "x"); Term (Name "y"); Term (Name "z") ])))

let () =
  assert (
    parse !builtins "(x w : y) -> z"
    = Left
        (Notn
           ( "pi",
             [
               Flag Explicit_pi; Name (Some "x"); Name (Some "w"); Term (Name "y"); Term (Name "z");
             ] )))

let () = assert (parse !builtins "x y |-> z" = Left (Abs ([ Some "x"; Some "y" ], Name "z")))
let () = assert (Either.is_right (parse !builtins "x y |-> z : w"))

let () =
  assert (
    parse !builtins "x y |-> (z : w)"
    = Left
        (Abs
           ( [ Some "x"; Some "y" ],
             Notn
               ( "()",
                 [
                   (* Flag is ignored, since the eventual notation is not a pi. *)
                   Flag Explicit_pi;
                   Term (Notn (":", [ Term (Name "z"); Term (Name "w") ]));
                 ] ) )))

let () =
  assert (
    parse !builtins "(x y |-> z) : w"
    = Left
        (Notn
           ( ":",
             [
               Term
                 (Notn ("()", [ Flag Explicit_pi; Term (Abs ([ Some "x"; Some "y" ], Name "z")) ]));
               Term (Name "w");
             ] )))

let () =
  assert (
    parse !builtins "let x := y in z"
    = Left (Notn ("let", [ Name (Some "x"); Flag Unasc_let; Term (Name "y"); Term (Name "z") ])))

let () =
  assert (
    parse !builtins "let x := y in let a ≔ b in c"
    = Left
        (Notn
           ( "let",
             [
               Name (Some "x");
               Flag Unasc_let;
               Term (Name "y");
               Term
                 (Notn ("let", [ Name (Some "a"); Flag Unasc_let; Term (Name "b"); Term (Name "c") ]));
             ] )))

let () = assert (Either.is_right (parse !builtins "let x := a in b : c"))

let () =
  assert (
    parse !builtins "let x : a := y in z"
    = Left
        (Notn
           ( "let",
             [ Name (Some "x"); Flag Asc_let; Term (Name "a"); Term (Name "y"); Term (Name "z") ] )))

let () =
  assert (
    parse !builtins "(x:A){y:B}(z w:C){u : D := M} -> N"
    = Left
        (Notn
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
             ] )))

let () = Types.Sigma.install ()

let () =
  assert (
    parse !builtins "{}"
    = Left
        (Notn
           ( "struc",
             [ (* Flag is ignored, since the eventual notation is not a pi *) Flag Implicit_pi ] )))

let () =
  assert (
    parse !builtins "{x := y}"
    = Left
        (Notn ("struc", [ (* flag ignored *) Flag Implicit_pi; Name (Some "x"); Term (Name "y") ])))

let () =
  assert (
    parse !builtins "{x := y ; z := w}"
    = Left
        (Notn
           ( "struc",
             [
               (* flag ignored *)
               Flag Implicit_pi;
               Name (Some "x");
               Term (Name "y");
               Name (Some "z");
               Term (Name "w");
             ] )))

let () =
  assert (
    parse !builtins "{x := y ; z := w;}"
    = Left
        (Notn
           ( "struc",
             [
               (* flag ignored *)
               Flag Implicit_pi;
               Name (Some "x");
               Term (Name "y");
               Name (Some "z");
               Term (Name "w");
             ] )))

let () =
  assert (
    parse !builtins "{x := y ; z := w; a ≔ b}"
    = Left
        (Notn
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
             ] )))

let () = assert (parse !builtins "A><B" = Left (Notn ("><", [ Term (Name "A"); Term (Name "B") ])))

let () =
  assert (
    parse !builtins "A >< B >< C"
    = Left
        (Notn ("><", [ Term (Name "A"); Term (Notn ("><", [ Term (Name "B"); Term (Name "C") ])) ])))

let () =
  assert (
    parse !builtins "(x:A) >< B x"
    = Left
        (Notn
           ( "sig",
             [
               (* ignored flag *)
               Flag Explicit_pi;
               Name (Some "x");
               Term (Name "A");
               Term (App (Name "B", Name "x"));
             ] )))

let () =
  assert (
    parse !builtins "(x:A) >< (y:B x) >< C x y"
    = Left
        (Notn
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
             ] )))
