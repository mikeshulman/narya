open Testutil
open Showparse
open Arith

let () = assert (parse arith "x" = Left (Name "x"))
let () = assert (parse arith "x + y" = Left (Notn ("+", [ Term (Name "x"); Term (Name "y") ])))

let () =
  assert (
    parse arith "x + y + z"
    = Left
        (Notn ("+", [ Term (Notn ("+", [ Term (Name "x"); Term (Name "y") ])); Term (Name "z") ])))

let () =
  assert (
    parse arith "x ^ y ^ z"
    = Left
        (Notn ("^", [ Term (Name "x"); Term (Notn ("^", [ Term (Name "y"); Term (Name "z") ])) ])))

let () =
  assert (
    parse arith "x * y + z"
    = Left
        (Notn ("+", [ Term (Notn ("*", [ Term (Name "x"); Term (Name "y") ])); Term (Name "z") ])))

let () =
  assert (
    parse arith "x + y * z"
    = Left
        (Notn ("+", [ Term (Name "x"); Term (Notn ("*", [ Term (Name "y"); Term (Name "z") ])) ])))

let () =
  assert (
    parse arith "x + y - z"
    = Left
        (Notn ("-", [ Term (Notn ("+", [ Term (Name "x"); Term (Name "y") ])); Term (Name "z") ])))

let () =
  assert (
    parse arith "x - y + z"
    = Left
        (Notn ("+", [ Term (Notn ("-", [ Term (Name "x"); Term (Name "y") ])); Term (Name "z") ])))

let () =
  assert (
    parse arith "x + y ^ z * w"
    = Left
        (Notn
           ( "+",
             [
               Term (Name "x");
               Term
                 (Notn
                    ( "*",
                      [ Term (Notn ("^", [ Term (Name "y"); Term (Name "z") ])); Term (Name "w") ]
                    ));
             ] )))

let () =
  assert (
    parse arith "x * y ^ z + w"
    = Left
        (Notn
           ( "+",
             [
               Term
                 (Notn
                    ( "*",
                      [ Term (Name "x"); Term (Notn ("^", [ Term (Name "y"); Term (Name "z") ])) ]
                    ));
               Term (Name "w");
             ] )))

let () = assert (parse arith "(x)" = Left (Notn ("()", [ Term (Name "x") ])))

let () =
  assert (
    parse arith "(x+y)"
    = Left (Notn ("()", [ Term (Notn ("+", [ Term (Name "x"); Term (Name "y") ])) ])))

let () =
  assert (
    parse arith "x + (y+z)"
    = Left
        (Notn
           ( "+",
             [
               Term (Name "x");
               Term (Notn ("()", [ Term (Notn ("+", [ Term (Name "y"); Term (Name "z") ])) ]));
             ] )))

let () = assert (parse arith "x y" = Left (App (Name "x", Name "y")))
let () = assert (parse arith "x (y)" = Left (App (Name "x", Notn ("()", [ Term (Name "y") ]))))
let () = assert (parse arith "(x) y" = Left (App (Notn ("()", [ Term (Name "x") ]), Name "y")))

let () =
  assert (
    parse arith "x y + z" = Left (Notn ("+", [ Term (App (Name "x", Name "y")); Term (Name "z") ])))

let () =
  assert (
    parse arith "x + y z" = Left (Notn ("+", [ Term (Name "x"); Term (App (Name "y", Name "z")) ])))

let () = assert (parse arith "x y z" = Left (App (App (Name "x", Name "y"), Name "z")))

let () =
  assert (
    parse arith "x (y z)" = Left (App (Name "x", Notn ("()", [ Term (App (Name "y", Name "z")) ]))))

let () =
  assert (
    parse arith "x + (v (y + z) * w) u"
    = Left
        (Notn
           ( "+",
             [
               Term (Name "x");
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
                                          ( Name "v",
                                            Notn
                                              ( "()",
                                                [
                                                  Term
                                                    (Notn ("+", [ Term (Name "y"); Term (Name "z") ]));
                                                ] ) ));
                                     Term (Name "w");
                                   ] ));
                          ] ),
                      Name "u" ));
             ] )))

let () = assert (parse arith "a. b c" = Left (App (App (Constr "a", Name "b"), Name "c")))
let () = assert (parse arith "a .b c" = Left (App (App (Name "a", Proj "b"), Name "c")))
let () = assert (Either.is_right (parse arith "x + y {` unterminated block comment"))

(* Parsing the church numeral 500, or even 1000, takes a near-negligible amount of time.  I think it helps that we have minimized backtracking. *)
let rec cnat n = if n <= 0 then "x" else "(f " ^ cnat (n - 1) ^ ")"
let () = assert (Either.is_left (parse arith (cnat 500)))
