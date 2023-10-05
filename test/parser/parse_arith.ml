open Testutil
open Showparse
open Arith

let () = assert (parse arith "x" = Ok (Name "x"))
let () = assert (parse arith "x + y" = Ok (Notn ("+", [ Term (Name "x"); Term (Name "y") ])))

let () =
  assert (
    parse arith "x + y + z"
    = Ok (Notn ("+", [ Term (Notn ("+", [ Term (Name "x"); Term (Name "y") ])); Term (Name "z") ])))

let () =
  assert (
    parse arith "x ^ y ^ z"
    = Ok (Notn ("^", [ Term (Name "x"); Term (Notn ("^", [ Term (Name "y"); Term (Name "z") ])) ])))

let () =
  assert (
    parse arith "x * y + z"
    = Ok (Notn ("+", [ Term (Notn ("*", [ Term (Name "x"); Term (Name "y") ])); Term (Name "z") ])))

let () =
  assert (
    parse arith "x + y * z"
    = Ok (Notn ("+", [ Term (Name "x"); Term (Notn ("*", [ Term (Name "y"); Term (Name "z") ])) ])))

let () =
  assert (
    parse arith "x + y - z"
    = Ok (Notn ("-", [ Term (Notn ("+", [ Term (Name "x"); Term (Name "y") ])); Term (Name "z") ])))

let () =
  assert (
    parse arith "x - y + z"
    = Ok (Notn ("+", [ Term (Notn ("-", [ Term (Name "x"); Term (Name "y") ])); Term (Name "z") ])))

let () =
  assert (
    parse arith "x + y ^ z * w"
    = Ok
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
    = Ok
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

let () = assert (parse arith "(x)" = Ok (Notn ("()", [ Term (Name "x") ])))

let () =
  assert (
    parse arith "(x+y)"
    = Ok (Notn ("()", [ Term (Notn ("+", [ Term (Name "x"); Term (Name "y") ])) ])))

let () =
  assert (
    parse arith "x + (y+z)"
    = Ok
        (Notn
           ( "+",
             [
               Term (Name "x");
               Term (Notn ("()", [ Term (Notn ("+", [ Term (Name "y"); Term (Name "z") ])) ]));
             ] )))

let () = assert (parse arith "x y" = Ok (App (Name "x", Name "y")))
let () = assert (parse arith "x (y)" = Ok (App (Name "x", Notn ("()", [ Term (Name "y") ]))))
let () = assert (parse arith "(x) y" = Ok (App (Notn ("()", [ Term (Name "x") ]), Name "y")))

let () =
  assert (
    parse arith "x y + z" = Ok (Notn ("+", [ Term (App (Name "x", Name "y")); Term (Name "z") ])))

let () =
  assert (
    parse arith "x + y z" = Ok (Notn ("+", [ Term (Name "x"); Term (App (Name "y", Name "z")) ])))

let () = assert (parse arith "x y z" = Ok (App (App (Name "x", Name "y"), Name "z")))

let () =
  assert (
    parse arith "x (y z)" = Ok (App (Name "x", Notn ("()", [ Term (App (Name "y", Name "z")) ]))))

let () =
  assert (
    parse arith "x + (v (y + z) * w) u"
    = Ok
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

let () = assert (parse arith "a. b c" = Ok (App (App (Constr "a", Name "b"), Name "c")))
let () = assert (parse arith "a .b c" = Ok (App (App (Name "a", Field "b"), Name "c")))
let () = assert (Result.is_error (parse arith "x + y {` unterminated block comment"))

(* Parsing the church numeral 500, or even 1000, takes a near-negligible amount of time.  I think it helps that we have minimized backtracking. *)
let rec cnat n = if n <= 0 then "x" else "(f " ^ cnat (n - 1) ^ ")"
let () = assert (Result.is_ok (parse arith (cnat 500)))
