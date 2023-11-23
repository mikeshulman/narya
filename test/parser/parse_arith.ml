open Testutil
open Showparse
open Arith

let () = assert (parse arith "x" = Ident "x")
let () = assert (parse arith "x + y" = Notn ("+", [ Term (Ident "x"); Term (Ident "y") ]))

let () =
  assert (
    parse arith "x + y + z"
    = Notn ("+", [ Term (Notn ("+", [ Term (Ident "x"); Term (Ident "y") ])); Term (Ident "z") ]))

let () =
  assert (
    parse arith "x ^ y ^ z"
    = Notn ("^", [ Term (Ident "x"); Term (Notn ("^", [ Term (Ident "y"); Term (Ident "z") ])) ]))

let () =
  assert (
    parse arith "x * y + z"
    = Notn ("+", [ Term (Notn ("*", [ Term (Ident "x"); Term (Ident "y") ])); Term (Ident "z") ]))

let () =
  assert (
    parse arith "x + y * z"
    = Notn ("+", [ Term (Ident "x"); Term (Notn ("*", [ Term (Ident "y"); Term (Ident "z") ])) ]))

let () =
  assert (
    parse arith "x + y - z"
    = Notn ("-", [ Term (Notn ("+", [ Term (Ident "x"); Term (Ident "y") ])); Term (Ident "z") ]))

let () =
  assert (
    parse arith "x - y + z"
    = Notn ("+", [ Term (Notn ("-", [ Term (Ident "x"); Term (Ident "y") ])); Term (Ident "z") ]))

let () =
  assert (
    parse arith "x + y ^ z * w"
    = Notn
        ( "+",
          [
            Term (Ident "x");
            Term
              (Notn
                 ( "*",
                   [ Term (Notn ("^", [ Term (Ident "y"); Term (Ident "z") ])); Term (Ident "w") ]
                 ));
          ] ))

let () =
  assert (
    parse arith "x * y ^ z + w"
    = Notn
        ( "+",
          [
            Term
              (Notn
                 ( "*",
                   [ Term (Ident "x"); Term (Notn ("^", [ Term (Ident "y"); Term (Ident "z") ])) ]
                 ));
            Term (Ident "w");
          ] ))

let () = assert (parse arith "(x)" = Notn ("()", [ Term (Ident "x") ]))

let () =
  assert (
    parse arith "(x+y)" = Notn ("()", [ Term (Notn ("+", [ Term (Ident "x"); Term (Ident "y") ])) ]))

let () =
  assert (
    parse arith "x + (y+z)"
    = Notn
        ( "+",
          [
            Term (Ident "x");
            Term (Notn ("()", [ Term (Notn ("+", [ Term (Ident "y"); Term (Ident "z") ])) ]));
          ] ))

let () = assert (parse arith "x y" = App (Ident "x", Ident "y"))
let () = assert (parse arith "x (y)" = App (Ident "x", Notn ("()", [ Term (Ident "y") ])))
let () = assert (parse arith "(x) y" = App (Notn ("()", [ Term (Ident "x") ]), Ident "y"))

let () =
  assert (parse arith "x y + z" = Notn ("+", [ Term (App (Ident "x", Ident "y")); Term (Ident "z") ]))

let () =
  assert (parse arith "x + y z" = Notn ("+", [ Term (Ident "x"); Term (App (Ident "y", Ident "z")) ]))

let () = assert (parse arith "x y z" = App (App (Ident "x", Ident "y"), Ident "z"))

let () =
  assert (parse arith "x (y z)" = App (Ident "x", Notn ("()", [ Term (App (Ident "y", Ident "z")) ])))

let () =
  assert (
    parse arith "x + (v (y + z) * w) u"
    = Notn
        ( "+",
          [
            Term (Ident "x");
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
                                       ( Ident "v",
                                         Notn
                                           ( "()",
                                             [
                                               Term
                                                 (Notn ("+", [ Term (Ident "y"); Term (Ident "z") ]));
                                             ] ) ));
                                  Term (Ident "w");
                                ] ));
                       ] ),
                   Ident "u" ));
          ] ))

let () = assert (parse arith "a. b c" = App (App (Constr "a", Ident "b"), Ident "c"))
let () = assert (parse arith "a .b c" = App (App (Ident "a", Field "b"), Ident "c"))

(* Parsing the church numeral 500, or even 1000, takes a near-negligible amount of time.  I think it helps that we have minimized backtracking. *)
let rec cnat n = if n <= 0 then "x" else "(f " ^ cnat (n - 1) ^ ")"
let _ = parse arith (cnat 500)
