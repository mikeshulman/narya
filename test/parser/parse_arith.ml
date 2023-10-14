open Testutil
open Showparse
open Arith

let () = assert (parse arith "x" = Name "x")
let () = assert (parse arith "x + y" = Notn ("+", [ Term (Name "x"); Term (Name "y") ]))

let () =
  assert (
    parse arith "x + y + z"
    = Notn ("+", [ Term (Notn ("+", [ Term (Name "x"); Term (Name "y") ])); Term (Name "z") ]))

let () =
  assert (
    parse arith "x ^ y ^ z"
    = Notn ("^", [ Term (Name "x"); Term (Notn ("^", [ Term (Name "y"); Term (Name "z") ])) ]))

let () =
  assert (
    parse arith "x * y + z"
    = Notn ("+", [ Term (Notn ("*", [ Term (Name "x"); Term (Name "y") ])); Term (Name "z") ]))

let () =
  assert (
    parse arith "x + y * z"
    = Notn ("+", [ Term (Name "x"); Term (Notn ("*", [ Term (Name "y"); Term (Name "z") ])) ]))

let () =
  assert (
    parse arith "x + y - z"
    = Notn ("-", [ Term (Notn ("+", [ Term (Name "x"); Term (Name "y") ])); Term (Name "z") ]))

let () =
  assert (
    parse arith "x - y + z"
    = Notn ("+", [ Term (Notn ("-", [ Term (Name "x"); Term (Name "y") ])); Term (Name "z") ]))

let () =
  assert (
    parse arith "x + y ^ z * w"
    = Notn
        ( "+",
          [
            Term (Name "x");
            Term
              (Notn
                 ("*", [ Term (Notn ("^", [ Term (Name "y"); Term (Name "z") ])); Term (Name "w") ]));
          ] ))

let () =
  assert (
    parse arith "x * y ^ z + w"
    = Notn
        ( "+",
          [
            Term
              (Notn
                 ("*", [ Term (Name "x"); Term (Notn ("^", [ Term (Name "y"); Term (Name "z") ])) ]));
            Term (Name "w");
          ] ))

let () = assert (parse arith "(x)" = Notn ("()", [ Term (Name "x") ]))

let () =
  assert (
    parse arith "(x+y)" = Notn ("()", [ Term (Notn ("+", [ Term (Name "x"); Term (Name "y") ])) ]))

let () =
  assert (
    parse arith "x + (y+z)"
    = Notn
        ( "+",
          [
            Term (Name "x");
            Term (Notn ("()", [ Term (Notn ("+", [ Term (Name "y"); Term (Name "z") ])) ]));
          ] ))

let () = assert (parse arith "x y" = App (Name "x", Name "y"))
let () = assert (parse arith "x (y)" = App (Name "x", Notn ("()", [ Term (Name "y") ])))
let () = assert (parse arith "(x) y" = App (Notn ("()", [ Term (Name "x") ]), Name "y"))

let () =
  assert (parse arith "x y + z" = Notn ("+", [ Term (App (Name "x", Name "y")); Term (Name "z") ]))

let () =
  assert (parse arith "x + y z" = Notn ("+", [ Term (Name "x"); Term (App (Name "y", Name "z")) ]))

let () = assert (parse arith "x y z" = App (App (Name "x", Name "y"), Name "z"))

let () =
  assert (parse arith "x (y z)" = App (Name "x", Notn ("()", [ Term (App (Name "y", Name "z")) ])))

let () =
  assert (
    parse arith "x + (v (y + z) * w) u"
    = Notn
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
          ] ))

let () = assert (parse arith "a. b c" = App (App (Constr "a", Name "b"), Name "c"))
let () = assert (parse arith "a .b c" = App (App (Name "a", Field "b"), Name "c"))

(* Parsing the church numeral 500, or even 1000, takes a near-negligible amount of time.  I think it helps that we have minimized backtracking. *)
let rec cnat n = if n <= 0 then "x" else "(f " ^ cnat (n - 1) ^ ")"
let _ = parse arith (cnat 500)
