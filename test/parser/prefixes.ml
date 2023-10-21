open Testutil
open Showparse
open Parser
open Notations
open Builtins

(* We define a nonassociative prefix notation @ of tightness +∞, the same tightness as function application. *)
let att =
  make ~name:"@" ~tightness:Float.infinity ~left:Closed ~right:Open ~assoc:Non ~tree:(fun n ->
      eop (Op "@") (Done n))

(* And also postfix notations ! and ? of tightness +∞, one left-associative and one not. *)
let bang =
  make ~name:"!" ~tightness:Float.infinity ~left:Open ~right:Closed ~assoc:Non ~tree:(fun n ->
      eop (Op "!") (Done n))

let query =
  make ~name:"?" ~tightness:Float.infinity ~left:Open ~right:Closed ~assoc:Left ~tree:(fun n ->
      eop (Op "?") (Done n))

let prefixes = !builtins |> State.add att |> State.add bang |> State.add query

(* Plain application *)
let () = assert (parse prefixes "@ f" = Notn ("@", [ Term (Name "f") ]))

(* Since function application is "left-associative" and @ has the same tightness, "@ f x"  is parsed as "(@ f) x".  Since @ is not right-associative, function application can't appear in *its* argument, so "@ (f x)" is not a possible parse. *)
let () = assert (parse prefixes "@ f x" = App (Notn ("@", [ Term (Name "f") ]), Name "x"))

(* Since @ is a prefix notation, it can appear anywhere as an argument, so "f @ x" is parsed as "f (@ x)". *)
let () = assert (parse prefixes "f @ x" = App (Name "f", Notn ("@", [ Term (Name "x") ])))

(* For the same reasons, "@ f @ x" is parsed as "(@ f) (@ x)". *)
let () =
  assert (
    parse prefixes "@ f @ x" = App (Notn ("@", [ Term (Name "f") ]), Notn ("@", [ Term (Name "x") ])))

(* Of course we can parenthesize its argument. *)
let () =
  assert (
    parse prefixes "@ (f x)"
    = Notn ("@", [ Term (Notn ("()", [ Flag Explicit_pi; Term (App (Name "f", Name "x")) ])) ]))

(* And again, since @ is a prefix notation, it can appear anyhere on the right, including inside itself. *)
let () = assert (parse prefixes "@ @ x" = Notn ("@", [ Term (Notn ("@", [ Term (Name "x") ])) ]))

(* Same for field projections, which are literally parsed as applications (and compiled later to something else) *)
let () = assert (parse prefixes "@ f .x" = App (Notn ("@", [ Term (Name "f") ]), Field "x"))

let unparse str =
  Core.Reporter.run ~emit:(fun _ -> ()) ~fatal:(fun _ -> ()) @@ fun () ->
  let _ = parse prefixes str in
  raise (Failure "Unexpected parse success")

(* But we can't apply @ *to* a field projection, since that's not a valid term on its own. *)
let () = unparse "f @ .x"

(* Now we experiment with the postfix ones *)
let () = assert (parse prefixes "x !" = Notn ("!", [ Term (Name "x") ]))
let () = assert (parse prefixes "x ?" = Notn ("?", [ Term (Name "x") ]))
let () = assert (parse prefixes "f x ?" = Notn ("?", [ Term (App (Name "f", Name "x")) ]))

(* It's not possible to get "f x !" to parse as "f (x !)", since function application is not right-associative and nothing is strictly tighter than it. *)
let () = unparse "f x !"

(* Now we try the operator in the middle.  This works since function application is left-associative. *)
let () = assert (parse prefixes "f ! x" = App (Notn ("!", [ Term (Name "f") ]), Name "x"))
let () = assert (parse prefixes "f ? x" = App (Notn ("?", [ Term (Name "f") ]), Name "x"))

let () =
  assert (
    parse prefixes "f ? x ?" = Notn ("?", [ Term (App (Notn ("?", [ Term (Name "f") ]), Name "x")) ]))
