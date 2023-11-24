open Util
open Core
open Parser
open Notation
open Testutil
open Showparse

(* We raise an error if one notation is a prefix of another, since parsing such combinations would require too much backtracking.  Here we test the generation of that error. *)

let ifthen = make "ifthen" Prefixr No.zero
let () = set_tree ifthen (eop (Ident "if") (term (Ident "then") (Done ifthen)))
let ifthen_only = State.empty |> State.add ifthen
let ifthenelse = make "ifthenelse" Prefixr No.zero

let () =
  set_tree ifthenelse
    (eop (Ident "if") (term (Ident "then") (term (Ident "else") (Done ifthenelse))))

let ifthenelse_only = State.empty |> State.add ifthenelse
let both = State.empty |> State.add ifthen |> State.add ifthenelse

module Terminal = Asai.Tty.Make (Core.Reporter.Code)

let () =
  Reporter.run ~emit:Terminal.display ~fatal:(fun d ->
      Terminal.display d;
      raise (Failure "Parse failure"))
  @@ fun () ->
  assert (parse ifthen_only "if x then y" = Notn ("ifthen", [ Term (Ident "x"); Term (Ident "y") ]));
  assert (
    parse ifthenelse_only "if x then y else z"
    = Notn ("ifthenelse", [ Term (Ident "x"); Term (Ident "y"); Term (Ident "z") ]))

let () =
  Reporter.run ~emit:Terminal.display ~fatal:(fun d ->
      if d.message = Parsing_ambiguity "One notation is a prefix of another" then ()
      else (
        Terminal.display d;
        raise (Failure "Unexpected error code")))
  @@ fun () ->
  assert (parse both "if x then y" = Notn ("ifthen", [ Term (Ident "x"); Term (Ident "y") ]))

(* However, it does work to have two distinct notations that share a common prefix, as long as both of them extend that prefix nontrivially.  (This is the whole point of merging notation trees.) *)

let ifthenelif = make "ifthenelif" Prefixr No.zero

let () =
  set_tree ifthenelif
    (eop (Ident "if") (term (Ident "then") (term (Ident "elif") (Done ifthenelif))))

let better_both = State.empty |> State.add ifthenelse |> State.add ifthenelif

let () =
  Reporter.run ~emit:Terminal.display ~fatal:(fun d ->
      Terminal.display d;
      raise (Failure "Parse failure"))
  @@ fun () ->
  assert (
    parse better_both "if x then y else z"
    = Notn ("ifthenelse", [ Term (Ident "x"); Term (Ident "y"); Term (Ident "z") ]));
  assert (
    parse better_both "if x then y elif z"
    = Notn ("ifthenelif", [ Term (Ident "x"); Term (Ident "y"); Term (Ident "z") ]))
