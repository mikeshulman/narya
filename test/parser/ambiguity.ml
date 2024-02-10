open Util
open Core
open Parser
open Notation
open Testutil
open Showparse
module Terminal = Asai.Tty.Make (Core.Reporter.Code)

(* We raise an error if one notation is a prefix of another, since parsing such combinations would require too much backtracking.  Here we test the generation of that error. *)

let ifthen = make "ifthen" (Prefixr No.zero)

let () =
  set_tree ifthen
    (Closed_entry (eop (Ident [ "if" ]) (term (Ident [ "then" ]) (Done_closed ifthen))))

let ifthenelse = make "ifthenelse" (Prefixr No.zero)

let () =
  set_tree ifthenelse
    (Closed_entry
       (eop (Ident [ "if" ])
          (term (Ident [ "then" ]) (term (Ident [ "else" ]) (Done_closed ifthenelse)))))

let () =
  Reporter.run ~emit:Terminal.display ~fatal:(fun d ->
      Terminal.display d;
      raise (Failure "Parse failure"))
  @@ fun () ->
  State.run_on State.empty @@ fun () ->
  State.Current.add ifthen;
  assert (parse "if x then y" = Notn ("ifthen", [ Term (Ident [ "x" ]); Term (Ident [ "y" ]) ]))

let () =
  Reporter.run ~emit:Terminal.display ~fatal:(fun d ->
      Terminal.display d;
      raise (Failure "Parse failure"))
  @@ fun () ->
  State.run_on State.empty @@ fun () ->
  State.Current.add ifthenelse;
  assert (
    parse "if x then y else z"
    = Notn ("ifthenelse", [ Term (Ident [ "x" ]); Term (Ident [ "y" ]); Term (Ident [ "z" ]) ]))

let () =
  Reporter.run ~emit:Terminal.display ~fatal:(fun d ->
      if
        d.message
        = Parsing_ambiguity "One notation is a prefix of another: [ifthen] and [ifthenelse]"
      then ()
      else (
        Terminal.display d;
        raise (Failure "Unexpected error code")))
  @@ fun () ->
  State.run_on State.empty @@ fun () ->
  State.Current.add ifthen;
  State.Current.add ifthenelse;
  assert (parse "if x then y" = Notn ("ifthen", [ Term (Ident [ "x" ]); Term (Ident [ "y" ]) ]))

(* However, it does work to have two distinct notations that share a common prefix, as long as both of them extend that prefix nontrivially.  (This is the whole point of merging notation trees.) *)

let ifthenelif = make "ifthenelif" (Prefixr No.zero)

let () =
  set_tree ifthenelif
    (Closed_entry
       (eop (Ident [ "if" ])
          (term (Ident [ "then" ]) (term (Ident [ "elif" ]) (Done_closed ifthenelif)))))

let () =
  Reporter.run ~emit:Terminal.display ~fatal:(fun d ->
      Terminal.display d;
      raise (Failure "Parse failure"))
  @@ fun () ->
  State.run_on State.empty @@ fun () ->
  State.Current.add ifthenelse;
  State.Current.add ifthenelif;
  assert (
    parse "if x then y else z"
    = Notn ("ifthenelse", [ Term (Ident [ "x" ]); Term (Ident [ "y" ]); Term (Ident [ "z" ]) ]));
  assert (
    parse "if x then y elif z"
    = Notn ("ifthenelif", [ Term (Ident [ "x" ]); Term (Ident [ "y" ]); Term (Ident [ "z" ]) ]))
