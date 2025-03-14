open Util
open Core
open Parser
open Notation
open Testutil
open Showparse
open Parseonly

(* We raise an error if one notation is a prefix of another, since parsing such combinations would require too much backtracking.  Here we test the generation of that error. *)

type (_, _, _) identity +=
  | Ifthen : (closed, No.zero, No.nonstrict opn) identity
  | Ifthenelse : (closed, No.zero, No.nonstrict opn) identity
  | Ifthenelif : (closed, No.zero, No.nonstrict opn) identity

let ifthen : (closed, No.zero, No.nonstrict opn) notation = (Ifthen, Prefixr No.zero)

let () =
  make ifthen "ifthen"
    (Closed_entry (eop (Ident [ "if" ]) (term (Ident [ "then" ]) (Done_closed ifthen))))

let ifthenelse : (closed, No.zero, No.nonstrict opn) notation = (Ifthenelse, Prefixr No.zero)

let () =
  make ifthenelse "ifthenelse"
    (Closed_entry
       (eop (Ident [ "if" ])
          (term (Ident [ "then" ]) (term (Ident [ "else" ]) (Done_closed ifthenelse)))))

let () =
  Parser.Lexer.Specials.run @@ fun () ->
  Reporter.run ~emit:Reporter.display ~fatal:(fun d ->
      Reporter.display d;
      raise (Failure "Parse failure"))
  @@ fun () ->
  Situation.run_on Situation.empty @@ fun () ->
  Situation.Current.add ifthen;
  assert (parse "if x then y" = Notn ("ifthen", [ Term (Ident [ "x" ]); Term (Ident [ "y" ]) ]))

let () =
  Parser.Lexer.Specials.run @@ fun () ->
  Reporter.run ~emit:Reporter.display ~fatal:(fun d ->
      Reporter.display d;
      raise (Failure "Parse failure"))
  @@ fun () ->
  Situation.run_on Situation.empty @@ fun () ->
  Situation.Current.add ifthenelse;
  assert (
    parse "if x then y else z"
    = Notn ("ifthenelse", [ Term (Ident [ "x" ]); Term (Ident [ "y" ]); Term (Ident [ "z" ]) ]))

let () =
  Parser.Lexer.Specials.run @@ fun () ->
  Reporter.run ~emit:Reporter.display ~fatal:(fun d ->
      if
        d.message
        = Parsing_ambiguity "One notation is a prefix of another: [ifthen] and [ifthenelse]"
      then ()
      else (
        Reporter.display d;
        raise (Failure "Unexpected error code")))
  @@ fun () ->
  Situation.run_on Situation.empty @@ fun () ->
  Situation.Current.add ifthen;
  Situation.Current.add ifthenelse;
  assert (parse "if x then y" = Notn ("ifthen", [ Term (Ident [ "x" ]); Term (Ident [ "y" ]) ]))

(* However, it does work to have two distinct notations that share a common prefix, as long as both of them extend that prefix nontrivially.  (This is the whole point of merging notation trees.) *)

let ifthenelif : (closed, No.zero, No.nonstrict opn) notation = (Ifthenelif, Prefixr No.zero)

let () =
  make ifthenelif "ifthenelif"
    (Closed_entry
       (eop (Ident [ "if" ])
          (term (Ident [ "then" ]) (term (Ident [ "elif" ]) (Done_closed ifthenelif)))))

let () =
  Parser.Lexer.Specials.run @@ fun () ->
  Reporter.run ~emit:Reporter.display ~fatal:(fun d ->
      Reporter.display d;
      raise (Failure "Parse failure"))
  @@ fun () ->
  Situation.run_on Situation.empty @@ fun () ->
  Situation.Current.add ifthenelse;
  Situation.Current.add ifthenelif;
  assert (
    parse "if x then y else z"
    = Notn ("ifthenelse", [ Term (Ident [ "x" ]); Term (Ident [ "y" ]); Term (Ident [ "z" ]) ]));
  assert (
    parse "if x then y elif z"
    = Notn ("ifthenelif", [ Term (Ident [ "x" ]); Term (Ident [ "y" ]); Term (Ident [ "z" ]) ]))
