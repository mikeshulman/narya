open Util
open Parser
open Postprocess
open Core
open Syntax
open Reporter
open Notation
open Print
open Format
open Testutil
open Repl

let () =
  run @@ fun () ->
  assume "A" "Type";
  assume "foo" "A → A → A";
  let foo = Option.get (Scope.lookup [ "foo" ]) in
  let amp = make "amp" (Infix No.zero) in
  set_tree amp (Open_entry (eop (Op "&") (done_open amp)));
  set_processor amp
    {
      process =
        (fun ctx obs loc _ ->
          match obs with
          | [ Term x; Term y ] ->
              let x = process ctx x in
              let y = process ctx y in
              {
                value = Raw.Synth (App ({ value = App ({ value = Const foo; loc }, y); loc }, x));
                loc;
              }
          | _ -> fatal (Anomaly "invalid notation arguments for amp"));
    };
  set_print amp (fun space ppf obs ws ->
      match obs with
      | [ x; y ] ->
          let wstimes, ws = take (Op "*") ws in
          taken_last ws;
          pp_open_hovbox ppf 2;
          if true then (
            pp_term `Break ppf x;
            pp_tok ppf (Op "&");
            pp_ws `Nobreak ppf wstimes;
            pp_term `None ppf y);
          pp_close_box ppf ();
          pp_space ppf space
      | _ -> fatal (Anomaly "invalid notation arguments for amp"));
  State.Current.add_with_print (`Constant foo)
    { notn = Wrap amp; pats = [ "x"; "y" ]; vals = [ "y"; "x" ] };
  assume "a" "A";
  assume "b" "A";
  equal_at "foo a b" "b & a" "A";
  print "b & a";
  ()
