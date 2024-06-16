open Util
open Parser
open Notation
open Testutil
open Repl

let () =
  run @@ fun () ->
  assume "A" "Type";
  assume "foo" "A → A → A";
  let foo = Option.get (Scope.lookup [ "foo" ]) in
  let _ =
    State.Current.add_user "amp" (Infix No.zero)
      [ `Var ("x", `Nobreak, []); `Op (Op "&", `Break, []); `Var ("y", `None, []) ]
      (`Constant foo) [ "y"; "x" ] in
  assume "a" "A";
  assume "b" "A";
  equal_at "foo a b" "b & a" "A";
  print "b & a";
  ()
