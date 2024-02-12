open Testutil.Repl

let () =
  run @@ fun () ->
  assume "A" "Type";
  assume "B" "A -> Type";
  assume "a0" "A";
  assume "a1" "A";
  assume "a2" "Id A a0 a1";
  assume "b0" "B a0";
  assume "b1" "B a1";
  assume "b2" "refl B a0 a1 a2 b0 b1"
