open Testutil.Print

let () =
  run @@ fun () ->
  Parser.Printconfig.Reader.run ~env:{ style = `Noncompact; state = `Case; chars = `Unicode }
  @@ fun () ->
  reformat "f x ` hello\n` goodbye\n y z";
  reformat "f x {` hello `}\n` goodbye\n y z";
  reformat "f x {` hello\nworld `}\n` goodbye\n y z";
  reformat "f x \n` hello\n y z";
  reformat "f x\n y z";
  reformat "f x\n\n y z"
