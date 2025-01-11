open Testutil.Print

let () =
  run @@ fun () ->
  Parser.Printconfig.Reader.run
    ~env:{ Parser.Printconfig.default with style = `Noncompact; state = `Case }
  @@ fun () ->
  reformat "f x ` hello\n` goodbye\n y z";
  reformat "f x {` hello `}\n` goodbye\n y z";
  reformat "f x {` hello\nworld `}\n` goodbye\n y z";
  reformat "f x \n` hello\n y z";
  reformat "f x\n y z";
  reformat "f x\n\n y z";
  reformat "(x ` variable\n : A) ` first arg\n -> B `second arg\n -> C";
  reformat "(x : A) ` first arg\n -> B `second arg\n -> C";
  reformat "(x : A) -> B `second arg\n -> C";
  (* TODO: Some things after a comment have an extra indent, because the forced newline at the end of the comment replaces what would otherwise have been a breaking space. *)
  reformat
    "(x : A) -> B `second arg\n -> C -> C -> C -> C -> C -> C -> C -> C -> C -> C -> C -> C -> C -> C -> C -> C -> C -> C -> C -> C "
