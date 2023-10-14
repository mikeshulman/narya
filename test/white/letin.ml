open Testutil.Mcp

let () =
  run @@ fun () ->
  let uu, _ = synth "Type" in
  let aa = assume "A" uu in
  let a = assume "a" aa in
  let ida, _ = synth "let id ≔ ((x ↦ x) : A → A) in id a" in
  let () = equal ida a in
  let ida', _ = synth "let id : A → A ≔ x ↦ x in id a" in
  let () = equal ida' a in
  let a' = assume "a'" aa in
  let constaa, _ = synth "let id : A → A ≔ x ↦ a' in id a" in
  let () = unequal constaa a in

  (* ap on let *)
  let c = assume "a''" (check "Id A a a'" uu) in
  let c', _ = synth "refl ((y ↦ let id : A → A ≔ x ↦ x in id y) : A → A) a a' a''" in
  let () = equal c c' in

  (* let affects typechecking *)
  let bb = assume "B" (check "A → Type" uu) in
  let z = assume "z" (check "B a" uu) in
  let f = assume "f" (check "(x:A) → B x → B x" uu) in
  let z' = check "let x ≔ a in f x z" (check "B a" uu) in
  let () = uncheck "((x ↦ f x z) : A → B a) a" (check "B a" uu) in
  ()
