open Testutil.Mcp

let uu, _ = synth "Type"
let aa = assume "A" uu
let a = assume "a" aa
let ida, _ = synth "let id ≔ ((x ↦ x) : A → A) in id a"
let () = equal ida a
let ida', _ = synth "let id : A → A ≔ x ↦ x in id a"
let () = equal ida' a
let a' = assume "a'" aa
let constaa, _ = synth "let id : A → A ≔ x ↦ a' in id a"
let () = unequal constaa a

(* ap on let *)
let c = assume "a''" (check "Id A a a'" uu)
let c', _ = synth "refl ((y ↦ let id : A → A ≔ x ↦ x in id y) : A → A) a a' a''"
let () = equal c c'

(* let affects typechecking *)
let bb = assume "B" (check "A → Type" uu)
let z = assume "z" (check "B a" uu)
let f = assume "f" (check "(x:A) → B x → B x" uu)
let z' = check "let x ≔ a in f x z" (check "B a" uu)
let () = uncheck "((x ↦ f x z) : A → B a) a" (check "B a" uu)
