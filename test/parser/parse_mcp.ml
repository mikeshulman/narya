open Testutil.Mcp

let () =
  Parser.Unparse.install ();
  run @@ fun () ->
  let uu, _ = synth "Type" in
  let aa = assume "A" uu in
  let atou, _ = synth "A → Type" in
  let bb = assume "B" atou in
  let atob, _ = synth "(x : A) → B x" in
  let f = assume "f" atob in
  let () = unequal atou atob in
  let () = equal f f in
  let abtou, _ = synth "(x:A)→ B x → Type" in
  let cc = assume "C" abtou in
  let abtoc, _ = synth "(x:A)→(y:B x)→C x y" in

  let g = assume "g" abtoc in
  let a0 = assume "a₀" aa in
  let a1 = assume "a₁" aa in
  let ida01, _ = synth "Id A a₀ a₁" in
  let ida01', _ = synth "refl A a₀ a₁" in
  let () = equal ida01 ida01' in
  let a2 = assume "a₂" ida01 in
  let fa2, fa2ty = synth "refl f a₀ a₁ a₂" in
  let fa2ty', _ = synth "refl B a₀ a₁ a₂ (f a₀) (f a₁)" in
  let () = equal fa2ty fa2ty' in
  let f' = check "x ↦ f x" atob in
  let () = equal_at f f' atob in
  let f'', _ = synth "(x ↦ f x) : (x:A)→ B x" in
  let () = equal_at f f'' atob in

  (* Cubes *)
  let xx = assume "X" uu in
  let x00 = assume "x00" xx in
  let x01 = assume "x01" xx in
  let xx02, _ = synth "Id X x00 x01" in
  let x02 = assume "x02" xx02 in
  let x10 = assume "x10" xx in
  let x11 = assume "x11" xx in
  let xx12, _ = synth "Id X x10 x11" in
  let x12 = assume "x12" xx12 in
  let xx20, _ = synth "Id X x00 x10" in
  let xx21, _ = synth "Id X x01 x11" in
  let x20 = assume "x20" xx20 in
  let x21 = assume "x21" xx21 in
  let xx22, _ = synth "refl (refl X) x00 x01 x02 x10 x11 x12 x20 x21" in
  let x22 = assume "x22" xx22 in
  let sx22, sx22ty = synth "sym x22" in
  let sx22ty', _ = synth "refl (refl X) x00 x10 x20 x01 x11 x21 x02 x12" in
  let () = equal sx22ty sx22ty' in

  (* Applied ascriptions *)
  let ida = check "((x ↦ x) : A → A) a₀" aa in
  let () = equal ida a0 in

  (* Check for the ambiguity bug. *)
  let _ = synth "(A:Type) → (A:Type) → A" in

  (* Efficiency *)
  let churchnat, _ = synth "(X:Type) → (X → X) → (X → X)" in

  let cnat n =
    let rec cnat n = if n <= 0 then "x" else "(f " ^ cnat (n - 1) ^ ")" in
    "X f x ↦ " ^ cnat n in

  (* This is near instantaneous. *)
  let fifty = check (cnat 50) churchnat in

  (* Doing 100 takes a noticeable fraction of a second, but only in the typechecking; the parsing is still near instantaneous. *)
  let cien = parse_term Emp (cnat 100) in

  (* Parsing church numerals starts to take a noticable fraction of a second around 2000. *)
  Testutil.Repl.def "Σ" "(A : Type) → (A → Type) → Type" "A B ↦ sig ( fst : A, snd : B fst)";
  let sigab, _ = synth "Σ A B" in
  let s = assume "s" sigab in
  let s1, s1ty = synth "s .fst" in
  let () = equal s1ty aa in
  let s2, s2ty = synth "s .snd" in
  let s2ty', _ = synth "B (s .fst)" in
  let () = equal s2ty s2ty' in
  let ba0, _ = synth "B a₀" in
  let b0 = assume "b₀" ba0 in
  let ab0 = check "( fst ≔ a₀, snd := b₀ )" sigab in
  let () = uncheck "( fst ≔ a₁, snd := b₀ )" sigab in
  let a0', _ = synth "(( fst ≔ a₀, snd ≔ b₀ ) : Σ A B) .fst" in
  let () = equal a0 a0' in
  let b0', _ = synth "((fst ≔ a₀, snd ≔ b₀ ) : Σ A B) .snd" in
  let () = equal b0 b0' in
  let ab0' = check "(a₀ , b₀)" sigab in
  let ab0'' = check "(_ ≔ a₀ , b₀)" sigab in
  let a0'', _ = synth "((a₀ , b₀) : Σ A B) .fst" in
  let () = equal a0 a0'' in

  (* 1-tuples *)
  Testutil.Repl.gel_install ();
  let rrty, _ = synth "A → X → Type" in
  let rr = assume "R" rrty in
  let r0ty, _ = synth "R a₀ x00" in
  let r0 = assume "r" r0ty in
  let ax, _ = synth "Gel A X R a₀ x00" in
  let rax = check "(ungel ≔ r)" ax in
  let rax' = check "(_ ≔ r)" ax in
  let () = uncheck "(r)" ax in

  (* Non-associativity of prod and comma *)
  let dd = assume "D" uu in
  let ee = assume "E" uu in
  let a = assume "a" aa in
  let d = assume "d" dd in
  let e = assume "e" ee in
  let aaddee, _ = synth "Σ A (_ ↦ Σ D (_ ↦ E))" in
  let aaddee', _ = synth "Σ (Σ A (_ ↦ D)) (_ ↦ E)" in
  let () = unequal aaddee aaddee' in
  let ade = check "(a , (d , e))" aaddee in
  let () = uncheck "(a , (d , e))" aaddee' in
  let () = uncheck "(a , d , e)" aaddee in

  (* Let's try some comments *)
  let _ = synth "(x : A) → ` a line comment
 B x" in

  let _ = synth "(x : A) {` a block comment `} →  B x" in

  let _ = synth "(x : A) {` a block comment
 spanning multiple
lines `}
  →  B x" in

  let _ =
    unparse
      "(x : A) {` a block comment
 containing ` a line comment
 and showing that {` block comments
nest `}
→  B x"
  in

  let _ =
    synth
      "(x : A) {` a block comment
 containing ` a line comment
 and showing that {` block `} comments
nest `}
→  B x"
  in

  (* Identifiers can start with digits, but not be only digits. *)
  let atoa, _ = synth "A → A" in
  let _ = check "0a ↦ 0a" atoa in
  let () = uncheck "0 ↦ 0" atoa in

  (* Local variables, constructors, and fields can't contain periods *)
  let () = unparse "x.x ↦ x.x" in
  let () = unparse "x .y.z" in
  let () = unparse "x.y. z" in
  let () = unparse "(x.x : A) → B x.x" in

  (* Generic degeneracies *)
  let ida00, _ = synth "Id A a₀ a₀" in
  let idb00, _ = synth "Id B a₀ a₀ (refl a₀) (f a₀) (f a₀)" in

  let () = equal_at (check "refl a₀" ida00) (check "a₀^(e)" ida00) ida00 in
  let () = equal_at (check "refl a₀" ida00) (check "a₀⁽ᵉ⁾" ida00) ida00 in

  (* Superscripts bind tighter than application: *)
  let () = equal_at (check "refl f a₀ a₀ (refl a₀)" idb00) (check "f⁽ᵉ⁾ a₀ a₀ a₀⁽ᵉ⁾" idb00) idb00 in
  let () =
    equal_at (check "refl f a₀ a₀ (refl a₀)" idb00) (check "f⁽ᵉ⁾ a₀ a₀ (a₀)⁽ᵉ⁾" idb00) idb00 in
  let () =
    equal_at (check "refl f a₀ a₀ (refl a₀)" idb00) (check "f⁽ᵉ⁾ a₀ a₀ (a₀⁽ᵉ⁾)" idb00) idb00 in
  let () =
    equal_at (check "refl f a₀ a₀ (refl a₀)" idb00) (check "f⁽ᵉ⁾ a₀ a₀ (a₀^(e))" idb00) idb00 in
  ()
