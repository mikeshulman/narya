open Testutil.Mcp
open Dim
open Core

(* For historical reasons, we do all our testing of readback in the empty context without "assume".  Thus we have a lot of abstractions. *)

let roundtrip tm ty = Norm.eval_term (Emp D.zero) (Readback.readback_at Ctx.empty tm ty)
let roundtrip_ok tm ty = equal_at tm (roundtrip tm ty) ty

(* The polymorphic identity *)
let () =
  run @@ fun () ->
  let idty, _ = synth "(X:Type) → X → X" in
  let id = check "_ x ↦ x" idty in
  roundtrip_ok id idty;

  (* Now some church numerals *)
  let nat, _ = synth "(X:Type) → (X → X) → (X → X)" in
  let zero = check "_ f x ↦ x" nat in
  roundtrip_ok zero nat;
  let one = check "_ f x ↦ f x" nat in
  roundtrip_ok one nat;
  let two = check "_ f x ↦ f (f x)" nat in
  roundtrip_ok two nat;
  let four = check "_ f x ↦ f (f (f (f x)))" nat in
  roundtrip_ok four nat;

  (* And some pairs *)
  Testutil.Repl.def "Σ" "(A : Type) → (A → Type) → Type" "A B ↦ sig ( fst : A, snd : B fst)";
  let swapty, _ = synth "(A B : Type) → Σ A (_ ↦ B) → Σ B (_ ↦ A)" in
  let swap = check "A B x ↦ (fst ≔ x .snd , snd ≔ x .fst)" swapty in
  roundtrip_ok swap swapty;

  let assocty, _ =
    synth
      "(A:Type) (B:A→Type) (C:(x:A)→B x→Type) → Σ A (a ↦ Σ (B a) (C a)) → Σ (Σ A B) (x ↦ C (x .fst) (x .snd))"
  in

  let assoc =
    check "A B C w ↦ (fst ≔ (fst ≔ w .fst , snd ≔ w .snd .fst) , snd ≔ w .snd .snd)" assocty in
  roundtrip_ok assoc assocty;

  (* And some reflexivity *)
  let reflty, _ = synth "(X:Type) (x:X) → Id X x x" in
  let refl = check "X x ↦ refl x" reflty in
  roundtrip_ok refl reflty;

  let apty, _ = synth "(A B : Type) (f : A → B) (a₀ a₁ : A) → Id A a₀ a₁ → Id B (f a₀) (f a₁)" in

  let ap = check "A B f a₀ a₁ a₂ ↦ refl f a₀ a₁ a₂" apty in
  roundtrip_ok ap apty;

  (* And some instantiations *)
  let iidty, _ = synth "(A:Type) (a₀ a₁ : A) → Type" in
  let iid = check "A a₀ a₁ ↦ Id A a₀ a₁" iidty in
  roundtrip_ok iid iidty;

  ()
