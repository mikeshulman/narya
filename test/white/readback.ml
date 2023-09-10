open Testutil.Mcp
open Dim
open Core

(* Because we haven't written a general way to make contexts into cocontexts, we do all our testing of readback in the empty context without "assume".  Thus we have a lot of abstractions. *)

let roundtrip tm ty = Norm.eval (Emp D.zero) (Readback.readback_at Coctx.empty tm ty)
let roundtrip_ok tm ty = equal_at tm (roundtrip tm ty) ty

(* The polymorphic identity *)
let idty, _ = synth "(X:Type) → X → X"
let id = check "_ x ↦ x" idty
(*
let () = roundtrip_ok id idty

(* Now some church numerals *)
let nat, _ = synth "(X:Type) → (X → X) → (X → X)"
let zero = check "_ f x ↦ x" nat
let () = roundtrip_ok zero nat
let one = check "_ f x ↦ f x" nat
let () = roundtrip_ok one nat
let two = check "_ f x ↦ f (f x)" nat
let () = roundtrip_ok two nat
let four = check "_ f x ↦ f (f (f (f x)))" nat
let () = roundtrip_ok four nat

(* And some pairs *)
let () = Types.Sigma.install ()
let swapty, _ = synth "(A B : Type) → Sig A (_ ↦ B) → Sig B (_ ↦ A)"
let swap = check "A B x ↦ (x .snd , x .fst)" swapty
let () = roundtrip_ok swap swapty

let assocty, _ =
  synth
    "(A:Type) (B:A→Type) (C:(x:A)→B x→Type) → Sig A (a ↦ Sig (B a) (C a)) → Sig (Sig A B) (x ↦ C (x .fst) (x .snd))"

let assoc = check "A B C w ↦ ((w .fst , w .snd .fst) , w .snd .snd)" assocty
let () = roundtrip_ok assoc assocty

(* And some reflexivity *)
let reflty, _ = synth "(X:Type) (x:X) → Id X x x"
let refl = check "X x ↦ refl x" reflty
let () = roundtrip_ok refl reflty

let apty, _ = synth "(A B : Type) (f : A → B) (a₀ a₁ : A) → Id A a₀ a₁ → Id B (f a₀) (f a₁)"

let ap = check "A B f a₀ a₁ a₂ ↦ refl f a₀ a₁ a₂" apty
let () = roundtrip_ok ap apty

(* And some instantiations *)
let iidty, _ = synth "(A:Type) (a₀ a₁ : A) → Type"
let iid = check "A a₀ a₁ ↦ Id A a₀ a₁" iidty
let () = roundtrip_ok iid iidty
*)
