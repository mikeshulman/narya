open Testutil
open Repl
open Core

let () =
  run @@ fun () ->
  (* Church numerals *)
  def "ℕ" "Type" "(A : Type) → (A → A) → (A → A)";
  def "zero" "ℕ" "A f x ↦ x";
  def "one" "ℕ" "A f x ↦ f x";
  def "two" "ℕ" "A f x ↦ f (f x)";
  def "three" "ℕ" "A f x ↦ f (f (f x))";
  def "four" "ℕ" "A f x ↦ f (f (f (f x)))";
  equal_at "one" "one" "ℕ";
  unequal_at "one" "zero" "ℕ";
  def "plus" "ℕ → ℕ → ℕ" "m n A f x ↦ m A f (n A f x)";
  equal_at "plus one one" "two" "ℕ";
  unequal_at "plus one two" "two" "ℕ";
  def "times" "ℕ → ℕ → ℕ" "m n A f x ↦ m A (n A f) x";
  equal_at "times two two" "four" "ℕ";

  (* Sigma-types *)
  Types.Sigma.install ();
  def "zero_zero" "ℕ × ℕ" "{ fst ≔ zero; snd ≔ zero }";
  equal_at "zero_zero .fst" "zero" "ℕ";
  equal_at "zero_zero .snd" "zero" "ℕ";
  assume "A" "Type";
  assume "B" "A → Type";
  assume "a" "A";
  assume "b" "B a";
  def "ab" "(x:A) × B x" "(a,b)";
  equal_at "ab .fst" "a" "A";
  equal_at "ab .snd" "b" "B a";
  (match Hashtbl.find Global.constants (Option.get (Scope.lookup "ab")) with
  | Defined _ -> ()
  | _ -> raise (Failure "pair wasn't defined to be a tree"));
  def "zero_zero'" "ℕ × ℕ" "{ .fst ↦ zero; .snd ↦ zero }";
  equal_at "zero_zero" "zero_zero'" "ℕ × ℕ";

  (* Coinductive streams *)
  Types.Stream.install ();
  def "zeros" "Stream ℕ" "{ head ≔ zero; tail ≔ zeros }";
  equal_at "zeros .head" "zero" "ℕ";
  equal_at "zeros .tail .head" "zero" "ℕ";
  equal_at "zeros .tail .tail .head" "zero" "ℕ";
  equal_at "zeros .tail .tail .tail .head" "zero" "ℕ";
  def "nats" "ℕ → Stream ℕ" "n ↦ { head ≔ n; tail ≔ nats (plus n one) }";
  equal_at "nats zero .tail .tail .head" "two" "ℕ";
  equal_at "nats zero .tail .tail .tail .tail .head" "four" "ℕ";

  (* Bisimulation *)
  def "∞eta" "Stream A → Stream A" "s ↦ { head ≔ s .head; tail ≔ ∞eta (s .tail) }";
  unequal_at "s ↦ s" "s ↦ ∞eta s" "Stream A → Stream A";
  def "∞eta_bisim" "(s:Stream A) → Id (Stream A) s (∞eta s)"
    "s ↦ { head ≔ refl (s .head); tail ≔ ∞eta_bisim (s .tail) }";

  (* Natural numbers *)
  Types.Nat.install ();

  (* Lists *)
  Types.Lst.install ();
  def "append" "(A:Type) -> List A -> List A -> List A"
    "A xs ys ↦ [ xs
      | nil.       ↦ ys
      | cons. x xs ↦ cons. x (append A xs ys)
      ]";
  equal_at "append N (cons. 0 nil.) (cons. 1 (cons. 2 nil.))" "cons. 0 (cons. 1 (cons. 2 nil.))"
    "List N";

  (* Vectors *)
  Types.Vec.install ();
  def "lplus" "N -> N -> N" "m n ↦ [ m
    | 0. ↦ n
    | 1. m ↦ 1. (lplus m n)
    ]";
  def "vappend" "(A:Type) (m n : N) -> Vec A m -> Vec A n -> Vec A (lplus m n)"
    "A m n xs ys ↦ [ xs
    | nil.         ↦ ys
    | cons. m x xs ↦ cons. (lplus m n) x (vappend A m n xs ys)
    | ]";
  equal_at "vappend N 1 2 (cons. 0 0 nil.) (cons. 1 1 (cons. 0 2 nil.))"
    "cons. 2 0 (cons. 1 1 (cons. 0 2 nil.))" "Vec N 3";

  (* Matching lambda *)
  def "exp" "N → N → N" "m ↦ [
    | 0. ↦ 1. 0.
    | 1. n ↦ exp m n * m
    ]";
  equal_at "exp 3 2" "9" "N";
  def "exp2" "N → N → N" "m ↦ [ 0. ↦ 1. 0. | 1. n ↦ exp m n * m ]";
  equal_at "exp2 2 3" "8" "N";

  (* Empty type *)
  Types.Empty.install ();
  def "abort1" "(A:Type) → ∅ → A" "A ↦ [ ]";
  def "abort2" "(A:Type) → ∅ → A" "A ↦ [|]";
  def "abort3" "(A:Type) → ∅ → A" "A x ↦ [ x | ]";

  (* Higher-dimensional lambdas in case trees.  This simple version doesn't actually need them, as it could be just an ordinary higher-dimensional lambda term at a leaf. *)
  assume "f" "(x:A)→B x";
  def "reflf" "Id ((x:A)→B x) f f" "x₀ x₁ x₂ ↦ refl f x₀ x₁ x₂";
  def "reflf_eq_reflf" "Id (Id ((x:A)→B x) f f) reflf (refl f)" "refl (refl f)";
  (* To test that we actually allow higher-dimensional lambdas in case trees, we need to do some case-tree-only thing inside the lambda, like a match. *)
  def "refl_abort_f" "∅ → Id ((x:A)→B x) f f" "e x₀ x₁ x₂ ↦ [ e | ]";
  def "refl_nat_f" "N → Id ((x:A)→B x) f f"
    "n x₀ x₁ x₂ ↦ [ n | 0. ↦ refl f x₀ x₁ x₂ | 1. _ ↦ refl f x₀ x₁ x₂ ]";
  def "refl_nat_f_eq_reflf" "Id (Id ((x:A)→B x) f f) (refl_nat_f 0.) (refl f)" "refl (refl f)";

  (* Higher-dimensional matches *)
  def "foo" "(x y : N) → Id N x y → N" "x y p ↦ [ p | 0. ↦ 0 | 1. n ↦ 1 ]";
  def "bar" "(x y : N) → Id N x y → N" "x y ↦ [ 0. ↦ 0. | 1. p ↦ p .0 ]";
  equal_at "bar 1 1 (refl (1:N))" "0" "N";
  equal_at "bar 2 2 (refl (2:N))" "1" "N";
  def "prec" "N → N" "[ 0. ↦ 0. | 1. n ↦ n ]";
  def "idnat" "(x y : N) → Id N x y → Id N x y" "x y ↦ [ 0. ↦ 0. | 1. p ↦ 1. p ]";
  def "apprec" "(x y : N) → Id N x y → Id N (prec x) (prec y)" "x y p ↦ [ p | 0. ↦ 0. | 1. p ↦ p ]";
  Types.Unit.install ();
  def "code" "N → N → Type" "[ 0. ↦ [ 0. ↦ ⊤ | 1. _ ↦ ∅ ] | 1. m ↦ [ 0. ↦ ∅ | 1. n ↦ code m n ] ]";
  def "rcode" "(x:N) → code x x" "[ 0. ↦ {} | 1. n ↦ rcode n ]";
  def "encode" "(x y : N) → Id N x y → code x y"
    "x y ↦ [ 0. ↦ {} | 1. p ↦ encode (p .0) (p .1) (p .2) ]";
  def "decode" "(x y : N) → code x y → Id N x y"
    "[ 0. ↦ [ 0. ↦ _ ↦ 0.
             | 1. _ ↦ [ ] ]
     | 1. x ↦ [ 0. ↦ [ ]
               | 1. y ↦ c ↦ 1. (decode x y c) ] ]";
  def "encode_decode" "(x y : N) (c : code x y) → Id (code x y) (encode x y (decode x y c)) c"
    "[ 0. ↦ [ 0. ↦ _ ↦ {}
             | 1. _ ↦ [ ] ]
     | 1. x ↦ [ 0. ↦ [ ]
               | 1. y ↦ c ↦ encode_decode x y c ] ]";
  def "decode_encode" "(x y : N) (p : Id N x y) → Id (Id N x y) (decode x y (encode x y p)) p"
    "x y ↦ [ 0. ↦ 0.
            | 1. p ↦ 1. (decode_encode (p .0) (p .1) (p .2)) ]";
  ()
