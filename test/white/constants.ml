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

  ()
