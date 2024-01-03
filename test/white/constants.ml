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
  def "zero_zero" "ℕ × ℕ" "( zero, zero )";
  equal_at "zero_zero .fst" "zero" "ℕ";
  equal_at "zero_zero .snd" "zero" "ℕ";
  assume "A" "Type";
  assume "B" "A → Type";
  assume "a" "A";
  assume "b" "B a";
  def "ab" "(x:A) × B x" "(fst ≔ a, snd ≔ b)";
  equal_at "ab .fst" "a" "A";
  equal_at "ab .snd" "b" "B a";
  (match Hashtbl.find Global.constants (Option.get (Scope.lookup [ "ab" ])) with
  | Defined _ -> ()
  | _ -> raise (Failure "pair wasn't defined to be a tree"));
  def "zero_zero'" "ℕ × ℕ" "( fst ≔ zero , snd ≔ zero )";
  equal_at "zero_zero" "zero_zero'" "ℕ × ℕ";

  (* Pi-types *)
  (* These are built in, of course, but we also have a named constant for them. *)
  Types.Pi.install ();
  equal_at "(x:A) → B x" "Π A B" "Type";

  (* In particular, this gives a way for the user to write higher-dimensional Π-types. *)
  equal_at "refl ((x:A) → B x)" "refl Π A A (refl A) B B (refl B)"
    "Id Type ((x:A) → B x) ((x:A) → B x)";

  (* Coinductive streams *)
  Types.Stream.install ();
  def "zeros" "Stream ℕ" "[ .head ↦ zero | .tail ↦ zeros ]";
  equal_at "zeros .head" "zero" "ℕ";
  equal_at "zeros .tail .head" "zero" "ℕ";
  equal_at "zeros .tail .tail .head" "zero" "ℕ";
  equal_at "zeros .tail .tail .tail .head" "zero" "ℕ";
  def "nats" "ℕ → Stream ℕ" "n ↦ [ .head ↦ n | .tail ↦ nats (plus n one) ]";
  equal_at "nats zero .tail .tail .head" "two" "ℕ";
  equal_at "nats zero .tail .tail .tail .tail .head" "four" "ℕ";

  (* Bisimulation *)
  def "∞eta" "Stream A → Stream A" "s ↦ [ .head ↦ s .head | .tail ↦ ∞eta (s .tail) ]";
  unequal_at "s ↦ s" "s ↦ ∞eta s" "Stream A → Stream A";
  def "∞eta_bisim" "(s:Stream A) → Id (Stream A) s (∞eta s)"
    "s ↦ [ .head ↦ refl (s .head) | .tail ↦ ∞eta_bisim (s .tail) ]";

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
    | zero. ↦ n
    | suc. m ↦ suc. (lplus m n)
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
    | zero. ↦ suc. zero.
    | suc. n ↦ exp m n * m
    ]";
  equal_at "exp 3 2" "9" "N";
  def "exp2" "N → N → N" "m ↦ [ zero. ↦ suc. zero. | suc. n ↦ exp m n * m ]";
  equal_at "exp2 2 3" "8" "N";

  (* Empty type *)
  Types.Empty.install ();
  def "abort1" "(A:Type) → ∅ → A" "A ↦ [ ]";
  def "abort2" "(A:Type) → ∅ → A" "A ↦ [|]";
  def "abort3" "(A:Type) → ∅ → A" "A x ↦ [ x | ]";
  def "abort4" "(A:Type) → ∅ → A" "A x ↦ [ x ]";

  (* Higher-dimensional lambdas in case trees.  This simple version doesn't actually need them, as it could be just an ordinary higher-dimensional lambda term at a leaf. *)
  assume "f" "(x:A)→B x";
  def "reflf" "Id ((x:A)→B x) f f" "x₀ x₁ x₂ ↦ refl f x₀ x₁ x₂";
  def "reflf_eq_reflf" "Id (Id ((x:A)→B x) f f) reflf (refl f)" "refl (refl f)";
  (* To test that we actually allow higher-dimensional lambdas in case trees, we need to do some case-tree-only thing inside the lambda, like a match. *)
  def "refl_abort_f" "∅ → Id ((x:A)→B x) f f" "e x₀ x₁ x₂ ↦ [ e | ]";
  def "refl_nat_f" "N → Id ((x:A)→B x) f f"
    "n x₀ x₁ x₂ ↦ [ n | zero. ↦ refl f x₀ x₁ x₂ | suc. _ ↦ refl f x₀ x₁ x₂ ]";
  def "refl_nat_f_eq_reflf" "Id (Id ((x:A)→B x) f f) (refl_nat_f zero.) (refl f)" "refl (refl f)";

  (* We also test cube variable abstraction syntax *)
  def "refl_abort_f_cube" "∅ → Id ((x:A)→B x) f f" "e x ⤇ [ e | ]";
  def "refl_nat_f_cube" "N → Id ((x:A)→B x) f f"
    "n x ⤇ [ n | zero. ↦ refl f x.0 x.1 x.2 | suc. _ ↦ refl f x.0 x.1 x.2 ]";
  (* These are actually *unequal* because definition by case trees is generative. *)
  unequal_at "refl_nat_f" "refl_nat_f_cube" "N → Id ((x:A)→B x) f f";
  (* But they become equal when evaluated at concrete numbers so that the case trees compute away. *)
  equal_at "refl_nat_f 3" "refl_nat_f_cube 3" "Id ((x:A)→B x) f f";

  (* Higher-dimensional matches *)
  def "foo" "(x y : N) → Id N x y → N" "x y p ↦ [ p | zero. ↦ 0 | suc. n ↦ 1 ]";
  def "bar" "(x y : N) → Id N x y → N" "x y ↦ [ zero. ↦ zero. | suc. p ↦ p.0 ]";
  equal_at "bar 1 1 (refl (1:N))" "0" "N";
  equal_at "bar 2 2 (refl (2:N))" "1" "N";
  def "prec" "N → N" "[ zero. ↦ zero. | suc. n ↦ n ]";
  def "idnat" "(x y : N) → Id N x y → Id N x y" "x y ↦ [ zero. ↦ zero. | suc. p ↦ suc. p ]";
  def "apprec" "(x y : N) → Id N x y → Id N (prec x) (prec y)"
    "x y p ↦ [ p | zero. ↦ zero. | suc. p ↦ p ]";
  Types.Unit.install ();
  def "code" "N → N → Type"
    "[ zero. ↦ [ zero. ↦ ⊤
                | suc. _ ↦ ∅ ]
     | suc. m ↦ [ zero. ↦ ∅
                 | suc. n ↦ code m n ] ]";
  def "rcode" "(x:N) → code x x" "[ zero. ↦ () | suc. n ↦ rcode n ]";
  def "encode" "(x y : N) → Id N x y → code x y"
    "x y ↦ [ zero. ↦ ()
            | suc. p ↦ encode p.0 p.1 p.2 ]";
  def "decode" "(x y : N) → code x y → Id N x y"
    "[ zero. ↦ [ zero. ↦ _ ↦ zero.
                | suc. _ ↦ [ ] ]
     | suc. x ↦ [ zero. ↦ [ ]
                 | suc. y ↦ c ↦ suc. (decode x y c) ] ]";
  def "encode_decode" "(x y : N) (c : code x y) → Id (code x y) (encode x y (decode x y c)) c"
    "[ zero. ↦ [ zero. ↦ _ ↦ ()
                | suc. _ ↦ [ ] ]
     | suc. x ↦ [ zero. ↦ [ ]
                 | suc. y ↦ c ↦ encode_decode x y c ] ]";
  def "decode_encode" "(x y : N) (p : Id N x y) → Id (Id N x y) (decode x y (encode x y p)) p"
    "x y ↦ [ zero. ↦ zero.
            | suc. p ↦ suc. (decode_encode p.0 p.1 p.2) ]";

  (* Matching on a boundary of a cube variable. *)
  def "mtchbd0" "(e:∅) (f : N → N) → Id (N → N) f f"
    "e f n ⤇ [ n.0 | zero. ↦ [ e ] | suc. _ ↦ [ e ] ]";

  def "mtchbd0'" "(e:∅) (f : N → N) → Id (N → N) f f"
    "e f n ⤇ [ n.0 | zero. ↦ [ e ] | suc. _ ↦ refl f n.0 n.1 n.2 ]";

  def "mtchbd0''" "(e:∅) (f : N → N) → Id (N → N) f f"
    "e f n0 n1 n2 ↦ [ n0 | zero. ↦ [e] | suc. _ ↦ refl f n0 n1 n2 ]";
  ()
