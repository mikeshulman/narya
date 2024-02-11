open Testutil.Repl

let () =
  run @@ fun () ->
  Types.Stream.install ();
  assume "A" "Type";

  (* We suppose a stream and take some parts of it *)
  assume "s" "Stream A";
  def "s0" "A" "s .head";
  def "s0t" "Stream A" "s .tail";
  def "s1" "A" "s .tail .head";
  def "s2" "A" "s .tail .tail .head";

  (* With a non-corecursive copattern-match, we can define a one-step eta-expansion, and see that streams don't satisfy eta-conversion. *)
  def "s'" "Stream A" "[ .head ↦ s .head | .tail ↦ s .tail ]";
  unequal_at "s" "s'" "Stream A";

  (* Their identity/bridge types are bisimulations.  We can use this to prove propositional one-step eta-conversion. *)
  def "s_is_s'" "Id (Stream A) s s'" "[ .head ↦ refl (s .head) | .tail ↦ refl (s .tail) ]";

  (* We can also define the general corecursor 'corec' by copattern-matching. *)
  def "corec" "(A X : Type) → (X → A) → (X → X) → X → Stream A"
    "A X h t x ↦ [ .head ↦ h x | .tail ↦ corec A X h t (t x) ]";

  (* Using corec, we can also define an infinitary eta-expansion. *)
  def "s''" "Stream A" "corec A (Stream A) (x ↦ x .head) (x ↦ x .tail) s";
  unequal_at "s" "s''" "Stream A";

  (* We can't prove this with a non-corecursive copattern-match (since it's more than one step) or with "refl corec" (since it can only equate two values of corec).  We need a more general bisimulation, which must be defined by a full coinduction, which in turn requires a new operation defined by a higher-dimensional copattern case tree.  *)
  def "∞eta" "Stream A → Stream A" "s ↦ [ .head ↦ s .head | .tail ↦ ∞eta (s .tail) ]";
  unequal_at "s ↦ s" "s ↦ ∞eta s" "Stream A → Stream A";
  def "∞eta_bisim" "(s:Stream A) → Id (Stream A) s (∞eta s)"
    "s ↦ [ .head ↦ refl (s .head) | .tail ↦ ∞eta_bisim (s .tail) ]";

  (* We construct a stream of natural numbers and check its first few elements *)
  Types.Nat.install ();
  def "nats" "Stream ℕ" "corec ℕ ℕ (x ↦ x) (x ↦ suc. x) 0";
  equal_at "nats .head" "0" "ℕ";
  equal_at "nats .tail .head" "1" "ℕ";
  equal_at "nats .tail .tail .head" "2" "ℕ";
  equal_at "nats .tail .tail .tail .head" "3" "ℕ";

  (* Now we construct the stream of fibonacci numbers and check the first few of its elements *)
  Testutil.Repl.nat_install_ops ();
  Types.Sigma.install ();
  def "fib" "Stream ℕ"
    "corec ℕ (ℕ × ℕ) (x ↦ x .fst) (x ↦ ( fst ≔ x .snd , snd ≔ x .fst + x .snd )) (fst ≔ 1, snd ≔ 1)";
  equal_at "fib .head" "1" "ℕ";
  equal_at "fib .tail .head" "1" "ℕ";
  equal_at "fib .tail .tail .head" "2" "ℕ";
  equal_at "fib .tail .tail .tail .head" "3" "ℕ";
  equal_at "fib .tail .tail .tail .tail .head" "5" "ℕ";
  equal_at "fib .tail .tail .tail .tail .tail .head" "8" "ℕ";

  ()
