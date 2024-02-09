open Testutil.Repl

let () =
  run @@ fun () ->
  Types.Sigma.install ();
  def "pair" "(A:Type) → (B : A → Type) → (x:A) → B x → ((x:A) × B x)" "A B a b ↦ (a,b)";
  assume "A" "Type";
  assume "B" "A → Type";
  (* Pairs and tuples have the correct type and are equal to each other *)
  assume "a" "A";
  assume "b" "B a";
  def "ab" "Σ A B" "(a,b)";
  def "ab'" "Σ A B" "pair A B a b";
  equal_at "ab" "ab'" "Σ A B";
  (* Projections have the correct type *)
  assume "x" "Σ A B";
  def "x1" "A" "x .fst";
  def "x2" "B x1" "x .snd";

  (* Projections of pairs and tuples compute *)
  equal_at "ab .fst" "a" "A";
  equal_at "ab .snd" "b" "B a";
  equal_at "ab' .fst" "a" "A";
  equal_at "ab' .snd" "b" "B a";

  (* Projections satisfy eta-conversion for both pairs and tupls *)
  def "x'" "Σ A B" "pair A B (x .fst) (x .snd)";
  equal_at "x" "x'" "Σ A B";
  def "x''" "Σ A B" "(x .fst, x .snd)";
  equal_at "x" "x''" "Σ A B";

  (* Identifications can be paired to give an identification of pairs *)
  assume "a0" "A";
  assume "b0" "B a0";
  assume "a1" "A";
  assume "b1" "B a1";
  assume "a2" "Id A a0 a1";
  assume "b2" "Id B a0 a1 a2 b0 b1";
  def "ab2" "Id (Σ A B) (a0,b0) (a1,b1)" "(a2,b2)";

  (* As for function-types, identity types of sigma-types are invariant under eta-conversion *)
  equal_at "Id (Σ A B) (a0,b0) (a1,b1)" "Id (Σ A B) (pair A B a0 b0) (a1,b1)" "Type";
  equal_at "(a2,b2)" "refl pair A A (refl A) B B (refl B) a0 a1 a2 b0 b1 b2"
    "Id (Σ A B) (a0,b0) (a1,b1)";

  (* And can be projected back out again to the inputs *)
  equal_at "ab2 .fst" "a2" "Id A a0 a1";
  equal_at "ab2 .snd" "b2" "Id B a0 a1 a2 b0 b1";

  (* Refl commutes with pairing *)
  equal_at "refl (pair A B a b)" "(refl a, refl b)" "Id (Σ A B) ab ab";
  equal_at "refl ((a,b) : Σ A B)" "(refl a, refl b)" "Id (Σ A B) ab ab";

  (* Sigmas can store identities and squares, and symmetry can act on them *)
  assume "X" "Type";
  assume "x00" "X";
  assume "x01" "X";
  assume "x02" "Id X x00 x01";
  assume "x10" "X";
  assume "x11" "X";
  assume "x12" "Id X x10 x11";
  assume "x20" "Id X x00 x10";
  assume "x21" "Id X x01 x11";
  assume "x22" "Id ((x y ↦ Id X x y) : X → X → Type) x00 x01 x02 x10 x11 x12 x20 x21";
  assume "Y" "Type";
  assume "y" "Y";
  assume "s" "(Id ((x y ↦ Id X x y) : X → X → Type) x00 x01 x02 x10 x11 x12 x20 x21) × Y";
  Testutil.Mcp.unsynth "sym s";
  def "s1s" "Id ((x y ↦ Id X x y) : X → X → Type) x00 x10 x20 x01 x11 x21 x02 x12" "sym (s .fst)";

  ()
