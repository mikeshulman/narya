open Testutil.Repl

let () =
  run @@ fun () ->
  assume "A" "Type";
  def "nat" "Type" "(A → A) → (A → A)";
  def "zero" "nat" "f x ↦ x";
  def "one" "nat" "f x ↦ f x";
  print "one";
  def "two" "nat" "f x ↦ f (f x)";
  def "three" "nat" "f x ↦ f (f (f x))";
  def "plus" "nat → nat → nat" "m n f x ↦ (m f) (n f x)";
  print "plus one one";
  print "plus two three";
  def "times" "nat → nat → nat" "m n f x ↦ m (n f) x";
  print "times one one";
  print "times two three";
  print "nat";
  print "(X:Type) → X → X";
  print "(X:Type)(_: X) → X";
  print "(x:A)(y:A) → A → (z:A) → A";
  def "unat" "Type" "(X:Type) → (X→X) → X→X";
  def "uzero" "unat" "_ _ x ↦ x";
  def "uone" "unat" "_ f x ↦ f x";
  def "utwo" "unat" "_ f x ↦ f (f x)";
  def "uthree" "unat" "_ f x ↦ f (f (f x))";
  print "uzero";
  print "uone";
  def "exp" "unat → unat → unat" "m n Y f x ↦ n (Y→Y) (m Y) f x";
  print "exp";
  print "exp utwo uthree";
  Types.Nat.install ();
  Types.Nat.install_ops ();
  Types.Sigma.install ();
  print "(fst := 0,snd := 0) : ℕ × ℕ";
  print "(0,0) : ℕ × ℕ";
  print "(fst := 1, 2) : ℕ × ℕ";
  print "(snd := 1, 2) : ℕ × ℕ";
  print "(0,(0,0)) : ℕ × ℕ × ℕ";
  print "((0,0),0) : (ℕ × ℕ) × ℕ";
  print "(fst ≔ x ↦ x, snd ≔ 2) : (ℕ → ℕ) × ℕ";
  assume "s" "(ℕ → ℕ) × ℕ";
  print "s .fst 3";
  (* TODO: Needs unparsing of case trees *)
  (*
  Types.Stream.install ();
  assume "zz" "Stream N";
  print "[ .head |-> 0 | .tail |-> zz] : Stream N";
  (* Evaluation and readback reorders fields to the order they appear in the record type definition. *)
  print "[ .tail |-> zz | .head |-> 0 ] : Stream N";
*)
  Types.Lst.install ();
  print "nil. : List ℕ";
  print "cons. 2 nil. : List ℕ";
  print "cons. 4 (cons. 2 nil.) : List ℕ";
  print "refl (0:ℕ)";
  assume "b" "A";
  print "refl b";
  print "(a ↦ refl a) : (a:A) → Id A a a";
  print "refl (refl b)";
  print "refl (refl (refl b))";
  (* Requires fixing the degeneracy-of-constant bug. *)
  (*
  assume "a00" "A";
  assume "a01" "A";
  assume "a10" "A";
  assume "a11" "A";
  assume "a02" "Id A a00 a01";
  assume "a20" "Id A a00 a10";
  assume "a12" "Id A a10 a11";
  assume "a21" "Id A a01 a11";
  assume "a22" "Id ((x y ↦ Id A x y) : A → A → Type) a00 a01 a02 a10 a11 a12 a20 a21"
*)
  (* Let-bindings always reduce away, disappearing after readback. *)
  print "let x := b in b";
  (* Binary operators *)
  assume "m" "ℕ";
  assume "n" "ℕ";
  print "m+n";
  print "m+n*n";
  print "m*(m+n*n)";
  print "m + suc. n";
  print "(m+n)*(m+n)";
  ()
