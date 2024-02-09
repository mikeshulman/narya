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
  Types.Gel.install ();
  assume "B" "Type";
  assume "R" "A → B → Type";
  assume "a" "A";
  assume "b" "B";
  assume "r" "R a b";
  print "(_ ≔ r) : Gel A B R a b";
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
  print "refl a";
  print "(a ↦ refl a) : (a:A) → Id A a a";
  print "refl (refl a)";
  print "refl (refl (refl a))";
  assume "a00" "A";
  assume "a01" "A";
  assume "a10" "A";
  assume "a11" "A";
  assume "a02" "Id A a00 a01";
  assume "a20" "Id A a00 a10";
  assume "a12" "Id A a10 a11";
  assume "a21" "Id A a01 a11";
  assume "a22" "Id ((x y ↦ Id A x y) : A → A → Type) a00 a01 a02 a10 a11 a12 a20 a21";
  print "sym a22";
  assume "a000" "A";
  assume "a001" "A";
  assume "a010" "A";
  assume "a011" "A";
  assume "a002" "Id A a000 a001";
  assume "a020" "Id A a000 a010";
  assume "a012" "Id A a010 a011";
  assume "a021" "Id A a001 a011";
  assume "a022" "Id ((x y ↦ Id A x y) : A → A → Type) a000 a001 a002 a010 a011 a012 a020 a021";
  assume "a100" "A";
  assume "a101" "A";
  assume "a110" "A";
  assume "a111" "A";
  assume "a102" "Id A a100 a101";
  assume "a120" "Id A a100 a110";
  assume "a112" "Id A a110 a111";
  assume "a121" "Id A a101 a111";
  assume "a122" "Id ((x y ↦ Id A x y) : A → A → Type) a100 a101 a102 a110 a111 a112 a120 a121";
  assume "a200" "Id A a000 a100";
  assume "a201" "Id A a001 a101";
  assume "a202" "Id ((x y ↦ Id A x y) : A → A → Type) a000 a001 a002 a100 a101 a102 a200 a201";
  assume "a210" "Id A a010 a110";
  assume "a211" "Id A a011 a111";
  assume "a212" "Id ((x y ↦ Id A x y) : A → A → Type) a010 a011 a012 a110 a111 a112 a210 a211";
  assume "a220" "Id ((x y ↦ Id A x y) : A → A → Type) a000 a010 a020 a100 a110 a120 a200 a210";
  assume "a221" "Id ((x y ↦ Id A x y) : A → A → Type) a001 a011 a021 a101 a111 a121 a201 a211";
  assume "a222"
    "Id ((x00 x01 x02 x10 x11 x12 x20 x21 ↦ Id ((x y ↦ Id A x y) : A → A → Type) x00 x01 x02 x10 x11 x12 x20 x21)
         : (x00:A) (x01:A) (x02 : Id A x00 x01) (x10:A) (x11:A) (x12 : Id A x10 x11) (x20 : Id A x00 x10) (x21 : Id A x01 x11) → Type)
     a000 a001 a002 a010 a011 a012 a020 a021 a022 a100 a101 a102 a110 a111 a112 a120 a121 a122 a200 a201 a202 a210 a211 a212 a220 a221";
  print "sym a222";
  print
    "refl ((x00 x01 x02 x10 x11 x12 x20 x21 x22 ↦ sym x22)
          : (x00:A) (x01:A) (x02 : Id A x00 x01) (x10:A) (x11:A) (x12 : Id A x10 x11) (x20 : Id A x00 x10) (x21 : Id A x01 x11)
              → Id ((x y ↦ Id A x y) : A → A → Type) x00 x01 x02 x10 x11 x12 x20 x21
              → Id ((x y ↦ Id A x y) : A → A → Type) x00 x10 x20 x01 x11 x21 x02 x12)
       a000 a001 a002 a010 a011 a012 a020 a021 a022 a100 a101 a102 a110 a111 a112 a120 a121 a122 a200 a201 a202 a210 a211 a212 a220 a221 a222";
  print
    "refl ((x00 x01 x02 x10 x11 x12 x20 x21 x22 ↦ sym x22)
          : (x00:A) (x01:A) (x02 : Id A x00 x01) (x10:A) (x11:A) (x12 : Id A x10 x11) (x20 : Id A x00 x10) (x21 : Id A x01 x11)
              → Id ((x y ↦ Id A x y) : A → A → Type) x00 x01 x02 x10 x11 x12 x20 x21
              → Id ((x y ↦ Id A x y) : A → A → Type) x00 x10 x20 x01 x11 x21 x02 x12)
       a000 a010 a020 a001 a011 a021 a002 a012 (sym a022) a100 a110 a120 a101 a111 a121 a102 a112 (sym a122) a200 a210 a220 a201 a211 a221 a202 a212 (sym a222)";
  print
    "sym
     (refl ((x00 x01 x02 x10 x11 x12 x20 x21 x22 ↦ sym x22)
          : (x00:A) (x01:A) (x02 : Id A x00 x01) (x10:A) (x11:A) (x12 : Id A x10 x11) (x20 : Id A x00 x10) (x21 : Id A x01 x11)
              → Id ((x y ↦ Id A x y) : A → A → Type) x00 x01 x02 x10 x11 x12 x20 x21
              → Id ((x y ↦ Id A x y) : A → A → Type) x00 x10 x20 x01 x11 x21 x02 x12)
       a000 a010 a020 a001 a011 a021 a002 a012 (sym a022) a100 a110 a120 a101 a111 a121 a102 a112 (sym a122) a200 a210 a220 a201 a211 a221 a202 a212 (sym a222))";

  (* Let-bindings always reduce away, disappearing after readback. *)
  print "let x := a in a";
  (* Binary operators *)
  assume "m" "ℕ";
  assume "n" "ℕ";
  print "m+n";
  print "m+n*n";
  print "m*(m+n*n)";
  print "m + suc. n";
  print "(m+n)*(m+n)";
  ()
