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
  print "exp utwo uthree"
