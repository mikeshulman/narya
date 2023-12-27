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
  print "times two three"
