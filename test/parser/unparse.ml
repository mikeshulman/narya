open Testutil.Repl

let () =
  run @@ fun () ->
  assume "A" "Type";
  def "nat" "Type" "(A → A) → (A → A)";
  def "zero" "nat" "f x ↦ x";
  def "one" "nat" "f x ↦ f x";
  def "two" "nat" "f x ↦ f (f x)";
  def "three" "nat" "f x ↦ f (f (f x))";
  def "plus" "nat → nat → nat" "m n f x ↦ (m f) (n f x)";
  print "plus one one" "nat";
  print "plus two three" "nat";
  def "times" "nat → nat → nat" "m n f x ↦ m (n f) x";
  print "times one one" "nat";
  print "times two three" "nat"
