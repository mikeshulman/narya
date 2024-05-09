def f : Type → Type ≔ X ↦ X

{` This tests the display of holes showing that X is locked.  But note that the definition also fails even after the hole is generated, because the typechecker can't tell that ?⁽ᵈ⁾ belongs to Type⁽ᵈ⁾ X since it doesn't know that ? is equal to X.  Agda is willing to accept holes like this, apparently delaying the necessary equation and checking it when a putative value is given to fill the hole; we would eventually like to do that to. `}
def g (X : Type) : Type⁽ᵈ⁾ X ≔ (f ?)⁽ᵈ⁾
