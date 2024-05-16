{` We check that a family of mutual definitions can apply external degeneracies to each other.  This was an issue once because they are temporarily defined as "axioms" during definition, and by default axioms don't admit external degeneracies. `}
def X : Type ≔ Type

and Y : (x : X) → X⁽ᵈ⁾ x ≔ ?
