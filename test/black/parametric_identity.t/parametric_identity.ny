{` First we postulate an equality type `}
axiom eq : (X:Type) → X → X → Type
axiom eqr : (X:Type) (x:X) → eq X x x

{` Now we prove a first application of parametricity: anything in the type of the polymorphic identity function is pointwise equal to the identity.  (This doesn't actually require the computation laws for gel/ungel, and it only uses unary parametricity.) `}
axiom f : (X:Type) → X → X

def f_is_id : (X:Type) (x:X) → eq X x (f X x) ≔ X x ↦
  refl f X X (Gel X X (a b ↦ eq X x b)) x x (_ ≔ eqr X x) .ungel
