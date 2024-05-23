Printing higher-dimensional pi-types

  $ cat >hdpi.ny <<EOF
  > axiom A : Type
  > axiom B : Type
  > axiom E : Id Type A B
  > axiom A' : A → Type
  > axiom B' : B → Type
  > axiom E' : refl ((X ↦ X → Type) : Type → Type) A B E A' B'
  > echo refl ((A B ↦ (x:A) → B x) : (X:Type) → (X → Type) → Type) A B E A' B' E'

  $ narya hdpi.ny
  refl Π A B E (x ↦ A' x) (x ↦ B' x) (x ⤇ E' x.0 x.1 x.2)
    : refl Type ((x : A) → A' x) ((x : B) → B' x)
  
