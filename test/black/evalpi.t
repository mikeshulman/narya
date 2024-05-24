  $ cat >test.ny <<EOF
  > axiom A:Type
  > axiom a0:A
  > axiom a1:A
  > axiom a2: Id A a0 a1
  > def a2' := refl ((y ↦ let id : A → A ≔ x ↦ x in id y) : A → A)
  > echo a2'
  > EOF

  $ narya -v test.ny
   ￫ info[I0001]
   ￮ Axiom A assumed
  
   ￫ info[I0001]
   ￮ Axiom a0 assumed
  
   ￫ info[I0001]
   ￮ Axiom a1 assumed
  
   ￫ info[I0001]
   ￮ Axiom a2 assumed
  
   ￫ info[I0000]
   ￮ Constant a2' defined
  
  y ⤇ y.2
    : refl Π A A (refl A) (_ ↦ A) (_ ↦ A) (_ ⤇ refl A) (y ↦ y) (y ↦ y)
  
