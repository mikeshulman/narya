Testing let-bindings

  $ cat >pre.ny <<EOF
  > axiom A:Type
  > axiom a0:A
  > axiom a1:A
  > axiom a2: Id A a0 a1
  > axiom B : A → Type
  > axiom b : B a0
  > axiom f : (x:A) → B x → B x
  > EOF

  $ narya -v pre.ny -e "def a0' : A := let id ≔ ((x ↦ x) : A → A) in id a0" -e "def test : Id A a0 a0' := refl a0"
   ￫ info[I0001]
   ￮ Axiom A assumed
  
   ￫ info[I0001]
   ￮ Axiom a0 assumed
  
   ￫ info[I0001]
   ￮ Axiom a1 assumed
  
   ￫ info[I0001]
   ￮ Axiom a2 assumed
  
   ￫ info[I0001]
   ￮ Axiom B assumed
  
   ￫ info[I0001]
   ￮ Axiom b assumed
  
   ￫ info[I0001]
   ￮ Axiom f assumed
  
   ￫ info[I0000]
   ￮ Constant a0' defined
  
   ￫ info[I0000]
   ￮ Constant test defined
  

  $ narya -v pre.ny -e "def a0' : A := let id : A → A ≔ x ↦ x in id a0" -e "def test : Id A a0 a0' := refl a0"
   ￫ info[I0001]
   ￮ Axiom A assumed
  
   ￫ info[I0001]
   ￮ Axiom a0 assumed
  
   ￫ info[I0001]
   ￮ Axiom a1 assumed
  
   ￫ info[I0001]
   ￮ Axiom a2 assumed
  
   ￫ info[I0001]
   ￮ Axiom B assumed
  
   ￫ info[I0001]
   ￮ Axiom b assumed
  
   ￫ info[I0001]
   ￮ Axiom f assumed
  
   ￫ info[I0000]
   ￮ Constant a0' defined
  
   ￫ info[I0000]
   ￮ Constant test defined
  

It matters what the variable is bound to:

  $ narya -v pre.ny -e "def a0' : A := let id : A → A ≔ x ↦ a1 in id a0" -e "def untest : Id A a0 a0' := refl a0"
   ￫ info[I0001]
   ￮ Axiom A assumed
  
   ￫ info[I0001]
   ￮ Axiom a0 assumed
  
   ￫ info[I0001]
   ￮ Axiom a1 assumed
  
   ￫ info[I0001]
   ￮ Axiom a2 assumed
  
   ￫ info[I0001]
   ￮ Axiom B assumed
  
   ￫ info[I0001]
   ￮ Axiom b assumed
  
   ￫ info[I0001]
   ￮ Axiom f assumed
  
   ￫ info[I0000]
   ￮ Constant a0' defined
  
   ￫ error[E0401]
   ￭ command-line exec string
   1 | def untest : Id A a0 a0' := refl a0
     ^ term synthesized type
         refl A a0 a0
       but is being checked against type
         refl A a0 a1
  
  [1]

Ap on let:

  $ narya -v pre.ny -e "def a2' := refl ((y ↦ let id : A → A ≔ x ↦ x in id y) : A → A) a0 a1 a2" -e "def test : Id (Id A a0 a1) a2 a2' := refl a2"
   ￫ info[I0001]
   ￮ Axiom A assumed
  
   ￫ info[I0001]
   ￮ Axiom a0 assumed
  
   ￫ info[I0001]
   ￮ Axiom a1 assumed
  
   ￫ info[I0001]
   ￮ Axiom a2 assumed
  
   ￫ info[I0001]
   ￮ Axiom B assumed
  
   ￫ info[I0001]
   ￮ Axiom b assumed
  
   ￫ info[I0001]
   ￮ Axiom f assumed
  
   ￫ info[I0000]
   ￮ Constant a2' defined
  
   ￫ info[I0000]
   ￮ Constant test defined
  

Let affects typechecking:

  $ narya -v pre.ny -e "def b' : B a0 := let x ≔ a0 in f x b" -e "def untest : B a0 ≔ ((x ↦ f x b) : A → B a0) a0"
   ￫ info[I0001]
   ￮ Axiom A assumed
  
   ￫ info[I0001]
   ￮ Axiom a0 assumed
  
   ￫ info[I0001]
   ￮ Axiom a1 assumed
  
   ￫ info[I0001]
   ￮ Axiom a2 assumed
  
   ￫ info[I0001]
   ￮ Axiom B assumed
  
   ￫ info[I0001]
   ￮ Axiom b assumed
  
   ￫ info[I0001]
   ￮ Axiom f assumed
  
   ￫ info[I0000]
   ￮ Constant b' defined
  
   ￫ error[E0401]
   ￭ command-line exec string
   1 | def untest : B a0 ≔ ((x ↦ f x b) : A → B a0) a0
     ^ term synthesized type B a0 but is being checked against type B x
  
  [1]
