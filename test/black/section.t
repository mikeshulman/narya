  $ cat >err.ny <<EOF
  > axiom A : Type
  > section B :=
  >   axiom f : A -> Type
  > end
  > echo B.f
  > echo f
  > EOF

  $ narya -v err.ny
   ￫ info[I0001]
   ￮ axiom A assumed
  
   ￫ info[I0007]
   ￮ section B opened
  
   ￫ info[I0001]
   ￮ axiom f assumed
  
   ￫ info[I0008]
   ￮ section B closed
  
  B.f
    : A → Type
  
   ￫ error[E0300]
   ￭ $TESTCASE_ROOT/err.ny
   6 | echo f
     ^ unbound variable: f
  
  [1]

  $ narya -v -e 'end'
   ￫ error[E2600]
   ￮ no section here to end
  
  [1]

  $ cat >section.ny <<EOF
  > axiom A:Type
  > section one :=
  >   axiom B:Type
  >   section two :=
  >     axiom f : A -> B
  >   end
  >   axiom a:A
  >   def b : B := two.f a
  >   section three :=
  >     axiom C : B -> Type
  >     axiom c : C b
  >   end
  >   axiom g : (y:B) → three.C y
  > end
  > axiom gc : Id (one.three.C one.b) one.three.c (one.g one.b)
  > import one.three
  > axiom gc' : Id (C one.b) c (one.g one.b)
  > EOF

  $ narya -v section.ny
   ￫ info[I0001]
   ￮ axiom A assumed
  
   ￫ info[I0007]
   ￮ section one opened
  
   ￫ info[I0001]
   ￮ axiom B assumed
  
   ￫ info[I0007]
   ￮ section two opened
  
   ￫ info[I0001]
   ￮ axiom f assumed
  
   ￫ info[I0008]
   ￮ section two closed
  
   ￫ info[I0001]
   ￮ axiom a assumed
  
   ￫ info[I0000]
   ￮ constant b defined
  
   ￫ info[I0007]
   ￮ section three opened
  
   ￫ info[I0001]
   ￮ axiom C assumed
  
   ￫ info[I0001]
   ￮ axiom c assumed
  
   ￫ info[I0008]
   ￮ section three closed
  
   ￫ info[I0001]
   ￮ axiom g assumed
  
   ￫ info[I0008]
   ￮ section one closed
  
   ￫ info[I0001]
   ￮ axiom gc assumed
  
   ￫ info[I0001]
   ￮ axiom gc' assumed
  
