Synthesizing definitions

  $ narya -v -e 'axiom A : Type' -e 'axiom f : A -> A' -e 'axiom a : A' -e 'def fa := f a'
   ￫ info[I0001]
   ￮ Axiom A assumed
  
   ￫ info[I0001]
   ￮ Axiom f assumed
  
   ￫ info[I0001]
   ￮ Axiom a assumed
  
   ￫ info[I0000]
   ￮ Constant fa defined
  

Matches can also synthesize

  $ narya -v -e 'def bot : Type ≔ data [ ]' -e 'axiom P : bot → Type' -e 'def foo (e : bot) ≔ match e return x ↦ P x [ ]'
   ￫ info[I0000]
   ￮ Constant bot defined
  
   ￫ info[I0001]
   ￮ Axiom P assumed
  
   ￫ info[I0000]
   ￮ Constant foo defined
  
