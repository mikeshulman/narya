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
  
