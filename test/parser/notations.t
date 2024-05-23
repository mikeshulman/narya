Testing notation commands

  $ narya -v -e 'axiom A:Type' -e 'axiom f:A->A->A' -e 'notation 0 f : x "&" y := f x y'
   ￫ info[I0001]
   ￮ Axiom A assumed
  
   ￫ info[I0001]
   ￮ Axiom f assumed
  
   ￫ info[I0002]
   ￮ Notation f defined
  

  $ narya -e 'axiom A:Type' -e 'axiom f:A->A->A' -e 'notation 0 f : x "&" y.z := f x y.z'
   ￫ error[E0202]
   ￮ invalid local variable name: y.z
  
  [1]

  $ narya -e 'axiom A:Type' -e 'axiom f:A->A->A' -e 'notation 0 f : x "/" := f x x'
   ￫ error[E2209]
   ￮ notation variable 'x' used twice
  
  [1]


  $ narya -e 'axiom A:Type' -e 'axiom f:A->A->A' -e 'notation 0 f : x "&" y "#" z := f x y'
   ￫ error[E2208]
   ￮ unused notation variable: 'z'
  
  [1]


  $ narya -e 'axiom A:Type' -e 'axiom f:A->A->A' -e 'notation 0 f : x "/" := f x y'
   ￫ error[E2210]
   ￮ unbound variable(s) in notation definition: y
  
  [1]

  $ narya -e 'axiom A:Type' -e 'axiom f:A->A->A' -e 'notation 0 f : x "&" y "#" x := f x y'
   ￫ error[E2206]
   ￮ duplicate notation variable: 'x'
  
  [1]

  $ narya -e 'axiom A:Type' -e 'axiom f:A->A->A' -e 'notation f : "#" x "&" y "#" := f x y'

  $ narya -e 'axiom A:Type' -e 'axiom f:A->A->A' -e 'notation f : x "&" y "#" := f x y'
   ￫ error[E2205]
   ￮ notation command doesn't match pattern (tightness must be omitted only for outfix notations)
  
  [1]

  $ narya -e 'axiom A:Type' -e 'axiom f:A->A->A' -e 'notation 0 f : "#" x "&" y "#" := f x y'
   ￫ error[E2205]
   ￮ notation command doesn't match pattern (tightness must be omitted only for outfix notations)
  
  [1]

  $ narya -e 'axiom A:Type' -e 'axiom f:A->A->A' -e 'notation 0.5 f : x "&" y := f x y'


  $ narya -e 'axiom A:Type' -e 'axiom f:A->A->A' -e 'notation 0.1 f : x "&" y := f x y'
   ￫ error[E2200]
   ￭ command-line exec string
   1 | notation 0.1 f : x "&" y := f x y
     ^ invalid tightness: 0.1
  
  [1]

  $ narya -e 'axiom A:Type' -e 'axiom f:A->A->A' -e 'notation 0 f : x "&x" y := f x y'
   ￫ error[E2201]
   ￮ invalid notation symbol: &x
  
  [1]

  $ narya -e 'axiom A:Type' -e 'axiom f:A->A->A' -e 'notation 0 f : x "&" y := Type x y'
   ￫ error[E2207]
   ￮ invalid notation head: Type
  
  [1]

  $ narya -e 'axiom A:Type' -e 'axiom f:A' -e 'notation f : "&" := f'

  $ narya -e 'axiom A:Type' -e 'axiom f:A->A->A' -e 'notation 0 f : x "&" … "&" y := f x y'
   ￫ error[E0100]
   ￮ internal ellipses in notation not yet implemented
  
  [1]

  $ narya -e 'axiom A:Type' -e 'axiom f:A->A->A' -e 'notation 0 f : x "&" … y := f x y'
   ￫ error[E0100]
   ￮ internal ellipses in notation not yet implemented
  
  [1]

  $ narya -e 'axiom A:Type' -e 'axiom f:A->A->A' -e 'notation 0 f : … := f x y'
   ￫ error[E2202]
   ￮ notation has no symbols
  
  [1]

  $ narya -e 'axiom A:Type' -e 'axiom f:A->A->A' -e 'notation 0 f : … x "&" y … := f x y'
   ￫ error[E2204]
   ￮ notation can't be both right and left associative
  
  [1]

  $ narya -e 'axiom A:Type' -e 'axiom f:A->A' -e 'notation 0 f : x := f x'
   ￫ error[E2202]
   ￮ notation has no symbols
  
  [1]

  $ narya -e 'axiom A:Type' -e 'axiom f:A->A->A' -e 'notation 0 f : "&" x y := f x y'
   ￫ error[E2203]
   ￮ missing notation symbol between variables
  
  [1]

  $ narya -e 'axiom A:Type' -e 'axiom f:A->A->A' -e 'notation 0 f : x "&" y := f x y' -e 'notation 0 f2 : x "%" y := f x y'
   ￫ warning[E2211]
   ￮ replacing printing notation for f (previous notation will still be parseable)
  
