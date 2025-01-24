Testing notation commands

  $ narya -v -e 'axiom A:Type' -e 'axiom f:A->A->A' -e 'notation 0 f : x "&" y := f x y' -e 'def ff (x y : A) : A := x & y' -e 'axiom a : A' -e 'echo ff a a'
   ￫ info[I0001]
   ￮ axiom A assumed
  
   ￫ info[I0001]
   ￮ axiom f assumed
  
   ￫ info[I0002]
   ￮ notation f defined
  
   ￫ info[I0000]
   ￮ constant ff defined
  
   ￫ info[I0001]
   ￮ axiom a assumed
  
  a & a
    : A
  

  $ narya -e 'axiom A:Type' -e 'axiom f:A->A->A' -e 'notation 0 f : x "&" y.z := f x y.z'
   ￫ error[E0202]
   ￮ invalid local variable name: y.z
  
  [1]

  $ narya -e 'axiom A:Type' -e 'axiom f:A->A->A' -e 'notation 0 f : x "/" := f x x'
   ￫ error[E2207]
   ￮ notation variable 'x' used twice
  
  [1]


  $ narya -e 'axiom A:Type' -e 'axiom f:A->A->A' -e 'notation 0 f : x "&" y "#" z := f x y'
   ￫ error[E2206]
   ￮ unused notation variable: 'z'
  
  [1]


  $ narya -e 'axiom A:Type' -e 'axiom f:A->A->A' -e 'notation 0 f : x "/" := f x y'
   ￫ error[E2208]
   ￮ unbound variable(s) in notation definition: y
  
  [1]

  $ narya -e 'axiom A:Type' -e 'axiom f:A->A->A' -e 'notation 0 f : x "&" y "#" x := f x y'
   ￫ error[E2204]
   ￮ duplicate notation variable: 'x'
  
  [1]

  $ narya -e 'axiom A:Type' -e 'axiom f:A->A->A' -e 'notation f : "#" x "&" y "#" := f x y'

  $ narya -e 'axiom A:Type' -e 'axiom f:A->A->A' -e 'notation f : x "&" y "#" := f x y'
   ￫ error[E2203]
   ￮ notation command doesn't match pattern (tightness must be omitted only for outfix notations)
  
  [1]

  $ narya -e 'axiom A:Type' -e 'axiom f:A->A->A' -e 'notation 0 f : "#" x "&" y "#" := f x y'
   ￫ error[E2203]
   ￮ notation command doesn't match pattern (tightness must be omitted only for outfix notations)
  
  [1]

  $ narya -e 'axiom A:Type' -e 'axiom f:A->A->A' -e 'notation 0.5 f : x "&" y := f x y' -e 'def ff (x y : A) : A := x & y'


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
   ￫ error[E2205]
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
   ￮ invalid notation pattern: has no symbols
  
  [1]

  $ narya -e 'axiom A:Type' -e 'axiom f:A->A->A' -e 'notation 0 f : … x "&" y … := f x y'
   ￫ error[E2202]
   ￮ invalid notation pattern: can't be both right and left associative
  
  [1]

  $ narya -e 'axiom A:Type' -e 'axiom f:A->A' -e 'notation 0 f : x := f x'
   ￫ error[E2202]
   ￮ invalid notation pattern: has no symbols
  
  [1]

  $ narya -e 'axiom A:Type' -e 'axiom f:A->A->A' -e 'notation 0 f : "&" x y := f x y'
   ￫ error[E2202]
   ￮ invalid notation pattern: missing symbol between variables
  
  [1]

  $ narya -e 'axiom A:Type' -e 'axiom f:A->A->A' -e 'notation 0 f : x "&" y := f x y' -e 'notation 0 f2 : x "%" y := f x y' -e 'def ff (x y : A) : A := x & y' -e 'def ff2 (x y : A) : A := x % y' -e 'axiom a : A' -e 'echo ff a a' -e 'echo ff2 a a'
   ￫ warning[E2209]
   ￮ replacing printing notation for f (previous notation will still be parseable)
  
  a % a
    : A
  
  a % a
    : A
  
