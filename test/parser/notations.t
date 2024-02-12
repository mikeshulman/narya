Testing notation commands

  $ narya -v -e 'axiom A:Type' -e 'axiom f:A->A->A' -e 'infix 0 f : x "&" y := f x y'
   ￫ info[I0001]
   ￮ Axiom A assumed
  
   ￫ info[I0001]
   ￮ Axiom f assumed
  
   ￫ info[I0002]
   ￮ Notation f defined
  

  $ narya -e 'axiom A:Type' -e 'axiom f:A->A->A' -e 'infix 0 f : x "&" y.z := f x y.z'
   ￫ error[E0202]
   ￮ invalid local variable name: y.z
  
  [1]

  $ narya -e 'axiom A:Type' -e 'axiom f:A->A->A' -e 'postfix 0 f : x "/" := f x x'
   ￫ error[E2007]
   ￮ invalid notation pattern: 'variable used twice: x'
  
  [1]


  $ narya -e 'axiom A:Type' -e 'axiom f:A->A->A' -e 'infix 0 f : x "&" y "#" z := f x y'
   ￫ error[E2007]
   ￮ invalid notation pattern: 'unused variable: z'
  
  [1]


  $ narya -e 'axiom A:Type' -e 'axiom f:A->A->A' -e 'postfix 0 f : x "/" := f x y'
   ￫ error[E2007]
   ￮ invalid notation pattern: 'unbound variable(s): y'
  
  [1]

  $ narya -e 'axiom A:Type' -e 'axiom f:A->A->A' -e 'infix 0 f : x "&" y "#" x := f x y'
   ￫ error[E2007]
   ￮ invalid notation pattern: 'duplicate variable: x'
  
  [1]

  $ narya -e 'axiom A:Type' -e 'axiom f:A->A->A' -e 'prefix 0 f : x "&" y := f x y'
   ￫ error[E2003]
   ￮ declared fixity doesn't match notation pattern
  
  [1]

  $ narya -e 'axiom A:Type' -e 'axiom f:A->A->A' -e 'outfix f : "#" x "&" y "#" := f x y'

  $ narya -e 'axiom A:Type' -e 'axiom f:A->A->A' -e 'outfix 0 f : "#" x "&" y "#" := f x y'
   ￫ error[E0200]
   ￭ command-line exec string
   1 | outfix 0 f : "#" x "&" y "#" := f x y
     ^ parse error
  
  [1]

  $ narya -e 'axiom A:Type' -e 'axiom f:A->A->A' -e 'infix 0.5 f : x "&" y := f x y'


  $ narya -e 'axiom A:Type' -e 'axiom f:A->A->A' -e 'infix 0.1 f : x "&" y := f x y'
   ￫ error[E2004]
   ￮ invalid tightness: 0.1
  
  [1]
