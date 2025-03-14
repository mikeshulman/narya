The parsing of "(X:Type)->Y" is technically ambiguous: in addition to
a dependent function-type, it could be a non-dependent function type
with ascribed domain.  We always interpret it as a dependent
function-type, but to get the non-dependent version you can add extra
parentheses.

  $ narya -e 'def A := Type axiom x : Type axiom B : Type echo (x:A) -> B'
  (x : Type) → B
    : Type
  

  $ narya -e 'def A := Type axiom x : Type axiom B : Type echo ((x:A)) -> B'
  x → B
    : Type
  

  $ narya -e 'def A := Type axiom x : Type axiom B : Type echo ((x):A) -> B'
  x → B
    : Type
  

There was once a bug with expressions like this, so we test for it.

  $ narya -e "echo (A:Type) → (A:Type) → A"
  (A : Type) (A0 : Type) → A0
    : Type
  
