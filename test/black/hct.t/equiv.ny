import "isfibrant"
import "homotopy"

{` Notions of equivalence `}

option function boundaries ≔ implicit
option type boundaries ≔ implicit

{` Bisimulations `}

def isBisim (A B : Fib) (R : A .t → B .t → Fib) : Type ≔ codata [
| r .trr : A .t → B .t
| r .liftr : (a : A .t) → R a (r .trr a) .t
| r .trl : B .t → A .t
| r .liftl : (b : B .t) → R (r .trl b) b .t
| r .id
  : (a0 a1 : A .t) (b0 b1 : B .t) (r0 : R a0 b0 .t) (r1 : R a1 b1 .t)
    → isBisim (Idf A a0 a1) (Idf B b0 b1)
        (a2 b2 ↦ (Id R a2 b2 .t r0 r1, refl R a2 b2 .f .id.1 r0 r1)) ]

{` 1-1 correspondences `}

def is11 (A B : Fib) (R : A .t → B .t → Fib) : Type ≔ sig (
contrr : (a:A .t) → isContr (Σf B (b ↦ R a b)),
contrl : (b:B .t) → isContr (Σf A (a ↦ R a b)))
