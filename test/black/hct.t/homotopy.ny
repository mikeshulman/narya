import "isfibrant"
import "fibrant_types" | renaming . fibrancy

def Σf (A : Fib) (B : A .t → Fib) : Fib ≔ (
  t ≔ fibrancy.Σ (A .t) (a ↦ B a .t),
  f ≔ fibrancy.𝕗Σ (A .t) (a ↦ B a .t) (A .f) (a ↦ B a .f))

def Πf (A : Fib) (B : A .t → Fib) : Fib ≔ (
  t ≔ (a : A .t) → B a .t,
  f ≔ fibrancy.𝕗Π (A .t) (a ↦ B a .t) (A .f) (a ↦ B a .f))

def isContr (A : Fib) : Fib ≔ Σf A (center ↦ Πf A (a ↦ Idf A a center))
