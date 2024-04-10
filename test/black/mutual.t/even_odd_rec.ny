` We can define even and odd predicates by mutual recursion.  We start with the natural numbers and the decidable propositions.
def ℕ : Type ≔ data [ zero. | suc. (_ : ℕ) ]
def ⊤ : Type ≔ sig ()
def ⊥ : Type ≔ data []

` The pair of "even" and "odd" will together inhabit this record type.
def even_odd_type : Type ≔ sig (
  even : ℕ → Type,
  odd : ℕ → Type,
)

` Now we can define them together, by mutual recursion
def even_odd : even_odd_type ≔ (
  even ≔ [
  | zero. ↦ ⊤
  | suc. n ↦ even_odd .odd n
  ],
  odd ≔ [
  | zero. ↦ ⊥
  | suc. n ↦ even_odd .even n
  ],
)

echo even_odd .even 8

echo even_odd .odd 8
