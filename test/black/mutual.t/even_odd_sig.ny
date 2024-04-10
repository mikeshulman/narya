` We can define even and odd predicates by mutual *induction*.  We start with the natural numbers.
def ℕ : Type ≔ data [ zero. | suc. (_ : ℕ) ]

` The pair of "even" and "odd" will together inhabit this record type.
def even_odd_type : Type ≔ sig (
  even : ℕ → Type,
  odd : ℕ → Type,
)

` Now we can define them together, by mutual induction.
def even_odd : even_odd_type ≔ (
  even ≔ data [
  | even_zero. : even_odd .even zero.
  | even_suc. : (n:ℕ) → even_odd .odd n → even_odd .even (suc. n)
  ],
  odd ≔ data [
  | odd_suc. : (n:ℕ) → even_odd .even n → even_odd .odd (suc. n)
  ],
)

` Then we pick out the two components and give them separate names.

def even ≔ even_odd .even

def odd ≔ even_odd .odd

` As a test, we prove that every natural number is either even or odd.  First we define "or".

def sum (A B : Type) : Type ≔ data [ inl. (a:A) | inr. (b:B) ]

` Now we need a helper lemma, since we can't pattern-match on an intermediate value inside a definition.
def even_or_odd_suc (n:ℕ) : sum (even n) (odd n) → sum (even (suc. n)) (odd (suc. n)) ≔ [
| inl. e ↦ inr. (odd_suc. n e)
| inr. o ↦ inl. (even_suc. n o)
]

` Finally we can prove the theorem.
def all_even_or_odd (n:ℕ) : sum (even n) (odd n) ≔ match n [
| zero. ↦ inl. even_zero.
| suc. n ↦ even_or_odd_suc n (all_even_or_odd n)
]
