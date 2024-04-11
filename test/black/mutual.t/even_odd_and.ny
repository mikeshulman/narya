{` This version of even_odd_sig uses mutual-induction syntax. `}

def ℕ : Type ≔ data [ zero. | suc. (_ : ℕ) ]

def even : ℕ → Type ≔ data [
| even_zero. : even zero.
| even_suc. : (n:ℕ) → odd n → even (suc. n)
]

and odd : ℕ → Type ≔ data [
| odd_suc. : (n:ℕ) → even n → odd (suc. n)
]

def sum (A B : Type) : Type ≔ data [ inl. (a:A) | inr. (b:B) ]

def even_or_odd_suc (n:ℕ) : sum (even n) (odd n) → sum (even (suc. n)) (odd (suc. n)) ≔ [
| inl. e ↦ inr. (odd_suc. n e)
| inr. o ↦ inl. (even_suc. n o)
]

def all_even_or_odd (n:ℕ) : sum (even n) (odd n) ≔ match n [
| zero. ↦ inl. even_zero.
| suc. n ↦ even_or_odd_suc n (all_even_or_odd n)
]
