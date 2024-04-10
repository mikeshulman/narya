` A version that defines families of canonical types by "recursion".
def ℕ : Type ≔ data [ zero. | suc. (_ : ℕ) ]

def even_odd_type : Type ≔ sig (
  even : ℕ → Type,
  odd : ℕ → Type,
)

def even_odd : even_odd_type ≔ (
  even ≔ [
  | zero. ↦ sig ()
  | suc. n ↦ sig (even_suc : even_odd .odd n)
  ],
  odd ≔ [
  | zero. ↦ data []
  | suc. n ↦ sig (odd_suc : even_odd .even n)
  ],
)

echo even_odd .even 8

echo even_odd .odd 8
