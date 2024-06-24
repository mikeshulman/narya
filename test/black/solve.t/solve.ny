def ℕ : Type ≔ data [ zero. | suc. (_:ℕ) ]

def Nat : Type ≔ ?

solve 0 ≔ ℕ

def plus (x y : ℕ) : ℕ ≔ ?

solve 1 ≔ match y [ zero. ↦ ? | suc. z ↦ ? ]

solve 2 ≔ x

solve 3 ≔ suc. (plus x z)

echo plus 4 5
