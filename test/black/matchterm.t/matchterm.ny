def ℕ : Type ≔ data [ zero. | suc. (_:ℕ) ]
def plus (m n : ℕ) : ℕ ≔ match n [ zero. ↦ m | suc. n ↦ suc. (plus m n) ]
def bool : Type ≔ data [ false. | true. ]
def plus_is_1 (m n : ℕ) : bool ≔ match (plus m n) [ zero. ↦ false. | suc. k ↦ match k [ zero. ↦ true. | suc. _ ↦ false. ]]
echo plus_is_1 0 1
echo plus_is_1 0 0
echo plus_is_1 1 0
echo plus_is_1 1 1
echo plus_is_1 0 2
def ⊥ : Type ≔ data [ ]
def contra (A C : Type) (a : A) (na : A → ⊥) : C ≔ match na a [ ]
def doublematch (n : ℕ) : bool ≔ match n [ zero. ↦ false. | suc. k ↦ match n [ zero. ↦ true. | suc. _ ↦ false. ]]
