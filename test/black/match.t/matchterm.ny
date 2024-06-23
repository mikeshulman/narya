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
{` We can quiet the hint this way: `}
def doublematch' (n : ℕ) : bool ≔ match n [ zero. ↦ false. | suc. k ↦ match n return _ ↦ _ [ zero. ↦ true. | suc. _ ↦ false. ]]

def ⊤ : Type ≔ sig ()
def zero_or_suc : ℕ → Type ≔ [ zero. ↦ ⊤ | suc. _ ↦ ⊤ ]
{` To prove this, we have to specialize the type in the branches, requiring a "return" annotation on the match: `}
def plus_zero_or_suc (m n : ℕ) : zero_or_suc (plus m n) ≔ match (plus m n) return x ↦ zero_or_suc x [ zero. ↦ () | suc. _ ↦ () ]

{` We try an indexed inductive type `}
def Vec (A : Type) : ℕ → Type ≔ data [ nil. : Vec A zero. | cons. (n:ℕ) (_:A) (_:Vec A n) : Vec A (suc. n) ]
def idvec (A : Type) (n:ℕ) : Vec A n → Vec A n ≔ [ nil. ↦ nil. | cons. n x xs ↦ cons. n x (idvec A n xs) ]
def nil_or_cons (n:ℕ) (A:Type) : Vec A n → Type ≔ [ nil. ↦ ⊤ | cons. _ _ _ ↦ ⊤ ]
def idvec_nil_or_cons (n:ℕ) (A:Type) (v : Vec A n) : nil_or_cons n A (idvec A n v) ≔ match (idvec A n v) return m w ↦ nil_or_cons m A w [ nil. ↦ () | cons. _ _ _ ↦ () ]
