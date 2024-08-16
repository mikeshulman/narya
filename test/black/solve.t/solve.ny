def ℕ : Type ≔ data [ zero. | suc. (_:ℕ) ]

def Nat : Type ≔ ?

solve 0 ≔ ℕ

def plus (x y : ℕ) : ℕ ≔ ?

solve 1 ≔ match y [ zero. ↦ ? | suc. z ↦ ? ]

solve 2 ≔ x

solve 3 ≔ suc. (plus x z)

echo plus 4 5

{` holes can refer to global metas and depend on the value of previously filled holes `}

def Σ (A : Type) (B : A → Type) : Type ≔ sig ( fst : A, snd : B fst )

def 𝔹 : Type ≔ data [ false. | true. ]

def Jd (A : Type) (a : A) : A → Type ≔ data [ rfl. : Jd A a a ]

def invol1 : Σ (𝔹 → 𝔹) (f ↦ (x : 𝔹) → Jd 𝔹 x (f (f x))) ≔
  let not : 𝔹 → 𝔹 ≔ [ false. ↦ true. | true. ↦ false. ] in
  (?, ?)

solve 4 ≔ not

solve 5 ≔ [ true. ↦ rfl. | false. ↦ rfl. ]

{` holes can create global metas `}

def invol2 : Σ (𝔹 → 𝔹) (f ↦ (x : 𝔹) → Jd 𝔹 x (f (f x))) ≔ ?

solve 6 ≔ let not : 𝔹 → 𝔹 ≔ [ false. ↦ true. | true. ↦ false. ] in (not, ?)

solve 7 ≔ [ true. ↦ rfl. | false. ↦ rfl. ]
