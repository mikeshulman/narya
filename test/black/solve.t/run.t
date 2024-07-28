  $ narya -v -fake-interact solve.ny
   ￫ info[I0000]
   ￮ constant ℕ defined
  
   ￫ info[I0000]
   ￮ constant Nat defined, containing 1 hole
  
   ￫ info[I3003]
   ￮ hole ?0:
     
     ----------------------------------------------------------------------
     Type
  
   ￫ info[I0005]
   ￮ hole solved
  
   ￫ info[I0000]
   ￮ constant plus defined, containing 1 hole
  
   ￫ info[I3003]
   ￮ hole ?1:
     
     x : ℕ
     y : ℕ
     ----------------------------------------------------------------------
     ℕ
  
   ￫ info[I0005]
   ￮ hole solved, containing 2 new holes
  
   ￫ info[I3003]
   ￮ hole ?2:
     
     x : ℕ
     y ≔ 0 : ℕ
     ----------------------------------------------------------------------
     ℕ
  
   ￫ info[I3003]
   ￮ hole ?3:
     
     x : ℕ
     z : ℕ
     y ≔ suc. z : ℕ
     ----------------------------------------------------------------------
     ℕ
  
   ￫ info[I0005]
   ￮ hole solved
  
   ￫ info[I0005]
   ￮ hole solved
  
  9
    : ℕ
  
   ￫ info[I0000]
   ￮ constant Σ defined
  
   ￫ info[I0000]
   ￮ constant 𝔹 defined
  
   ￫ info[I0000]
   ￮ constant Jd defined
  
   ￫ info[I0000]
   ￮ constant invol1 defined, containing 2 holes
  
   ￫ info[I3003]
   ￮ hole ?4:
     
     not ≔ _let.0.not{…} : 𝔹 → 𝔹
     ----------------------------------------------------------------------
     𝔹 → 𝔹
  
   ￫ info[I3003]
   ￮ hole ?5:
     
     not ≔ _let.0.not{…} : 𝔹 → 𝔹
     ----------------------------------------------------------------------
     (x : 𝔹) → Jd 𝔹 x (invol1 .fst (invol1 .fst x))
  
   ￫ info[I0005]
   ￮ hole solved
  
   ￫ info[I0005]
   ￮ hole solved
  
   ￫ info[I0000]
   ￮ constant invol2 defined, containing 1 hole
  
   ￫ info[I3003]
   ￮ hole ?6:
     
     ----------------------------------------------------------------------
     Σ (𝔹 → 𝔹) (f ↦ (x : 𝔹) → Jd 𝔹 x (f (f x)))
  
   ￫ info[I0005]
   ￮ hole solved, containing 1 new hole
  
   ￫ info[I3003]
   ￮ hole ?7:
     
     not ≔ _let.1.not{…} : 𝔹 → 𝔹
     ----------------------------------------------------------------------
     (x : 𝔹) → Jd 𝔹 x (_let.1.not{…} (_let.1.not{…} x))
  
   ￫ info[I0005]
   ￮ hole solved
  
