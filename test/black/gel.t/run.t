  $ narya -v gel.ny
   ￫ info[I0000]
   ￮ constant Gel defined
  
   ￫ info[I0001]
   ￮ axiom A assumed
  
   ￫ info[I0001]
   ￮ axiom B assumed
  
   ￫ info[I0001]
   ￮ axiom R assumed
  
   ￫ info[I0001]
   ￮ axiom a₀ assumed
  
   ￫ info[I0001]
   ￮ axiom a₁ assumed
  
   ￫ info[I0001]
   ￮ axiom a₂ assumed
  
   ￫ info[I0001]
   ￮ axiom b₀ assumed
  
   ￫ info[I0001]
   ￮ axiom b₁ assumed
  
   ￫ info[I0001]
   ￮ axiom b₂ assumed
  
   ￫ info[I0001]
   ￮ axiom r₀ assumed
  
   ￫ info[I0001]
   ￮ axiom r₁ assumed
  
   ￫ info[I0001]
   ￮ axiom M assumed
  
  sym M
    : refl Gel A A (refl A) B B (refl B) R R (refl R) a₀ a₁ a₂ b₀ b₁ b₂
        (_ ≔ r₀) (_ ≔ r₁)
  
  sym M .ungel
    : refl R a₀ a₁ a₂ b₀ b₁ b₂ r₀ r₁
  
   ￫ info[I0000]
   ￮ constant eta defined
  
