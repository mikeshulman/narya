  $ narya -dtt -v sst.ny
   ￫ info[I0000]
   ￮ Constant Gel defined
  
   ￫ info[I0000]
   ￮ Constant SST defined
  
   ￫ info[I0000]
   ￮ Constant 0s defined
  
   ￫ info[I0000]
   ￮ Constant 1s defined
  
   ￫ info[I0000]
   ￮ Constant 2s defined
  
   ￫ info[I0000]
   ￮ Constant 3s defined
  
   ￫ info[I0000]
   ￮ Constant eq defined
  
   ￫ info[I0000]
   ￮ Constant Sing defined
  
   ￫ info[I0001]
   ￮ Axiom A assumed
  
  A
    : Type
  
   ￫ info[I0001]
   ￮ Axiom a₀ assumed
  
   ￫ info[I0001]
   ￮ Axiom a₁ assumed
  
  Gel A (y ↦ eq A a₀ y) a₁
    : Type
  
   ￫ info[I0001]
   ￮ Axiom a₀₁ assumed
  
   ￫ info[I0001]
   ￮ Axiom a₂ assumed
  
   ￫ info[I0001]
   ￮ Axiom a₀₂ assumed
  
   ￫ info[I0001]
   ￮ Axiom a₁₂ assumed
  
  Gel⁽ᵈ⁾ A (Gel A (y ↦ eq A a₀ y)) (y ↦ eq A a₁ y)
    (y ⤇ eq⁽ᵈ⁾ A (Gel A (y0 ↦ eq A a₀ y0)) a₁ a₀₁ y.0 y.1) a₂ a₀₂ a₁₂
    : Type
  
   ￫ info[I0001]
   ￮ Axiom a₀₁₂ assumed
  
   ￫ info[I0001]
   ￮ Axiom a₃ assumed
  
   ￫ info[I0001]
   ￮ Axiom a₀₃ assumed
  
   ￫ info[I0001]
   ￮ Axiom a₁₃ assumed
  
   ￫ info[I0001]
   ￮ Axiom a₀₁₃ assumed
  
   ￫ info[I0001]
   ￮ Axiom a₂₃ assumed
  
   ￫ info[I0001]
   ￮ Axiom a₀₂₃ assumed
  
   ￫ info[I0001]
   ￮ Axiom a₁₂₃ assumed
  
  Gel⁽ᵈᵈ⁾ A (Gel A (y ↦ eq A a₀ y)) (Gel A (y ↦ eq A a₁ y))
    (Gel⁽ᵈ⁾ A (Gel A (y ↦ eq A a₀ y)) (y ↦ eq A a₁ y)
       (y ⤇ eq⁽ᵈ⁾ A (Gel A (y0 ↦ eq A a₀ y0)) a₁ a₀₁ y.0 y.1)) (y ↦ eq A a₂ y)
    (y ⤇ eq⁽ᵈ⁾ A (Gel A (y0 ↦ eq A a₀ y0)) a₂ a₀₂ y.0 y.1)
    (y ⤇ eq⁽ᵈ⁾ A (Gel A (y0 ↦ eq A a₁ y0)) a₂ a₁₂ y.0 y.1)
    (y ⤇
     eq⁽ᵈᵈ⁾ A (Gel A (y0 ↦ eq A a₀ y0)) (Gel A (y0 ↦ eq A a₁ y0))
       (Gel⁽ᵈ⁾ A (Gel A (y0 ↦ eq A a₀ y0)) (y0 ↦ eq A a₁ y0)
          (y0 ⤇ eq⁽ᵈ⁾ A (Gel A (y1 ↦ eq A a₀ y1)) a₁ a₀₁ y0.0 y0.1)) a₂ a₀₂ a₁₂
       a₀₁₂ y.00 y.01 y.10 y.11) a₃ a₀₃ a₁₃ a₀₁₃ a₂₃ a₀₂₃ a₁₂₃
    : Type
  
   ￫ info[I0000]
   ￮ Constant sst.∅ defined
  
   ￫ info[I0000]
   ￮ Constant sst.𝟙 defined
  
   ￫ info[I0000]
   ￮ Constant sst.prod defined
  
   ￫ info[I0000]
   ￮ Constant sst.Σ defined
  
   ￫ info[I0000]
   ￮ Constant sst.const defined
  
   ￫ info[I0000]
   ￮ Constant sst.sum defined
  
   ￫ info[I0000]
   ￮ Constant ASST defined
  
   ￫ info[I0000]
   ￮ Constant sst.pt defined
  
   ￫ info[I0000]
   ￮ Constant sst.hom defined
  
   ￫ info[I0000]
   ￮ Constant sst.id defined
  
   ￫ info[I0000]
   ￮ Constant sst.comp defined
  
   ￫ info[I0000]
   ￮ Constant sst.abort defined
  
   ￫ info[I0000]
   ￮ Constant sst.uniq defined
  
   ￫ info[I0000]
   ￮ Constant sst.pair defined
  
   ￫ info[I0000]
   ￮ Constant sst.abortz defined
  
   ￫ info[I0000]
   ￮ Constant sst.const_abort defined
  
   ￫ info[I0000]
   ￮ Constant sst.copair defined
  
  $ narya -arity 2 -direction p -external -v sct.ny
   ￫ info[I0000]
   ￮ Constant SCT defined
  
   ￫ info[I0000]
   ￮ Constant 0s defined
  
   ￫ info[I0000]
   ￮ Constant 1s defined
  
   ￫ info[I0000]
   ￮ Constant 2s defined
  
  $ narya -dtt -e "def foo (X:Type) : Type^(d) X := X^(d)"
   ￫ error[E0310]
   ￭ command-line exec string
   1 | def foo (X:Type) : Type^(d) X := X^(d)
     ^ variable locked behind external degeneracy
  
  [1]

  $ narya -dtt -e "axiom A : Type" -e "echo A^(d)"
   ￫ error[E0311]
   ￭ command-line exec string
   1 | echo A^(d)
     ^ axiom A locked behind external degeneracy
  
  [1]

  $ narya -dtt mutual.ny
   ￫ error[E3000]
   ￮ There are open holes
  
  [1]
