  $ narya -v holes.ny
   ￫ info[I0001]
   ￮ axiom A assumed
  
   ￫ info[I0001]
   ￮ axiom B assumed
  
   ￫ info[I0000]
   ￮ constant id defined
  
   ￫ info[I0100]
   ￮ hole ?0 generated:
     
     ----------------------------------------------------------------------
     A → B
  
   ￫ info[I0000]
   ￮ constant f defined, containing 1 hole
  
   ￫ info[I0100]
   ￮ hole ?1 generated:
     
     x : A
     ----------------------------------------------------------------------
     B
  
   ￫ info[I0000]
   ￮ constant f' defined, containing 1 hole
  
   ￫ info[I0000]
   ￮ constant ℕ defined
  
   ￫ info[I0100]
   ￮ hole ?2 generated:
     
     m : ℕ
     n ≔ 0 : ℕ
     ----------------------------------------------------------------------
     ℕ
  
   ￫ info[I0100]
   ￮ hole ?3 generated:
     
     m : ℕ
     n : ℕ
     n0 ≔ suc. n : ℕ (not in scope)
     ----------------------------------------------------------------------
     ℕ
  
   ￫ info[I0000]
   ￮ constant plus defined, containing 2 holes
  
   ￫ info[I0001]
   ￮ axiom P assumed
  
   ￫ info[I0100]
   ￮ hole ?4 generated:
     
     n1 : ℕ (not in scope)
     n0 : ℕ
     n : ℕ
     ----------------------------------------------------------------------
     P n
  
   ￫ info[I0000]
   ￮ constant anop defined, containing 1 hole
  
   ￫ info[I0100]
   ￮ hole ?5 generated:
     
     n0 : ℕ
     n1 : ℕ (not in scope)
     n : ℕ
     ----------------------------------------------------------------------
     P n
  
   ￫ info[I0000]
   ￮ constant anop' defined, containing 1 hole
  
   ￫ info[I0100]
   ￮ hole ?6 generated:
     
     n0 : ℕ (not in scope)
     H : ℕ (not in scope)
     n : ℕ
     ----------------------------------------------------------------------
     P n
  
   ￫ info[I0000]
   ￮ constant anop'' defined, containing 1 hole
  
   ￫ info[I0100]
   ￮ hole ?7 generated:
     
     H : ℕ
     H0 : ℕ (not in scope)
     n : ℕ
     ----------------------------------------------------------------------
     P n
  
   ￫ info[I0000]
   ￮ constant anop''' defined, containing 1 hole
  
   ￫ info[I0000]
   ￮ constant Σ defined
  
   ￫ info[I0100]
   ￮ hole ?8 generated:
     
     ----------------------------------------------------------------------
     Type
  
   ￫ info[I0100]
   ￮ hole ?9 generated:
     
     ----------------------------------------------------------------------
     pp .fst
  
   ￫ info[I0000]
   ￮ constant pp defined, containing 2 holes
  
   ￫ info[I0100]
   ￮ hole ?10 generated:
     
     ----------------------------------------------------------------------
     Type
  
   ￫ info[I0100]
   ￮ hole ?11 generated:
     
     ----------------------------------------------------------------------
     ?10{…}
  
   ￫ info[I0000]
   ￮ constant pp' defined, containing 2 holes
  
   ￫ info[I0100]
   ￮ hole ?12 generated:
     
     bar : ℕ
     ----------------------------------------------------------------------
     Type
  
   ￫ info[I0000]
   ￮ constant foo defined, containing 1 hole
  
   ￫ info[I0100]
   ￮ hole ?13 generated:
     
     bar : Type
     x : bar
     ----------------------------------------------------------------------
     Type
  
   ￫ info[I0000]
   ￮ constant foo' defined, containing 1 hole
  
   ￫ info[I0100]
   ￮ hole ?14 generated:
     
     A : Type
     B : Type
     x : A
     y : B
     ----------------------------------------------------------------------
     Type
  
   ￫ info[I0000]
   ￮ constant gel0 defined, containing 1 hole
  
   ￫ info[I0100]
   ￮ hole ?15 generated:
     
     A : Type
     B : Type
     x : A
     y : B
     one : Type
     ----------------------------------------------------------------------
     Type
  
   ￫ info[I0000]
   ￮ constant gel1 defined, containing 1 hole
  
   ￫ info[I0100]
   ￮ hole ?16 generated:
     
     A : Type
     B : Type
     x : A
     y : B
     ----------------------------------------------------------------------
     Type
  
   ￫ info[I0100]
   ￮ hole ?17 generated:
     
     A : Type
     B : Type
     x : A
     y : B
     one : ?16{…}
     ----------------------------------------------------------------------
     Type
  
   ￫ info[I0000]
   ￮ constant gel2 defined, containing 2 holes
  
   ￫ info[I0100]
   ￮ hole ?18 generated:
     
     A : Type
     B : Type
     x.0 : A
     x.1 : B
     x.2 : gel3 A B x.0 x.1
     ----------------------------------------------------------------------
     Type
  
   ￫ info[I0100]
   ￮ hole ?19 generated:
     
     A : Type
     B : Type
     x.0 : A
     x.1 : B
     x.2 : gel3 A B x.0 x.1
     ----------------------------------------------------------------------
     Type
  
   ￫ info[I0000]
   ￮ constant gel3 defined, containing 2 holes
  
   ￫ info[I0001]
   ￮ axiom C assumed
  
   ￫ info[I0000]
   ￮ constant AC defined
  
   ￫ info[I0100]
   ￮ hole ?20 generated:
     
     ----------------------------------------------------------------------
     ℕ → A
  
   ￫ info[I0100]
   ￮ hole ?21 generated:
     
     ----------------------------------------------------------------------
     C (ac .a 0)
  
   ￫ info[I0000]
   ￮ constant ac defined, containing 2 holes
  
   ￫ info[I0000]
   ￮ constant ida defined
  
   ￫ info[I0000]
   ￮ constant ideqid defined
  
  u u0 u1 ↦ u1
    : refl Π A A (refl A) (_ ↦ A) (_ ↦ A) (_ ⤇ refl A) ida ida
  
   ￫ info[I0000]
   ￮ constant ideqid' defined
  
  u u0 u00 ↦ u00
    : refl Π A A (refl A) (_ ↦ A) (_ ↦ A) (_ ⤇ refl A) ida ida
  
   ￫ info[I0100]
   ￮ hole ?22 generated:
     
     u1 : A (not in scope)
     u0 : A (not in scope)
     u : refl A u1 u0
     ----------------------------------------------------------------------
     refl A u1 u0
  
   ￫ info[I0000]
   ￮ constant ideqid'' defined, containing 1 hole
  
   ￫ info[I0100]
   ￮ hole ?23 generated:
     
     X : Type
     ----------------------------------------------------------------------
     Type
  
   ￫ info[I0000]
   ￮ constant afam defined, containing 1 hole
  
   ￫ info[I0000]
   ￮ constant idafam defined
  
   ￫ error[E3002]
   ￮ file $TESTCASE_ROOT/holes.ny contains open holes
  
  [1]

  $ narya -v -dtt dtt-holes.ny
   ￫ info[I0000]
   ￮ constant f defined
  
   ￫ error[E0401]
   ￭ $TESTCASE_ROOT/dtt-holes.ny
   4 | def g (X : Type) : Type⁽ᵈ⁾ X ≔ (f ?)⁽ᵈ⁾
     ^ term synthesized type
         Type⁽ᵈ⁾ ?0{…}
       but is being checked against type
         Type⁽ᵈ⁾ X
  
  [1]
