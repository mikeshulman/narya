  $ narya -v holes.ny
   ￫ info[I0001]
   ￮ axiom A assumed
  
   ￫ info[I0001]
   ￮ axiom B assumed
  
  B
    : Type
  
   ￫ info[I0000]
   ￮ constant id defined
  
   ￫ info[I0001]
   ￮ axiom b assumed
  
   ￫ info[I0001]
   ￮ axiom g assumed
  
   ￫ info[I0000]
   ￮ constant f defined, containing 1 hole
  
   ￫ info[I3003]
   ￮ hole ?0:
     
     ----------------------------------------------------------------------
     A → B
  
   ￫ info[I0001]
   ￮ axiom a_very_long_variable assumed
  
   ￫ info[I0001]
   ￮ axiom a_very_long_function assumed
  
   ￫ info[I0000]
   ￮ constant f' defined, containing 1 hole
  
   ￫ info[I3003]
   ￮ hole ?1:
     
     ----------------------------------------------------------------------
     A → B
  
   ￫ info[I0000]
   ￮ constant ℕ defined
  
   ￫ info[I0000]
   ￮ constant plus defined, containing 2 holes
  
   ￫ info[I3003]
   ￮ hole ?2:
     
     m : ℕ
     n ≔ 0 : ℕ
     ----------------------------------------------------------------------
     ℕ
  
   ￫ info[I3003]
   ￮ hole ?3:
     
     m : ℕ
     n : ℕ
     n0 ≔ suc. n : ℕ (not in scope)
     ----------------------------------------------------------------------
     ℕ
  
   ￫ info[I0001]
   ￮ axiom P assumed
  
   ￫ info[I0000]
   ￮ constant anop defined, containing 1 hole
  
   ￫ info[I3003]
   ￮ hole ?4:
     
     n1 : ℕ (not in scope)
     n0 : ℕ
     n : ℕ
     ----------------------------------------------------------------------
     P n
  
   ￫ info[I0000]
   ￮ constant anop' defined, containing 1 hole
  
   ￫ info[I3003]
   ￮ hole ?5:
     
     n0 : ℕ
     n1 : ℕ (not in scope)
     n : ℕ
     ----------------------------------------------------------------------
     P n
  
   ￫ info[I0000]
   ￮ constant anop'' defined, containing 1 hole
  
   ￫ info[I3003]
   ￮ hole ?6:
     
     n0 : ℕ (not in scope)
     H : ℕ (not in scope)
     n : ℕ
     ----------------------------------------------------------------------
     P n
  
   ￫ info[I0000]
   ￮ constant anop''' defined, containing 1 hole
  
   ￫ info[I3003]
   ￮ hole ?7:
     
     H : ℕ
     H0 : ℕ (not in scope)
     n : ℕ
     ----------------------------------------------------------------------
     P n
  
   ￫ info[I0000]
   ￮ constant Σ defined
  
   ￫ info[I0000]
   ￮ constant pp defined, containing 2 holes
  
   ￫ info[I3003]
   ￮ hole ?8:
     
     ----------------------------------------------------------------------
     Type
  
   ￫ info[I3003]
   ￮ hole ?9:
     
     ----------------------------------------------------------------------
     pp .fst
  
   ￫ info[I0000]
   ￮ constant pp' defined, containing 2 holes
  
   ￫ info[I3003]
   ￮ hole ?10:
     
     ----------------------------------------------------------------------
     Type
  
   ￫ info[I3003]
   ￮ hole ?11:
     
     ----------------------------------------------------------------------
     ?10{…}
  
   ￫ info[I0000]
   ￮ constant foo defined, containing 1 hole
  
   ￫ info[I3003]
   ￮ hole ?12:
     
     bar : ℕ
     ----------------------------------------------------------------------
     Type
  
   ￫ info[I0000]
   ￮ constant foo' defined, containing 1 hole
  
   ￫ info[I3003]
   ￮ hole ?13:
     
     bar : Type
     x : bar
     ----------------------------------------------------------------------
     Type
  
   ￫ info[I0000]
   ￮ constant gel0 defined, containing 1 hole
  
   ￫ info[I3003]
   ￮ hole ?14:
     
     A : Type
     B : Type
     x : A
     y : B
     ----------------------------------------------------------------------
     Type
  
   ￫ info[I0000]
   ￮ constant gel1 defined, containing 1 hole
  
   ￫ info[I3003]
   ￮ hole ?15:
     
     A : Type
     B : Type
     x : A
     y : B
     one : Type
     ----------------------------------------------------------------------
     Type
  
   ￫ info[I0000]
   ￮ constant gel2 defined, containing 2 holes
  
   ￫ info[I3003]
   ￮ hole ?16:
     
     A : Type
     B : Type
     x : A
     y : B
     ----------------------------------------------------------------------
     Type
  
   ￫ info[I3003]
   ￮ hole ?17:
     
     A : Type
     B : Type
     x : A
     y : B
     one : ?16{…}
     ----------------------------------------------------------------------
     Type
  
   ￫ info[I0000]
   ￮ constant gel3 defined, containing 2 holes
  
   ￫ info[I3003]
   ￮ hole ?18:
     
     A : Type
     B : Type
     x.0 : A
     x.1 : B
     x.2 : gel3 A B x.0 x.1
     ----------------------------------------------------------------------
     Type
  
   ￫ info[I3003]
   ￮ hole ?19:
     
     A : Type
     B : Type
     x.0 : A
     x.1 : B
     x.2 : gel3 A B x.0 x.1
     ----------------------------------------------------------------------
     Type
  
   ￫ info[I0001]
   ￮ axiom C assumed
  
   ￫ info[I0000]
   ￮ constant AC defined
  
   ￫ info[I0000]
   ￮ constant ac defined, containing 2 holes
  
   ￫ info[I3003]
   ￮ hole ?20:
     
     ----------------------------------------------------------------------
     ℕ → A
  
   ￫ info[I3003]
   ￮ hole ?21:
     
     ----------------------------------------------------------------------
     C (ac .a 0)
  
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
  
   ￫ info[I0000]
   ￮ constant ideqid'' defined, containing 1 hole
  
   ￫ info[I3003]
   ￮ hole ?22:
     
     u1 : A (not in scope)
     u0 : A (not in scope)
     u : refl A u1 u0
     ----------------------------------------------------------------------
     refl A u1 u0
  
   ￫ info[I0000]
   ￮ constant afam defined, containing 1 hole
  
   ￫ info[I3003]
   ￮ hole ?23:
     
     X : Type
     ----------------------------------------------------------------------
     Type
  
   ￫ info[I0000]
   ￮ constant idafam defined
  
   ￫ error[E3002]
   ￮ file holes.ny contains open holes
  
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

No holes in echo:

  $ narya -e 'echo (? : Type)'
   ￫ error[E2002]
   ￭ command-line exec string
   1 | echo (? : Type)
     ^ command 'echo' cannot contain holes
  
  [1]

No holes in imported file

  $ echo 'def A : Type := ?' >to_import.ny

  $ narya -e 'import "to_import"'
   ￫ error[E2002]
   ￭ $TESTCASE_ROOT/to_import.ny
   1 | def A : Type := ?
     ^ imported file 'to_import' cannot contain holes
  
  [1]
