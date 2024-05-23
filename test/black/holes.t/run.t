  $ narya -v holes.ny
   ￫ info[I0001]
   ￮ Axiom A assumed
  
   ￫ info[I0001]
   ￮ Axiom B assumed
  
   ￫ info[I0000]
   ￮ Constant id defined
  
   ￫ info[I0100]
   ￭ holes.ny
   7 | def f : A → B ≔ ?
     ^ hole ?0 generated:
       
       ----------------------------------------------------------------------
       A → B
  
   ￫ info[I0000]
   ￮ Constant f defined, containing 1 hole
  
   ￫ info[I0100]
   ￭ holes.ny
   9 | def f' : A → B ≔ x ↦ ?
     ^ hole ?1 generated:
       
       x : A
       ----------------------------------------------------------------------
       B
  
   ￫ info[I0000]
   ￮ Constant f' defined, containing 1 hole
  
   ￫ info[I0000]
   ￮ Constant ℕ defined
  
   ￫ info[I0100]
   ￭ holes.ny
   17 | | zero. ↦ ?
      ^ hole ?2 generated:
        
        m : ℕ
        n ≔ 0 : ℕ
        ----------------------------------------------------------------------
        ℕ
  
   ￫ info[I0100]
   ￭ holes.ny
   18 | | suc. n ↦ ?
      ^ hole ?3 generated:
        
        m : ℕ
        n : ℕ
        n0 ≔ suc. n : ℕ (not in scope)
        ----------------------------------------------------------------------
        ℕ
  
   ￫ info[I0000]
   ￮ Constant plus defined, containing 2 holes
  
   ￫ info[I0001]
   ￮ Axiom P assumed
  
   ￫ info[I0100]
   ￭ holes.ny
   23 | def anop : ℕ → ℕ → (x : ℕ) → P x ≔ n n0 n ↦ ?
      ^ hole ?4 generated:
        
        n1 : ℕ (not in scope)
        n0 : ℕ
        n : ℕ
        ----------------------------------------------------------------------
        P n
  
   ￫ info[I0000]
   ￮ Constant anop defined, containing 1 hole
  
   ￫ info[I0100]
   ￭ holes.ny
   26 | def anop' : ℕ → ℕ → (x : ℕ) → P x ≔ n0 n n ↦ ?
      ^ hole ?5 generated:
        
        n0 : ℕ
        n1 : ℕ (not in scope)
        n : ℕ
        ----------------------------------------------------------------------
        P n
  
   ￫ info[I0000]
   ￮ Constant anop' defined, containing 1 hole
  
   ￫ info[I0100]
   ￭ holes.ny
   28 | def anop'' : ℕ → ℕ → (x : ℕ) → P x ≔ n _ n ↦ ?
      ^ hole ?6 generated:
        
        n0 : ℕ (not in scope)
        H : ℕ (not in scope)
        n : ℕ
        ----------------------------------------------------------------------
        P n
  
   ￫ info[I0000]
   ￮ Constant anop'' defined, containing 1 hole
  
   ￫ info[I0100]
   ￭ holes.ny
   31 | def anop''' : ℕ → ℕ → (x : ℕ) → P x ≔ H _ n ↦ ?
      ^ hole ?7 generated:
        
        H : ℕ
        H0 : ℕ (not in scope)
        n : ℕ
        ----------------------------------------------------------------------
        P n
  
   ￫ info[I0000]
   ￮ Constant anop''' defined, containing 1 hole
  
   ￫ info[I0000]
   ￮ Constant Σ defined
  
   ￫ info[I0100]
   ￭ holes.ny
   39 | def pp : Σ Type (X ↦ X) ≔ ( ? , ? )
      ^ hole ?8 generated:
        
        ----------------------------------------------------------------------
        Type
  
   ￫ info[I0100]
   ￭ holes.ny
   39 | def pp : Σ Type (X ↦ X) ≔ ( ? , ? )
      ^ hole ?9 generated:
        
        ----------------------------------------------------------------------
        pp .fst
  
   ￫ info[I0000]
   ￮ Constant pp defined, containing 2 holes
  
   ￫ info[I0100]
   ￭ holes.ny
   42 | def pp' : Σ Type (X ↦ X) ≔ ( id ? , ? )
      ^ hole ?10 generated:
        
        ----------------------------------------------------------------------
        Type
  
   ￫ info[I0100]
   ￭ holes.ny
   42 | def pp' : Σ Type (X ↦ X) ≔ ( id ? , ? )
      ^ hole ?11 generated:
        
        ----------------------------------------------------------------------
        ?10
  
   ￫ info[I0000]
   ￮ Constant pp' defined, containing 2 holes
  
   ￫ info[I0100]
   ￭ holes.ny
   48 |   baz : ?,
      ^ hole ?12 generated:
        
        bar : ℕ
        ----------------------------------------------------------------------
        Type
  
   ￫ info[I0000]
   ￮ Constant foo defined, containing 1 hole
  
   ￫ info[I0100]
   ￭ holes.ny
   53 |   baz : (x:bar) → ?,
      ^ hole ?13 generated:
        
        bar : Type
        x : bar
        ----------------------------------------------------------------------
        Type
  
   ￫ info[I0000]
   ￮ Constant foo' defined, containing 1 hole
  
   ￫ info[I0100]
   ￭ holes.ny
   57 |   one : ?,
      ^ hole ?14 generated:
        
        A : Type
        B : Type
        x : A
        y : B
        ----------------------------------------------------------------------
        Type
  
   ￫ info[I0000]
   ￮ Constant gel0 defined, containing 1 hole
  
   ￫ info[I0100]
   ￭ holes.ny
   62 |   two : ?
      ^ hole ?15 generated:
        
        A : Type
        B : Type
        x : A
        y : B
        one : Type
        ----------------------------------------------------------------------
        Type
  
   ￫ info[I0000]
   ￮ Constant gel1 defined, containing 1 hole
  
   ￫ info[I0100]
   ￭ holes.ny
   66 |   one : ?,
      ^ hole ?16 generated:
        
        A : Type
        B : Type
        x : A
        y : B
        ----------------------------------------------------------------------
        Type
  
   ￫ info[I0100]
   ￭ holes.ny
   67 |   two : ?
      ^ hole ?17 generated:
        
        A : Type
        B : Type
        x : A
        y : B
        one : ?16
        ----------------------------------------------------------------------
        Type
  
   ￫ info[I0000]
   ￮ Constant gel2 defined, containing 2 holes
  
   ￫ info[I0100]
   ￭ holes.ny
   71 | | x .one : ?
      ^ hole ?18 generated:
        
        A : Type
        B : Type
        x.0 : A
        x.1 : B
        x : gel3 A B x.0 x.1
        ----------------------------------------------------------------------
        Type
  
   ￫ info[I0100]
   ￭ holes.ny
   72 | | x .two : ?
      ^ hole ?19 generated:
        
        A : Type
        B : Type
        x.0 : A
        x.1 : B
        x : gel3 A B x.0 x.1
        ----------------------------------------------------------------------
        Type
  
   ￫ info[I0000]
   ￮ Constant gel3 defined, containing 2 holes
  
   ￫ info[I0001]
   ￮ Axiom C assumed
  
   ￫ info[I0000]
   ￮ Constant AC defined
  
   ￫ info[I0100]
   ￭ holes.ny
   83 |   a ≔ ?,
      ^ hole ?20 generated:
        
        ----------------------------------------------------------------------
        ℕ → A
  
   ￫ info[I0100]
   ￭ holes.ny
   84 |   c ≔ ?
      ^ hole ?21 generated:
        
        ----------------------------------------------------------------------
        C (ac .a 0)
  
   ￫ info[I0000]
   ￮ Constant ac defined, containing 2 holes
  
   ￫ info[I0000]
   ￮ Constant ida defined
  
   ￫ info[I0000]
   ￮ Constant ideqid defined
  
  u u0 u1 ↦ u1
    : refl Π A A (refl A) (_ ↦ A) (_ ↦ A) (_ ⤇ refl A) ida ida
  
   ￫ info[I0000]
   ￮ Constant ideqid' defined
  
  u u0 u00 ↦ u00
    : refl Π A A (refl A) (_ ↦ A) (_ ↦ A) (_ ⤇ refl A) ida ida
  
   ￫ info[I0100]
   ￭ holes.ny
   98 | def ideqid'' : Id (A -> A) ida ida := ((x |-> x) : Id (A -> A ) ida ida -> Id (A -> A) ida ida) (u u u |-> ?)
      ^ hole ?22 generated:
        
        u1 : A (not in scope)
        u0 : A (not in scope)
        u : refl A u1 u0
        ----------------------------------------------------------------------
        refl A u1 u0
  
   ￫ info[I0000]
   ￮ Constant ideqid'' defined, containing 1 hole
  
   ￫ info[I0100]
   ￭ holes.ny
   101 | def afam : Type → Type ≔ X ↦ id ?
       ^ hole ?23 generated:
         
         X : Type
         ----------------------------------------------------------------------
         Type
  
   ￫ info[I0000]
   ￮ Constant afam defined, containing 1 hole
  
   ￫ info[I0000]
   ￮ Constant idafam defined
  
   ￫ error[E3000]
   ￮ There are open holes
  
  [1]

  $ narya -v -dtt dtt-holes.ny
   ￫ info[I0000]
   ￮ Constant f defined
  
   ￫ info[I0100]
   ￭ dtt-holes.ny
   4 | def g (X : Type) : Type⁽ᵈ⁾ X ≔ (f ?)⁽ᵈ⁾
     ^ hole ?0 generated:
       
       X : Type (blocked by modal lock)
       ----------------------------------------------------------------------
       Type
  
   ￫ error[E0401]
   ￭ dtt-holes.ny
   4 | def g (X : Type) : Type⁽ᵈ⁾ X ≔ (f ?)⁽ᵈ⁾
     ^ term synthesized type
         Type⁽ᵈ⁾ ?0
       but is being checked against type
         Type⁽ᵈ⁾ X
  
  [1]
