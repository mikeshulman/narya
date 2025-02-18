  $ narya -v sqrt.ny
   ￫ info[I0001]
   ￮ axiom A assumed
  
   ￫ info[I0000]
   ￮ constant √A defined
  
   ￫ info[I0001]
   ￮ axiom s0 assumed
  
   ￫ info[I0001]
   ￮ axiom s1 assumed
  
   ￫ info[I0001]
   ￮ axiom s2 assumed
  
  s2 .root.1
    : A
  
   ￫ info[I0001]
   ￮ axiom s00 assumed
  
   ￫ info[I0001]
   ￮ axiom s01 assumed
  
   ￫ info[I0001]
   ￮ axiom s10 assumed
  
   ￫ info[I0001]
   ￮ axiom s11 assumed
  
   ￫ info[I0001]
   ￮ axiom s02 assumed
  
   ￫ info[I0001]
   ￮ axiom s12 assumed
  
   ￫ info[I0001]
   ￮ axiom s20 assumed
  
   ￫ info[I0001]
   ￮ axiom s21 assumed
  
   ￫ info[I0001]
   ￮ axiom s22 assumed
  
  sym s22 .root.2
    : refl A (s02 .root.1) (s12 .root.1)
  
  s22 .root.2
    : refl A (s20 .root.1) (s21 .root.1)
  
  s2⁽¹ᵉ⁾ .root.2
    : refl A (refl s0 .root.1) (refl s1 .root.1)
  
  refl s2 .root.2
    : refl A (s2 .root.1) (s2 .root.1)
  
  s0⁽ᵉᵉ⁾ .root.2
    : refl A (refl s0 .root.1) (refl s0 .root.1)
  
  s0⁽ᵉᵉ⁾ .root.2
    : refl A (refl s0 .root.1) (refl s0 .root.1)
  
   ￫ info[I0001]
   ￮ axiom B assumed
  
   ￫ info[I0001]
   ￮ axiom f assumed
  
   ￫ info[I0000]
   ￮ constant √f defined
  
   ￫ info[I0001]
   ￮ axiom b0 assumed
  
   ￫ info[I0001]
   ￮ axiom b1 assumed
  
   ￫ info[I0001]
   ￮ axiom b2 assumed
  
  f b0 b1 b2
    : A
  
   ￫ info[I0001]
   ￮ axiom t00 assumed
  
   ￫ info[I0001]
   ￮ axiom t01 assumed
  
   ￫ info[I0001]
   ￮ axiom t10 assumed
  
   ￫ info[I0001]
   ￮ axiom t11 assumed
  
   ￫ info[I0001]
   ￮ axiom t02 assumed
  
   ￫ info[I0001]
   ￮ axiom t12 assumed
  
   ￫ info[I0001]
   ￮ axiom t20 assumed
  
   ￫ info[I0001]
   ￮ axiom t21 assumed
  
   ￫ info[I0001]
   ￮ axiom t22 assumed
  
  refl f t00 t01 t02 t10 t11 t12 t20 t21 t22
    : refl A (f t00 t10 t20) (f t01 t11 t21)
  
   ￫ info[I0001]
   ￮ axiom a assumed
  
   ￫ info[I0000]
   ￮ constant s2' defined
  
  a
    : A
  
  refl a
    : refl A a a
  
   ￫ info[I0000]
   ￮ constant ID defined
  
   ￫ info[I0000]
   ￮ constant √IDA defined
  
   ￫ info[I0000]
   ￮ constant η defined
  
   ￫ info[I0001]
   ￮ axiom a0 assumed
  
   ￫ info[I0001]
   ￮ axiom a1 assumed
  
   ￫ info[I0001]
   ￮ axiom a2 assumed
  
  a0
    : A
  
  a1
    : A
  
  a2
    : refl A a0 a1
  
   ￫ info[I0001]
   ￮ axiom u0 assumed
  
   ￫ info[I0001]
   ￮ axiom u1 assumed
  
   ￫ info[I0001]
   ￮ axiom u2 assumed
  
  u2 .root.1
    : ID A
  
   ￫ info[I0000]
   ￮ constant u2' defined, containing 2 holes
  
   ￫ info[I3003]
   ￮ hole ?0:
     
     ----------------------------------------------------------------------
     refl ID A A (refl A) (refl u0 .root.1) (refl u1 .root.1)
  
   ￫ info[I3003]
   ￮ hole ?1:
     
     ----------------------------------------------------------------------
     ID A
  
   ￫ info[I0001]
   ￮ axiom u00 assumed
  
   ￫ info[I0001]
   ￮ axiom u01 assumed
  
   ￫ info[I0001]
   ￮ axiom u02 assumed
  
   ￫ info[I0001]
   ￮ axiom u10 assumed
  
   ￫ info[I0001]
   ￮ axiom u11 assumed
  
   ￫ info[I0001]
   ￮ axiom u12 assumed
  
   ￫ info[I0001]
   ￮ axiom u20 assumed
  
   ￫ info[I0001]
   ￮ axiom u21 assumed
  
   ￫ info[I0001]
   ￮ axiom u22 assumed
  
  sym u22 .root.2
    : refl ID A A (refl A) (u02 .root.1) (u12 .root.1)
  
  u22 .root.2
    : refl ID A A (refl A) (u20 .root.1) (u21 .root.1)
  
   ￫ info[I0000]
   ￮ constant u22' defined, containing 3 holes
  
   ￫ info[I3003]
   ￮ hole ?2:
     
     ----------------------------------------------------------------------
     ID⁽ᵉᵉ⁾ A A (refl A) A A (refl A) (refl A) (refl A) A⁽ᵉᵉ⁾
       (refl u00 .root.1) (refl u01 .root.1) (u02⁽¹ᵉ⁾ .root.2)
       (refl u10 .root.1) (refl u11 .root.1) (u12⁽¹ᵉ⁾ .root.2)
       (u20⁽¹ᵉ⁾ .root.2) (u21⁽¹ᵉ⁾ .root.2)
  
   ￫ info[I3003]
   ￮ hole ?3:
     
     ----------------------------------------------------------------------
     refl ID A A (refl A) (u20 .root.1) (u21 .root.1)
  
   ￫ info[I3003]
   ￮ hole ?4:
     
     ----------------------------------------------------------------------
     refl ID A A (refl A) (u02 .root.1) (u12 .root.1)
  
   ￫ error[E3002]
   ￮ file $TESTCASE_ROOT/sqrt.ny contains open holes
  
  [1]


  $ narya -v isfibrant.ny
   ￫ info[I0000]
   ￮ constant isFibrant defined
  
   ￫ info[I0000]
   ￮ constant Fib defined
  
   ￫ info[I0000]
   ￮ constant Idf defined
  
   ￫ info[I0000]
   ￮ constant transport defined
  
   ￫ info[I0000]
   ￮ constant concat defined
  
   ￫ info[I0000]
   ￮ constant inverse defined
  
   ￫ info[I0000]
   ￮ constant transport2 defined
  
   ￫ info[I0000]
   ￮ constant refl_transport_1 defined
  
   ￫ info[I0000]
   ￮ constant refl_transport_2 defined
  
   ￫ info[I0000]
   ￮ constant Idf2 defined
  
   ￫ info[I0000]
   ￮ constant concat_p1 defined
  
   ￫ info[I0000]
   ￮ constant J defined
  
   ￫ info[I0000]
   ￮ constant Sqf defined
  
   ￫ info[I0000]
   ￮ constant conn defined
  
   ￫ info[I0000]
   ￮ constant coconn defined
  
   ￫ info[I0000]
   ￮ constant concat_1p defined
  
   ￫ info[I0000]
   ￮ constant Jβ defined
  
