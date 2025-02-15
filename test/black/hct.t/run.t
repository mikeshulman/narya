  $ narya -v hct.ny
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
  
  s22 .root.2
    : refl A (s02 .root.1) (s12 .root.1)
  
  s22 .root.2
    : refl A (s20 .root.1) (s21 .root.1)
  

  $ narya -v 2dct.ny
   ￫ info[I0001]
   ￮ axiom A assumed
  
   ￫ info[I0000]
   ￮ constant √√A defined
  
   ￫ info[I0001]
   ￮ axiom s000 assumed
  
   ￫ info[I0001]
   ￮ axiom s001 assumed
  
   ￫ info[I0001]
   ￮ axiom s002 assumed
  
   ￫ info[I0001]
   ￮ axiom s010 assumed
  
   ￫ info[I0001]
   ￮ axiom s011 assumed
  
   ￫ info[I0001]
   ￮ axiom s012 assumed
  
   ￫ info[I0001]
   ￮ axiom s020 assumed
  
   ￫ info[I0001]
   ￮ axiom s021 assumed
  
   ￫ info[I0001]
   ￮ axiom s022 assumed
  
   ￫ info[I0001]
   ￮ axiom s100 assumed
  
   ￫ info[I0001]
   ￮ axiom s101 assumed
  
   ￫ info[I0001]
   ￮ axiom s102 assumed
  
   ￫ info[I0001]
   ￮ axiom s110 assumed
  
   ￫ info[I0001]
   ￮ axiom s111 assumed
  
   ￫ info[I0001]
   ￮ axiom s112 assumed
  
   ￫ info[I0001]
   ￮ axiom s120 assumed
  
   ￫ info[I0001]
   ￮ axiom s121 assumed
  
   ￫ info[I0001]
   ￮ axiom s122 assumed
  
   ￫ info[I0001]
   ￮ axiom s200 assumed
  
   ￫ info[I0001]
   ￮ axiom s201 assumed
  
   ￫ info[I0001]
   ￮ axiom s202 assumed
  
   ￫ info[I0001]
   ￮ axiom s210 assumed
  
   ￫ info[I0001]
   ￮ axiom s211 assumed
  
   ￫ info[I0001]
   ￮ axiom s212 assumed
  
   ￫ info[I0001]
   ￮ axiom s220 assumed
  
   ￫ info[I0001]
   ￮ axiom s221 assumed
  
   ￫ info[I0001]
   ￮ axiom s222 assumed
  
  s222 .rroot.23
    : refl A (s022 .rroot.12) (s122 .rroot.12)
  
  s222 .rroot.23
    : refl A (s202 .rroot.12) (s212 .rroot.12)
  
  s222 .rroot.23
    : refl A (s220 .rroot.12) (s221 .rroot.12)
  
  s222 .rroot.23
    : refl A (s022 .rroot.12) (s122 .rroot.12)
  
  s222 .rroot.23
    : refl A (s220 .rroot.12) (s221 .rroot.12)
  
  s222 .rroot.23
    : refl A (s202 .rroot.12) (s212 .rroot.12)
  

  $ narya -v sqrt.ny
   ￫ info[I0001]
   ￮ axiom A assumed
  
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
  

  $ narya -v 2dsqrt.ny
   ￫ info[I0001]
   ￮ axiom A assumed
  
   ￫ info[I0000]
   ￮ constant ID2 defined
  
   ￫ info[I0000]
   ￮ constant √√ID2A defined
  
   ￫ info[I0000]
   ￮ constant t defined
  
   ￫ info[I0001]
   ￮ axiom a00 assumed
  
   ￫ info[I0001]
   ￮ axiom a01 assumed
  
   ￫ info[I0001]
   ￮ axiom a02 assumed
  
   ￫ info[I0001]
   ￮ axiom a10 assumed
  
   ￫ info[I0001]
   ￮ axiom a11 assumed
  
   ￫ info[I0001]
   ￮ axiom a12 assumed
  
   ￫ info[I0001]
   ￮ axiom a20 assumed
  
   ￫ info[I0001]
   ￮ axiom a21 assumed
  
   ￫ info[I0001]
   ￮ axiom a22 assumed
  
   ￫ info[I0000]
   ￮ constant ta defined
  
  a00
    : A
  
  a00
    : A
  
  a01
    : A
  
  a10
    : A
  
  a02
    : refl A a00 a01
  
  a20
    : refl A a00 a10
  
  a22
    : A⁽ᵉᵉ⁾ a00 a01 a02 a10 a11 a12 a20 a21
  
  sym a22
    : A⁽ᵉᵉ⁾ a00 a10 a20 a01 a11 a21 a02 a12
  

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
  
