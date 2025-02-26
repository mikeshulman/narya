  $ narya -v -fake-interact=implicit-boundaries.ny
   ￫ info[I0001]
   ￮ axiom A assumed
  
   ￫ info[I0001]
   ￮ axiom B assumed
  
   ￫ info[I0001]
   ￮ axiom f assumed
  
   ￫ info[I0001]
   ￮ axiom a0 assumed
  
   ￫ info[I0001]
   ￮ axiom a1 assumed
  
   ￫ info[I0001]
   ￮ axiom a2 assumed
  
  refl f a0 a1 a2
    : refl B (f a0) (f a1)
  
   ￫ info[I0100]
   ￮ option set function boundaries to implicit
  
  refl f a2
    : refl B (f a0) (f a1)
  
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
  
  f⁽ᵉᵉ⁾ a22
    : B⁽ᵉᵉ⁾ (f a00) (f a01) (refl f a02) (f a10) (f a11) (refl f a12)
        (refl f a20) (refl f a21)
  
   ￫ info[I0100]
   ￮ option set function boundaries to explicit
  
  f⁽ᵉᵉ⁾ a00 a01 a02 a10 a11 a12 a20 a21 a22
    : B⁽ᵉᵉ⁾ (f a00) (f a01) (refl f a00 a01 a02) (f a10) (f a11)
        (refl f a10 a11 a12) (refl f a00 a10 a20) (refl f a01 a11 a21)
  
   ￫ info[I0007]
   ￮ section test opened
  
   ￫ info[I0100]
   ￮ option set function boundaries to implicit
  
  f⁽ᵉᵉ⁾ a22
    : B⁽ᵉᵉ⁾ (f a00) (f a01) (refl f a02) (f a10) (f a11) (refl f a12)
        (refl f a20) (refl f a21)
  
   ￫ info[I0008]
   ￮ section test closed
  
  f⁽ᵉᵉ⁾ a00 a01 a02 a10 a11 a12 a20 a21 a22
    : B⁽ᵉᵉ⁾ (f a00) (f a01) (refl f a00 a01 a02) (f a10) (f a11)
        (refl f a10 a11 a12) (refl f a00 a10 a20) (refl f a01 a11 a21)
  
   ￫ info[I0001]
   ￮ axiom g assumed
  
  refl g a00 a01 a02 a10 a11 a12 a20 a21 a22
    : refl B (g a00 a10 a20) (g a01 a11 a21)
  
   ￫ info[I0100]
   ￮ option set function boundaries to implicit
  
  refl g a02 a12 a22
    : refl B (g a00 a10 a20) (g a01 a11 a21)
  

  $ narya -v -show-function-boundaries -fake-interact=implicit-boundaries.ny
   ￫ info[I0001]
   ￮ axiom A assumed
  
   ￫ info[I0001]
   ￮ axiom B assumed
  
   ￫ info[I0001]
   ￮ axiom f assumed
  
   ￫ info[I0001]
   ￮ axiom a0 assumed
  
   ￫ info[I0001]
   ￮ axiom a1 assumed
  
   ￫ info[I0001]
   ￮ axiom a2 assumed
  
  refl f a0 a1 a2
    : refl B (f a0) (f a1)
  
   ￫ info[I0100]
   ￮ option set function boundaries to implicit
  
  refl f {a0} {a1} a2
    : refl B (f a0) (f a1)
  
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
  
  f⁽ᵉᵉ⁾ {a00} {a01} {a02} {a10} {a11} {a12} {a20} {a21} a22
    : B⁽ᵉᵉ⁾ (f a00) (f a01) (refl f {a00} {a01} a02) (f a10) (f a11)
        (refl f {a10} {a11} a12) (refl f {a00} {a10} a20)
        (refl f {a01} {a11} a21)
  
   ￫ info[I0100]
   ￮ option set function boundaries to explicit
  
  f⁽ᵉᵉ⁾ a00 a01 a02 a10 a11 a12 a20 a21 a22
    : B⁽ᵉᵉ⁾ (f a00) (f a01) (refl f a00 a01 a02) (f a10) (f a11)
        (refl f a10 a11 a12) (refl f a00 a10 a20) (refl f a01 a11 a21)
  
   ￫ info[I0007]
   ￮ section test opened
  
   ￫ info[I0100]
   ￮ option set function boundaries to implicit
  
  f⁽ᵉᵉ⁾ {a00} {a01} {a02} {a10} {a11} {a12} {a20} {a21} a22
    : B⁽ᵉᵉ⁾ (f a00) (f a01) (refl f {a00} {a01} a02) (f a10) (f a11)
        (refl f {a10} {a11} a12) (refl f {a00} {a10} a20)
        (refl f {a01} {a11} a21)
  
   ￫ info[I0008]
   ￮ section test closed
  
  f⁽ᵉᵉ⁾ a00 a01 a02 a10 a11 a12 a20 a21 a22
    : B⁽ᵉᵉ⁾ (f a00) (f a01) (refl f a00 a01 a02) (f a10) (f a11)
        (refl f a10 a11 a12) (refl f a00 a10 a20) (refl f a01 a11 a21)
  
   ￫ info[I0001]
   ￮ axiom g assumed
  
  refl g a00 a01 a02 a10 a11 a12 a20 a21 a22
    : refl B (g a00 a10 a20) (g a01 a11 a21)
  
   ￫ info[I0100]
   ￮ option set function boundaries to implicit
  
  refl g {a00} {a01} a02 {a10} {a11} a12 {a20} {a21} a22
    : refl B (g a00 a10 a20) (g a01 a11 a21)
  

  $ narya -v implicit-boundaries.ny
   ￫ info[I0001]
   ￮ axiom A assumed
  
   ￫ info[I0001]
   ￮ axiom B assumed
  
   ￫ info[I0001]
   ￮ axiom f assumed
  
   ￫ info[I0001]
   ￮ axiom a0 assumed
  
   ￫ info[I0001]
   ￮ axiom a1 assumed
  
   ￫ info[I0001]
   ￮ axiom a2 assumed
  
  refl f a0 a1 a2
    : refl B (f a0) (f a1)
  
   ￫ info[I0100]
   ￮ option set function boundaries to implicit
  
  refl f a2
    : refl B (f a0) (f a1)
  
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
  
  f⁽ᵉᵉ⁾ a22
    : B⁽ᵉᵉ⁾ (f a00) (f a01) (refl f a02) (f a10) (f a11) (refl f a12)
        (refl f a20) (refl f a21)
  
   ￫ info[I0100]
   ￮ option set function boundaries to explicit
  
  f⁽ᵉᵉ⁾ a00 a01 a02 a10 a11 a12 a20 a21 a22
    : B⁽ᵉᵉ⁾ (f a00) (f a01) (refl f a00 a01 a02) (f a10) (f a11)
        (refl f a10 a11 a12) (refl f a00 a10 a20) (refl f a01 a11 a21)
  
   ￫ info[I0007]
   ￮ section test opened
  
   ￫ info[I0100]
   ￮ option set function boundaries to implicit
  
  f⁽ᵉᵉ⁾ a22
    : B⁽ᵉᵉ⁾ (f a00) (f a01) (refl f a02) (f a10) (f a11) (refl f a12)
        (refl f a20) (refl f a21)
  
   ￫ info[I0008]
   ￮ section test closed
  
  f⁽ᵉᵉ⁾ a00 a01 a02 a10 a11 a12 a20 a21 a22
    : B⁽ᵉᵉ⁾ (f a00) (f a01) (refl f a00 a01 a02) (f a10) (f a11)
        (refl f a10 a11 a12) (refl f a00 a10 a20) (refl f a01 a11 a21)
  
   ￫ info[I0001]
   ￮ axiom g assumed
  
  refl g a00 a01 a02 a10 a11 a12 a20 a21 a22
    : refl B (g a00 a10 a20) (g a01 a11 a21)
  
   ￫ info[I0100]
   ￮ option set function boundaries to implicit
  
  refl g a02 a12 a22
    : refl B (g a00 a10 a20) (g a01 a11 a21)
  

  $ narya -v -show-function-boundaries implicit-boundaries.ny
   ￫ info[I0001]
   ￮ axiom A assumed
  
   ￫ info[I0001]
   ￮ axiom B assumed
  
   ￫ info[I0001]
   ￮ axiom f assumed
  
   ￫ info[I0001]
   ￮ axiom a0 assumed
  
   ￫ info[I0001]
   ￮ axiom a1 assumed
  
   ￫ info[I0001]
   ￮ axiom a2 assumed
  
  refl f a0 a1 a2
    : refl B (f a0) (f a1)
  
   ￫ info[I0100]
   ￮ option set function boundaries to implicit
  
  refl f {a0} {a1} a2
    : refl B (f a0) (f a1)
  
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
  
  f⁽ᵉᵉ⁾ {a00} {a01} {a02} {a10} {a11} {a12} {a20} {a21} a22
    : B⁽ᵉᵉ⁾ (f a00) (f a01) (refl f {a00} {a01} a02) (f a10) (f a11)
        (refl f {a10} {a11} a12) (refl f {a00} {a10} a20)
        (refl f {a01} {a11} a21)
  
   ￫ info[I0100]
   ￮ option set function boundaries to explicit
  
  f⁽ᵉᵉ⁾ a00 a01 a02 a10 a11 a12 a20 a21 a22
    : B⁽ᵉᵉ⁾ (f a00) (f a01) (refl f a00 a01 a02) (f a10) (f a11)
        (refl f a10 a11 a12) (refl f a00 a10 a20) (refl f a01 a11 a21)
  
   ￫ info[I0007]
   ￮ section test opened
  
   ￫ info[I0100]
   ￮ option set function boundaries to implicit
  
  f⁽ᵉᵉ⁾ {a00} {a01} {a02} {a10} {a11} {a12} {a20} {a21} a22
    : B⁽ᵉᵉ⁾ (f a00) (f a01) (refl f {a00} {a01} a02) (f a10) (f a11)
        (refl f {a10} {a11} a12) (refl f {a00} {a10} a20)
        (refl f {a01} {a11} a21)
  
   ￫ info[I0008]
   ￮ section test closed
  
  f⁽ᵉᵉ⁾ a00 a01 a02 a10 a11 a12 a20 a21 a22
    : B⁽ᵉᵉ⁾ (f a00) (f a01) (refl f a00 a01 a02) (f a10) (f a11)
        (refl f a10 a11 a12) (refl f a00 a10 a20) (refl f a01 a11 a21)
  
   ￫ info[I0001]
   ￮ axiom g assumed
  
  refl g a00 a01 a02 a10 a11 a12 a20 a21 a22
    : refl B (g a00 a10 a20) (g a01 a11 a21)
  
   ￫ info[I0100]
   ￮ option set function boundaries to implicit
  
  refl g {a00} {a01} a02 {a10} {a11} a12 {a20} {a21} a22
    : refl B (g a00 a10 a20) (g a01 a11 a21)
  
