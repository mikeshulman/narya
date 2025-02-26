axiom A:Type
axiom B:Type
axiom f:A→B

axiom a0:A
axiom a1:A
axiom a2:Id A a0 a1

echo refl f a0 a1 a2

option function boundaries ≔ implicit

echo refl f a2

axiom a00 : A
axiom a01 : A
axiom a02 : Id A a00 a01
axiom a10 : A
axiom a11 : A
axiom a12 : Id A a10 a11
axiom a20 : Id A a00 a10
axiom a21 : Id A a01 a11
axiom a22 : Id (Id A) a00 a01 a02 a10 a11 a12 a20 a21

echo refl (refl f) a22

option function boundaries ≔ explicit

echo refl (refl f) a00 a01 a02 a10 a11 a12 a20 a21 a22

section test ≔

  option function boundaries ≔ implicit

  echo refl (refl f) a22

end

echo refl (refl f) a00 a01 a02 a10 a11 a12 a20 a21 a22

axiom g : (x0:A) (x1:A) (x2:Id A x0 x1) → B

echo refl g a00 a01 a02 a10 a11 a12 a20 a21 a22

option function boundaries ≔ implicit

echo refl g a02 a12 a22
