axiom A:Type
axiom B:Type
axiom f:A→B

axiom a0:A
axiom a1:A
axiom a2:Id A a0 a1

echo refl f a0 a1 a2

{` When function boundaries are implicit, we don't give a0 and a1. `}

option function boundaries ≔ implicit

echo refl f a2

{` Similarly for cubes `}

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

{` Similarly for types *of* cubes `}

option type boundaries ≔ implicit

echo Id (Id A) a02 a12 a20 a21

echo Id (Id A) {a00} {a01} a02 a12 a20 a21

echo Id (Id A) {a00} {a01} a02 {a10} {a11} a12 a20 a21

echo Id (Id A) a02 {a10} {a11} a12 a20 a21

{` Mixing and matching function and type options `}

option function boundaries ≔ explicit

echo refl (refl f) a00 a01 a02 a10 a11 a12 a20 a21 a22

option type boundaries ≔ explicit

echo refl (refl f) a00 a01 a02 a10 a11 a12 a20 a21 a22

{` These options don't survive the ends of sections `}

section test ≔

  option function boundaries ≔ implicit

  echo refl (refl f) a22

end

echo refl (refl f) a00 a01 a02 a10 a11 a12 a20 a21 a22

{` The dimension of the argument can be greater than the dimension of the application (this is a 1-dimensional application). `}

axiom g : (x0:A) (x1:A) (x2:Id A x0 x1) → B

echo refl g a00 a01 a02 a10 a11 a12 a20 a21 a22

option function boundaries ≔ implicit

echo refl g a02 a12 a22

{` Even when printing implicit arguments is off, they are included if the corresponding primary argument doesn't synthesize. `}

axiom C : Type
def A×B : Type ≔ sig (fst : A, snd : B)
axiom h : A×B → C

axiom b0:B
axiom b1:B
axiom b2:Id B b0 b1

echo refl h {(a0,b0)} {(a1,b1)} (a2,b2)

axiom b00 : B
axiom b01 : B
axiom b02 : Id B b00 b01
axiom b10 : B
axiom b11 : B
axiom b12 : Id B b10 b11
axiom b20 : Id B b00 b10
axiom b21 : Id B b01 b11
axiom b22 : Id (Id B) b00 b01 b02 b10 b11 b12 b20 b21

echo refl (refl h) {(a00,b00)} {(a01,b01)} {(a02,b02)} {(a10,b10)} {(a11,b11)} {(a12,b12)} {(a20,b20)} {(a21,b21)} (a22,b22)

option type boundaries ≔ implicit

echo refl (refl h) {(a00,b00)} {(a01,b01)} {(a02,b02)} {(a10,b10)} {(a11,b11)} {(a12,b12)} {(a20,b20)} {(a21,b21)} (a22,b22)

axiom ab10 : A×B
axiom ab11 : A×B
axiom ab12 : Id A×B ab10 ab11
axiom ab20 : Id A×B (a00,b00) ab10
axiom ab21 : Id A×B (a01,b01) ab11
axiom ab22 : Id (Id A×B) {(a00,b00)} {(a01,b01)} (a02,b02) {ab10} {ab11} ab12 ab20 ab21

echo ab22

echo refl (refl h) {(a00,b00)} {(a01,b01)} {(a02,b02)} {ab10} {ab11} {ab12} {ab20} {ab21} ab22
