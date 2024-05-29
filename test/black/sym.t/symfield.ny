axiom B : Type
def A : Type ≔ sig ( unwrap : B )
axiom a00 : A
axiom a01 : A
axiom a02 : Id A a00 a01
axiom a10 : A
axiom a11 : A
axiom a12 : Id A a10 a11
axiom a20 : Id A a00 a10
axiom a21 : Id A a01 a11
axiom a22 : refl (Id A) a00 a01 a02 a10 a11 a12 a20 a21

echo (sym a22) .unwrap
echo sym (a22 .unwrap)

def Jd (X:Type) (x:X) : X → Type ≔ data [ rfl. : Jd X x x ]

def test
  : Jd (refl (Id B) (a00 .unwrap) (a10 .unwrap) (a20 .unwrap) (a01 .unwrap) (a11 .unwrap) (a21 .unwrap) (a02 .unwrap) (a12 .unwrap))
       ((sym a22) .unwrap) (sym (a22 .unwrap))
  ≔ rfl.
