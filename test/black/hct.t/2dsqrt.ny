axiom A:Type

def ID2 (X : Type) : Type ≔ sig (
  x00 : X,
  x01 : X,
  x02 : Id X x00 x01,
  x10 : X,
  x11 : X,
  x12 : Id X x10 x11,
  x20 : Id X x00 x10,
  x21 : Id X x01 x11,
  x22 : X⁽ᵉᵉ⁾ x00 x01 x02 x10 x11 x12 x20 x21,
)

def √√ID2A : Type ≔ codata [
  | x .root.ee : ID2 A
]

def t (a:A) : √√ID2A ≔ [
  .root.ee ↦ (a.00, a.01, a.02, a.10, a.11, a.12, a.20, a.21, a.22)
]

axiom a00:A
axiom a01:A
axiom a02:Id A a00 a01
axiom a10:A
axiom a11:A
axiom a12:Id A a10 a11
axiom a20:Id A a00 a10
axiom a21:Id A a01 a11
axiom a22: A⁽ᵉᵉ⁾ a00 a01 a02 a10 a11 a12 a20 a21

def ta ≔ t⁽ᵉᵉ⁾ a00 a01 a02 a10 a11 a12 a20 a21 a22

echo sym ta

echo ta .root.12 .x00
echo ta .root.21 .x00


{` These are the same... `}
echo ta .root.21
echo (sym ta) .root.12

{` But their .x01 fields are different! (The second one is right.) `}
echo ta .root.21 .x01
echo (sym ta) .root.12 .x01


echo ta .root.12 .x02
echo ta .root.21 .x02
echo ta .root.12 .x22
echo (sym ta) .root.21 .x22
