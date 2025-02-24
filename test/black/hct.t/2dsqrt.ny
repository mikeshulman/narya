{` The "double square root", a higher coinductive type with a 2-dimensional field. `}
axiom A:Type

def √√A : Type ≔ codata [
| x .rroot.ee : A
]

{` To project this out, we need a doubly degenerated instance.  With a triply degenerated instance, we can project out all six fields. `}
axiom s000 : √√A
axiom s001 : √√A
axiom s002 : Id √√A s000 s001
axiom s010 : √√A
axiom s011 : √√A
axiom s012 : Id √√A s010 s011
axiom s020 : Id √√A s000 s010
axiom s021 : Id √√A s001 s011
axiom s022 : √√A⁽ᵉᵉ⁾ s000 s001 s002 s010 s011 s012 s020 s021
axiom s100 : √√A
axiom s101 : √√A
axiom s102 : Id √√A s100 s101
axiom s110 : √√A
axiom s111 : √√A
axiom s112 : Id √√A s110 s111
axiom s120 : Id √√A s100 s110
axiom s121 : Id √√A s101 s111
axiom s122 : √√A⁽ᵉᵉ⁾ s100 s101 s102 s110 s111 s112 s120 s121
axiom s200 : Id √√A s000 s100
axiom s201 : Id √√A s001 s101
axiom s202 : √√A⁽ᵉᵉ⁾ s000 s001 s002 s100 s101 s102 s200 s201
axiom s210 : Id √√A s010 s110
axiom s211 : Id √√A s011 s111
axiom s212 : √√A⁽ᵉᵉ⁾ s010 s011 s012 s110 s111 s112 s210 s211
axiom s220 : √√A⁽ᵉᵉ⁾ s000 s010 s020 s100 s110 s120 s200 s210
axiom s221 : √√A⁽ᵉᵉ⁾ s001 s011 s021 s101 s111 s121 s201 s211

axiom s222 : √√A⁽ᵉᵉᵉ⁾
  s000 s001 s002 s010 s011 s012 s020 s021 s022
  s100 s101 s102 s110 s111 s112 s120 s121 s122
  s200 s201 s202 s210 s211 s212 s220 s221

{` Here are the six fields, with their six different types.  Note that they all compute to .rroot.12 of a symmetrized s222. `}
echo s222 .rroot.12
echo s222 .rroot.13
echo s222 .rroot.23
echo s222 .rroot.21
echo s222 .rroot.32
echo s222 .rroot.31

{` To compute with concrete instances, let's consider instead the double square root of a type of squares, to make it easier to define elements. `}
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
  | x .rroot.ee : ID2 A
]

def t (a:A) : √√ID2A ≔ [
  .rroot.ee ↦ (a.00, a.01, a.02, a.10, a.11, a.12, a.20, a.21, a.22)
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

{` ta has two projectable fields, .rroot.12 and .rroot.21. `}
echo ta .rroot.12
echo ta .rroot.21

{` They are transposed `}
echo ta .rroot.12 .x00
echo ta .rroot.21 .x00

echo ta .rroot.12 .x01
echo ta .rroot.21 .x01

echo ta .rroot.12 .x02
echo ta .rroot.21 .x02

echo ta .rroot.12 .x10
echo ta .rroot.21 .x10

echo ta .rroot.12 .x11
echo ta .rroot.21 .x11

echo ta .rroot.12 .x12
echo ta .rroot.21 .x12

echo ta .rroot.12 .x20
echo ta .rroot.21 .x20

echo ta .rroot.12 .x21
echo ta .rroot.21 .x21

echo ta .rroot.12 .x22
echo ta .rroot.21 .x22

{` They are related by symmetry `}
echo ta .rroot.21
echo (sym ta) .rroot.12

{` ...and so are their fields. `}
echo ta .rroot.21 .x01
echo (sym ta) .rroot.12 .x01

echo ta .rroot.21 .x02
echo (sym ta) .rroot.12 .x02

