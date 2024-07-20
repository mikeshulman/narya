axiom A:Type

def √√A : Type ≔ codata [
| x .rroot.ee : A
]

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

echo s222 .rroot.12
echo s222 .rroot.13
echo s222 .rroot.23
echo s222 .rroot.21
echo s222 .rroot.32
echo s222 .rroot.31
