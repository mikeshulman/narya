axiom A : Type

def √A : Type ≔ codata [
  | x .root.e : A
]

axiom s0 : √A
axiom s1 : √A
axiom s2 : Id √A s0 s1
echo s2 .root.1

axiom s00 : √A
axiom s01 : √A
axiom s10 : √A
axiom s11 : √A
axiom s02 : Id √A s00 s01
axiom s12 : Id √A s10 s11
axiom s20 : Id √A s00 s10
axiom s21 : Id √A s01 s11
axiom s22 : √A⁽ᵉᵉ⁾ s00 s01 s02 s10 s11 s12 s20 s21
echo s22 .root.1
echo s22 .root.2
