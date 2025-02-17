axiom A:Type

def ID (X : Type) : Type ≔ sig (
  x0 : X,
  x1 : X,
  x2 : Id X x0 x1,
)

def √IDA : Type ≔ codata [
  | x .root.e : ID A
]

def η (a:A) : √IDA ≔ [
  .root.e ↦ (a.0, a.1, a.2)
]

axiom a0:A
axiom a1:A
axiom a2:Id A a0 a1

echo refl η a0 a1 a2 .root.1 .x0
echo refl η a0 a1 a2 .root.1 .x1
echo refl η a0 a1 a2 .root.1 .x2

axiom s0 : √IDA
axiom s1 : √IDA
axiom s2 : Id √IDA s0 s1
echo s2 .root.1

def ⊥ : Type ≔ data [ ]
axiom admit : ⊥


def s2' : Id √IDA s0 s1 ≔ [
| .root.1 ↦ ?
| .root.e ↦ ?
]

axiom s00 : √IDA
axiom s01 : √IDA
axiom s02 : Id √IDA s00 s01
axiom s10 : √IDA
axiom s11 : √IDA
axiom s12 : Id √IDA s10 s11
axiom s20 : Id √IDA s00 s10
axiom s21 : Id √IDA s01 s11

axiom s22 : Id (Id √IDA) s00 s01 s02 s10 s11 s12 s20 s21
echo s22 .root.1
echo s22 .root.2


def s22' : Id (Id √IDA) s00 s01 s02 s10 s11 s12 s20 s21 ≔ [
| .root.1 ↦ ?
| .root.2 ↦ ?
| .root.e ↦ ?
]
