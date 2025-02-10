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
