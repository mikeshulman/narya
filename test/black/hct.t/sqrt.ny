{` The "amazing right adjoint" can only be defined for closed types. `}
axiom A : Type

def √A : Type ≔ codata [
  | x .root.e : A
]

{` If we have an equality in √A, we can project out an element of A.  This is the counit of the adjunction Id ⊣ √. `}
axiom s0 : √A
axiom s1 : √A
axiom s2 : Id √A s0 s1
echo s2 .root.1

{` At higher dimensions, if we have a square in √A, we can project out *two* elements of A, according to the two directions of the square. `}
axiom s00 : √A
axiom s01 : √A
axiom s10 : √A
axiom s11 : √A
axiom s02 : Id √A s00 s01
axiom s12 : Id √A s10 s11
axiom s20 : Id √A s00 s10
axiom s21 : Id √A s01 s11
axiom s22 : √A⁽ᵉᵉ⁾ s00 s01 s02 s10 s11 s12 s20 s21
{` The two are related by symmetrizing the square. `}
echo s22 .root.1
echo s22 .root.2

{` We can also take the fields of refl s2. `}
echo refl s2 .root.1
echo refl s2 .root.2
echo refl (s2 .root.1)

{` Since sym fixes refl-refl, the two fields of refl-refl s0 are the same. `}
echo refl (refl s0) .root.1
echo refl (refl s0) .root.2


{` To define an element of √, we specify the value for the higher field in a degenerated context. `}
axiom B : Type
axiom f (y0 y1 : B) (y2 : Id B y0 y1) : A

def √f (b : B) : √A ≔ [
| .root.e ↦ f b.0 b.1 b.2
]

axiom b0 : B
axiom b1 : B
axiom b2 : Id B b0 b1

{` When we have this element sufficiently degenerated, we can project out its field(s) and get the value we supplied, applied to the correct arguments. `}
echo refl √f b0 b1 b2 .root.1

{` And similarly at the next dimension. `}
axiom t00 : B
axiom t01 : B
axiom t10 : B
axiom t11 : B
axiom t02 : Id B t00 t01
axiom t12 : Id B t10 t11
axiom t20 : Id B t00 t10
axiom t21 : Id B t01 t11
axiom t22 : Id (Id B) t00 t01 t02 t10 t11 t12 t20 t21

echo √f⁽ᵉᵉ⁾  t00 t01 t02 t10 t11 t12 t20 t21 t22 .root.2
echo √f⁽ᵉᵉ⁾  t00 t01 t02 t10 t11 t12 t20 t21 t22 .root.1

{` We can also see that sym fixes refl-refl on a non-neutral element. `}
axiom a : A
def √a : √A ≔ [
| .root.e ↦ a
]
echo refl √a .root.1
echo refl (refl √a) .root.1
echo refl (refl √a) .root.2

{` We can also define elements of degenerate versions of √A, as higher coinductive types in their own right.  In this case we have to give a value for the "actual" field that has appeared, as well as the higher field that is now further degenerated. `}

def s2' : Id √A (√f b0) (√f b1) ≔ [
| .root.e ↦ refl f b0 b1 b2 b0 b1 b2 (refl b0) (refl b1) (sym (refl b2))
| .root.1 ↦ a
]

{` Only the version that's already fully instantiated can be directly projected out. `}
echo s2' .root.1

{` The other one only comes into play when we degenerate. `}
echo refl s2' .root.2
echo refl s2' .root.1

{` One way to define the unit of the adjunction Id ⊣ √ is to wrap up Id and its endpoints in a sig. `}
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

{` The pieces of this are what we put in.  (A triangle identity) `}
echo refl η a0 a1 a2 .root.1 .x0
echo refl η a0 a1 a2 .root.1 .x1
echo refl η a0 a1 a2 .root.1 .x2

{` Higher-dimensional versions `}
axiom u0 : √IDA
axiom u1 : √IDA
axiom u2 : Id √IDA u0 u1
echo u2 .root.1

def u2' : Id √IDA u0 u1 ≔ [
| .root.1 ↦ ?
| .root.e ↦ ?
]

axiom u00 : √IDA
axiom u01 : √IDA
axiom u02 : Id √IDA u00 u01
axiom u10 : √IDA
axiom u11 : √IDA
axiom u12 : Id √IDA u10 u11
axiom u20 : Id √IDA u00 u10
axiom u21 : Id √IDA u01 u11

axiom u22 : Id (Id √IDA) u00 u01 u02 u10 u11 u12 u20 u21
echo u22 .root.1
echo u22 .root.2

def u22' : Id (Id √IDA) u00 u01 u02 u10 u11 u12 u20 u21 ≔ [
| .root.1 ↦ ?
| .root.2 ↦ ?
| .root.e ↦ ?
]
