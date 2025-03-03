axiom A:Type
axiom B:Type
axiom a:A
axiom b:B

def A×B : Type ≔ sig ( fst:A, snd:B )

def p1 : A×B ≔ (a,b)
def p2 : A×B ≔ (a,b,)
def p3 : A×B ≔ (a|b)
def p4 : A×B ≔ (
| a
| b
)
def p5 : A×B ≔ (fst ≔ a, snd ≔ b)
def p6 : A×B ≔ (snd ≔ b, fst ≔ a)
def p7 : A×B ≔ (snd ≔ b | fst ≔ a)
def p8 : A×B ≔ (
| fst ≔ a
| snd ≔ b
)
def p9 : A×B ≔ (
| snd ≔ b
| fst ≔ a
)

def A×B' : Type ≔ sig (
| fst : A
| snd : B
)

def p1' : A×B' ≔ (a , b)
