axiom A : Type
def twos : Type := data [
| foo. (_:A) (_:A)
]
notation 1 twos.foo : x "+" y := foo. x y
def threes : Type := data [
| foo. (_:A) (_:A) (_:A)
]
notation 1 threes.foo : x "*" y "*" z := foo. x y z
axiom a:A
def a2 : twos := a + a
echo a2
def a3 : threes := a * a * a
echo a3
