` (Binary) semi-cubical types
def SCT : Type ≔ codata [
| X .z : Type
| X .s : SCT⁽ᵖ⁾ X X
]

def 0s (X : SCT) : Type ≔ X .z

def 1s (X : SCT) (x0 x1 : 0s X) : Type ≔ X .s .z x0 x1

def 2s (X : SCT) (x00 x01 : 0s X) (x02 : 1s X x00 x01) (x10 x11 : 0s X) (x12 : 1s X x10 x11) (x20 : 1s X x00 x10) (x21 : 1s X x01 x11) : Type
  ≔ X .s .s .z x00 x01 x02 x10 x11 x12 x20 x21
