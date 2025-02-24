axiom A:Type

{` Bottom face `}
axiom a000 : A
axiom a001 : A
axiom a002 : Id A a000 a001
axiom a010 : A
axiom a011 : A
axiom a012 : Id A a010 a011
axiom a020 : Id A a000 a010
axiom a021 : Id A a001 a011
axiom a022 : Id (Id A) a000 a001 a002 a010 a011 a012 a020 a021

{` Top face `}
axiom a100 : A
axiom a101 : A
axiom a102 : Id A a100 a101
axiom a110 : A
axiom a111 : A
axiom a112 : Id A a110 a111
axiom a120 : Id A a100 a110
axiom a121 : Id A a101 a111
axiom a122 : Id (Id A) a100 a101 a102 a110 a111 a112 a120 a121

{` Front face `}
axiom a200 : Id A a000 a100
axiom a201 : Id A a001 a101
axiom a202 : Id (Id A) a000 a001 a002 a100 a101 a102 a200 a201

{` Back face `}
axiom a210 : Id A a010 a110
axiom a211 : Id A a011 a111
axiom a212 : Id (Id A) a010 a011 a012 a110 a111 a112 a210 a211

{` Left face `}
axiom a220 : Id (Id A) a000 a010 a020 a100 a110 a120 a200 a210

{` Right face `}
axiom a221 : Id (Id A) a001 a011 a021 a101 a111 a121 a201 a211

{` Center `}
axiom a222 : Id (Id (Id A))
  a000 a001 a002 a010 a011 a012 a020 a021 a022
  a100 a101 a102 a110 a111 a112 a120 a121 a122
  a200 a201 a202 a210 a211 a212 a220 a221

{` Nothing `}
echo a222
echo a222⁽¹²³⁾

{` One transposition `}
echo sym a222
echo a222⁽¹³²⁾

{` The other transposition `}
def sym2 (x00 x01 : A) (x02 : Id A x00 x01) (x10 x11 : A) (x12 : Id A x10 x11)
  (x20 : Id A x00 x10) (x21 : Id A x01 x11)
  (x22 : Id (Id A) x00 x01 x02 x10 x11 x12 x20 x21)
  : Id (Id A) x00 x10 x20 x01 x11 x21 x02 x12
  ≔ sym x22
echo refl sym2
  a000 a001 a002 a010 a011 a012 a020 a021 a022
  a100 a101 a102 a110 a111 a112 a120 a121 a122
  a200 a201 a202 a210 a211 a212 a220 a221 a222
echo a222⁽²¹³⁾

{` The two sides of the braid equation, in stages `}

{` apsym-sym `}
echo refl sym2
  a000 a010 a020 a001 a011 a021 a002 a012 (sym a022)
  a100 a110 a120 a101 a111 a121 a102 a112 (sym a122)
  a200 a210 a220 a201 a211 a221 a202 a212 (sym a222)
echo a222⁽³¹²⁾

{` sym-apsym-sym `}
echo sym (refl sym2
  a000 a010 a020 a001 a011 a021 a002 a012 (sym a022)
  a100 a110 a120 a101 a111 a121 a102 a112 (sym a122)
  a200 a210 a220 a201 a211 a221 a202 a212 (sym a222))
echo a222⁽³²¹⁾

{` sym-apsym `}
echo sym (refl sym2
  a000 a001 a002 a010 a011 a012 a020 a021 a022
  a100 a101 a102 a110 a111 a112 a120 a121 a122
  a200 a201 a202 a210 a211 a212 a220 a221 a222)
echo a222⁽²³¹⁾

{` apsym-sym-apsym `}
echo refl sym2
  a000 a100 a200 a001 a101 a201 a002 a102 (sym a202)
  a010 a110 a210 a011 a111 a211 a012 a112 (sym a212)
  a020 a120 (sym a220) a021 a121 (sym a221) a022 a122
  (sym (refl sym2
  a000 a001 a002 a010 a011 a012 a020 a021 a022
  a100 a101 a102 a110 a111 a112 a120 a121 a122
  a200 a201 a202 a210 a211 a212 a220 a221 a222))
echo a222⁽³²¹⁾

def braid :
  Id (A⁽ᵉᵉᵉ⁾ a000 a100 a200 a010 a110 a210 a020 a120 (sym a220) a001 a101 a201
      a011 a111 a211 a021 a121 (sym a221) a002 a102 (sym a202) a012 a112
      (sym a212) (sym a022) (sym a122))
  (sym (refl sym2
    a000 a010 a020 a001 a011 a021 a002 a012 (sym a022)
    a100 a110 a120 a101 a111 a121 a102 a112 (sym a122)
    a200 a210 a220 a201 a211 a221 a202 a212 (sym a222)))
  (refl sym2
    a000 a100 a200 a001 a101 a201 a002 a102 (sym a202)
    a010 a110 a210 a011 a111 a211 a012 a112 (sym a212)
    a020 a120 (sym a220) a021 a121 (sym a221) a022 a122
    (sym (refl sym2
      a000 a001 a002 a010 a011 a012 a020 a021 a022
      a100 a101 a102 a110 a111 a112 a120 a121 a122
      a200 a201 a202 a210 a211 a212 a220 a221 a222)))
  ≔ refl a222⁽³²¹⁾
