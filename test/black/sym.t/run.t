  $ narya -v sym.ny
   ￫ info[I0001]
   ￮ axiom A assumed
  
   ￫ info[I0001]
   ￮ axiom a00 assumed
  
   ￫ info[I0001]
   ￮ axiom a01 assumed
  
   ￫ info[I0001]
   ￮ axiom a02 assumed
  
   ￫ info[I0001]
   ￮ axiom a10 assumed
  
   ￫ info[I0001]
   ￮ axiom a11 assumed
  
   ￫ info[I0001]
   ￮ axiom a12 assumed
  
   ￫ info[I0001]
   ￮ axiom a20 assumed
  
   ￫ info[I0001]
   ￮ axiom a21 assumed
  
   ￫ info[I0001]
   ￮ axiom a22 assumed
  
  sym a22
    : A⁽ᵉᵉ⁾ a00 a10 a20 a01 a11 a21 a02 a12
  
  a22
    : A⁽ᵉᵉ⁾ a00 a01 a02 a10 a11 a12 a20 a21
  
   ￫ info[I0000]
   ￮ constant sym_involution defined
  
   ￫ info[I0001]
   ￮ axiom B assumed
  
   ￫ info[I0001]
   ￮ axiom f assumed
  
  f⁽ᵉᵉ⁾ a00 a10 a20 a01 a11 a21 a02 a12 (sym a22)
    : B⁽ᵉᵉ⁾ (f a00) (f a10) (refl f a00 a10 a20) (f a01) (f a11)
        (refl f a01 a11 a21) (refl f a00 a01 a02) (refl f a10 a11 a12)
  
  f⁽ᵉᵉ⁾ a00 a10 a20 a01 a11 a21 a02 a12 (sym a22)
    : B⁽ᵉᵉ⁾ (f a00) (f a10) (refl f a00 a10 a20) (f a01) (f a11)
        (refl f a01 a11 a21) (refl f a00 a01 a02) (refl f a10 a11 a12)
  
   ￫ info[I0000]
   ￮ constant ap_sym defined
  

  $ narya sym.ny -e "echo sym a00"
  sym a22
    : A⁽ᵉᵉ⁾ a00 a10 a20 a01 a11 a21 a02 a12
  
  a22
    : A⁽ᵉᵉ⁾ a00 a01 a02 a10 a11 a12 a20 a21
  
  f⁽ᵉᵉ⁾ a00 a10 a20 a01 a11 a21 a02 a12 (sym a22)
    : B⁽ᵉᵉ⁾ (f a00) (f a10) (refl f a00 a10 a20) (f a01) (f a11)
        (refl f a01 a11 a21) (refl f a00 a01 a02) (refl f a10 a11 a12)
  
  f⁽ᵉᵉ⁾ a00 a10 a20 a01 a11 a21 a02 a12 (sym a22)
    : B⁽ᵉᵉ⁾ (f a00) (f a10) (refl f a00 a10 a20) (f a01) (f a11)
        (refl f a01 a11 a21) (refl f a00 a01 a02) (refl f a10 a11 a12)
  
   ￫ error[E0601]
   ￭ command-line exec string
   1 | echo sym a00
     ^ argument of degeneracy 'sym' must have dimension at least ee
  
  [1]

  $ narya sym.ny -e "echo sym a02"
  sym a22
    : A⁽ᵉᵉ⁾ a00 a10 a20 a01 a11 a21 a02 a12
  
  a22
    : A⁽ᵉᵉ⁾ a00 a01 a02 a10 a11 a12 a20 a21
  
  f⁽ᵉᵉ⁾ a00 a10 a20 a01 a11 a21 a02 a12 (sym a22)
    : B⁽ᵉᵉ⁾ (f a00) (f a10) (refl f a00 a10 a20) (f a01) (f a11)
        (refl f a01 a11 a21) (refl f a00 a01 a02) (refl f a10 a11 a12)
  
  f⁽ᵉᵉ⁾ a00 a10 a20 a01 a11 a21 a02 a12 (sym a22)
    : B⁽ᵉᵉ⁾ (f a00) (f a10) (refl f a00 a10 a20) (f a01) (f a11)
        (refl f a01 a11 a21) (refl f a00 a01 a02) (refl f a10 a11 a12)
  
   ￫ error[E0601]
   ￭ command-line exec string
   1 | echo sym a02
     ^ argument of degeneracy 'sym' must have dimension at least ee
  
  [1]

  $ narya -v symsym.ny
   ￫ info[I0001]
   ￮ axiom A assumed
  
   ￫ info[I0001]
   ￮ axiom a000 assumed
  
   ￫ info[I0001]
   ￮ axiom a001 assumed
  
   ￫ info[I0001]
   ￮ axiom a002 assumed
  
   ￫ info[I0001]
   ￮ axiom a010 assumed
  
   ￫ info[I0001]
   ￮ axiom a011 assumed
  
   ￫ info[I0001]
   ￮ axiom a012 assumed
  
   ￫ info[I0001]
   ￮ axiom a020 assumed
  
   ￫ info[I0001]
   ￮ axiom a021 assumed
  
   ￫ info[I0001]
   ￮ axiom a022 assumed
  
   ￫ info[I0001]
   ￮ axiom a100 assumed
  
   ￫ info[I0001]
   ￮ axiom a101 assumed
  
   ￫ info[I0001]
   ￮ axiom a102 assumed
  
   ￫ info[I0001]
   ￮ axiom a110 assumed
  
   ￫ info[I0001]
   ￮ axiom a111 assumed
  
   ￫ info[I0001]
   ￮ axiom a112 assumed
  
   ￫ info[I0001]
   ￮ axiom a120 assumed
  
   ￫ info[I0001]
   ￮ axiom a121 assumed
  
   ￫ info[I0001]
   ￮ axiom a122 assumed
  
   ￫ info[I0001]
   ￮ axiom a200 assumed
  
   ￫ info[I0001]
   ￮ axiom a201 assumed
  
   ￫ info[I0001]
   ￮ axiom a202 assumed
  
   ￫ info[I0001]
   ￮ axiom a210 assumed
  
   ￫ info[I0001]
   ￮ axiom a211 assumed
  
   ￫ info[I0001]
   ￮ axiom a212 assumed
  
   ￫ info[I0001]
   ￮ axiom a220 assumed
  
   ￫ info[I0001]
   ￮ axiom a221 assumed
  
   ￫ info[I0001]
   ￮ axiom a222 assumed
  
  a222
    : A⁽ᵉᵉᵉ⁾ a000 a001 a002 a010 a011 a012 a020 a021 a022 a100 a101 a102 a110
        a111 a112 a120 a121 a122 a200 a201 a202 a210 a211 a212 a220 a221
  
  a222
    : A⁽ᵉᵉᵉ⁾ a000 a001 a002 a010 a011 a012 a020 a021 a022 a100 a101 a102 a110
        a111 a112 a120 a121 a122 a200 a201 a202 a210 a211 a212 a220 a221
  
  sym a222
    : A⁽ᵉᵉᵉ⁾ a000 a010 a020 a001 a011 a021 a002 a012 (sym a022) a100 a110 a120
        a101 a111 a121 a102 a112 (sym a122) a200 a210 a220 a201 a211 a221 a202
        a212
  
  a222⁽¹³²⁾
    : A⁽ᵉᵉᵉ⁾ a000 a010 a020 a001 a011 a021 a002 a012 (sym a022) a100 a110 a120
        a101 a111 a121 a102 a112 (sym a122) a200 a210 a220 a201 a211 a221 a202
        a212
  
   ￫ info[I0000]
   ￮ constant sym2 defined
  
  a222⁽²¹³⁾
    : A⁽ᵉᵉᵉ⁾ a000 a001 a002 a100 a101 a102 a200 a201 a202 a010 a011 a012 a110
        a111 a112 a210 a211 a212 a020 a021 a022 a120 a121 a122 (sym a220)
        (sym a221)
  
  a222⁽²¹³⁾
    : A⁽ᵉᵉᵉ⁾ a000 a001 a002 a100 a101 a102 a200 a201 a202 a010 a011 a012 a110
        a111 a112 a210 a211 a212 a020 a021 a022 a120 a121 a122 (sym a220)
        (sym a221)
  
  a222⁽³¹²⁾
    : A⁽ᵉᵉᵉ⁾ a000 a010 a020 a100 a110 a120 a200 a210 a220 a001 a011 a021 a101
        a111 a121 a201 a211 a221 a002 a012 (sym a022) a102 a112 (sym a122)
        (sym a202) (sym a212)
  
  a222⁽³¹²⁾
    : A⁽ᵉᵉᵉ⁾ a000 a010 a020 a100 a110 a120 a200 a210 a220 a001 a011 a021 a101
        a111 a121 a201 a211 a221 a002 a012 (sym a022) a102 a112 (sym a122)
        (sym a202) (sym a212)
  
  a222⁽³²¹⁾
    : A⁽ᵉᵉᵉ⁾ a000 a100 a200 a010 a110 a210 a020 a120 (sym a220) a001 a101 a201
        a011 a111 a211 a021 a121 (sym a221) a002 a102 (sym a202) a012 a112
        (sym a212) (sym a022) (sym a122)
  
  a222⁽³²¹⁾
    : A⁽ᵉᵉᵉ⁾ a000 a100 a200 a010 a110 a210 a020 a120 (sym a220) a001 a101 a201
        a011 a111 a211 a021 a121 (sym a221) a002 a102 (sym a202) a012 a112
        (sym a212) (sym a022) (sym a122)
  
  a222⁽²³¹⁾
    : A⁽ᵉᵉᵉ⁾ a000 a100 a200 a001 a101 a201 a002 a102 (sym a202) a010 a110 a210
        a011 a111 a211 a012 a112 (sym a212) a020 a120 (sym a220) a021 a121
        (sym a221) a022 a122
  
  a222⁽²³¹⁾
    : A⁽ᵉᵉᵉ⁾ a000 a100 a200 a001 a101 a201 a002 a102 (sym a202) a010 a110 a210
        a011 a111 a211 a012 a112 (sym a212) a020 a120 (sym a220) a021 a121
        (sym a221) a022 a122
  
  a222⁽³²¹⁾
    : A⁽ᵉᵉᵉ⁾ a000 a100 a200 a010 a110 a210 a020 a120 (sym a220) a001 a101 a201
        a011 a111 a211 a021 a121 (sym a221) a002 a102 (sym a202) a012 a112
        (sym a212) (sym a022) (sym a122)
  
  a222⁽³²¹⁾
    : A⁽ᵉᵉᵉ⁾ a000 a100 a200 a010 a110 a210 a020 a120 (sym a220) a001 a101 a201
        a011 a111 a211 a021 a121 (sym a221) a002 a102 (sym a202) a012 a112
        (sym a212) (sym a022) (sym a122)
  
   ￫ info[I0000]
   ￮ constant braid defined
  
   ￫ info[I0000]
   ￮ constant braid2 defined
  

  $ narya -v checksym.ny
   ￫ info[I0001]
   ￮ axiom A assumed
  
   ￫ info[I0001]
   ￮ axiom a00 assumed
  
   ￫ info[I0001]
   ￮ axiom a01 assumed
  
   ￫ info[I0001]
   ￮ axiom a02 assumed
  
   ￫ info[I0001]
   ￮ axiom a10 assumed
  
   ￫ info[I0001]
   ￮ axiom a11 assumed
  
   ￫ info[I0001]
   ￮ axiom a12 assumed
  
   ￫ info[I0001]
   ￮ axiom a20 assumed
  
   ￫ info[I0001]
   ￮ axiom a21 assumed
  
   ￫ info[I0001]
   ￮ axiom a22 assumed
  
   ￫ info[I0001]
   ￮ axiom B assumed
  
   ￫ info[I0001]
   ￮ axiom b00 assumed
  
   ￫ info[I0001]
   ￮ axiom b01 assumed
  
   ￫ info[I0001]
   ￮ axiom b02 assumed
  
   ￫ info[I0001]
   ￮ axiom b10 assumed
  
   ￫ info[I0001]
   ￮ axiom b11 assumed
  
   ￫ info[I0001]
   ￮ axiom b12 assumed
  
   ￫ info[I0001]
   ￮ axiom b20 assumed
  
   ￫ info[I0001]
   ￮ axiom b21 assumed
  
   ￫ info[I0001]
   ￮ axiom b22 assumed
  
   ￫ info[I0000]
   ￮ constant prod defined
  
   ￫ info[I0000]
   ￮ constant ab22 defined
  
   ￫ info[I0000]
   ￮ constant sym_ab22 defined
  
   ￫ info[I0000]
   ￮ constant sym_ab22' defined
  

  $ narya -v symfield.ny
   ￫ info[I0001]
   ￮ axiom B assumed
  
   ￫ info[I0000]
   ￮ constant A defined
  
   ￫ info[I0001]
   ￮ axiom a00 assumed
  
   ￫ info[I0001]
   ￮ axiom a01 assumed
  
   ￫ info[I0001]
   ￮ axiom a02 assumed
  
   ￫ info[I0001]
   ￮ axiom a10 assumed
  
   ￫ info[I0001]
   ￮ axiom a11 assumed
  
   ￫ info[I0001]
   ￮ axiom a12 assumed
  
   ￫ info[I0001]
   ￮ axiom a20 assumed
  
   ￫ info[I0001]
   ￮ axiom a21 assumed
  
   ￫ info[I0001]
   ￮ axiom a22 assumed
  
  sym a22 .unwrap
    : B⁽ᵉᵉ⁾ (a00 .unwrap) (a10 .unwrap) (a20 .unwrap) (a01 .unwrap)
        (a11 .unwrap) (a21 .unwrap) (a02 .unwrap) (a12 .unwrap)
  
  sym a22 .unwrap
    : B⁽ᵉᵉ⁾ (a00 .unwrap) (a10 .unwrap) (a20 .unwrap) (a01 .unwrap)
        (a11 .unwrap) (a21 .unwrap) (a02 .unwrap) (a12 .unwrap)
  
   ￫ info[I0000]
   ￮ constant Jd defined
  
   ￫ info[I0000]
   ￮ constant test defined
  
