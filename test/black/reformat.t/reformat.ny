axiom A : Type

axiom B : Type

axiom ` line comment
  C
  : Type {` block 1 `}

{` block 2 `}
axiom D ` line comment
  : Type

axiom E
  : `line comment
  Type

axiom {` block
  comment `} F
  : Type

axiom G {` block
  comment `}
  : Type

axiom H
  : {` block
  comment `} Type

axiom I
  {` block 1 `}
  {` block 2 `}
  : Type {` block 3 `}

echo A

echo ` line comment
  A

echo A ` line comment

echo {` block
  comment`} A

def ℕ : Type ≔ data [ zero. | suc. (_ : ℕ) ]

def ℕ1 : Type ≔ data [ ` line comment
| zero.
| suc. (_ : ℕ) ]

def ℕ2 : Type ≔ data [ {` block
comment `}
| zero.
| suc. (_ : ℕ) ]

def ℕ3 : Type ≔ data [
| zero.
| suc. (_ : ℕ) `line comment
]

def ℕ4 : Type ≔ data [
| zero.
| suc.
    (_
     : `line comment
     ℕ) ]

def ℕ5 : Type ≔ data [
| zero.
| suc.
    (_ `line comment
     : ℕ) ]

def ℕ6 : Type ≔ data [
| zero.
| suc. `line comment
    (_ : ℕ) ]

def Vec (A : Type) : ℕ → Type ≔ data [
| nil. : Vec A 0
| cons. (n : ℕ) (x : A) (xs : Vec A n) : Vec A (suc. n) ]

def Vec1 (A : Type) : ℕ → Type ≔ data [
| nil. : Vec1 A 0
| cons. (n : ℕ) {` block
    comment `}
    (x : A) (xs : Vec1 A n)
  : Vec1 A (suc. n) ]

def lots : Type ≔ data [
| boo. (_ : A) (_ : A) (_ : A) (_ : A) (_ : A) (_ : A) (_ : A) (_ : A)
    (_ : A) (_ : A) (_ : A) (_ : A) (_ : A) (_ : A) ]

def lots2 : Type ≔ (data [
| boo. (_ : A) (_ : A) (_ : A) (_ : A) (_ : A) (_ : A) (_ : A) (_ : A)
    (_ : A) (_ : A) (_ : A) (_ : A) (_ : A) (_ : A) ])

def prod (A B : Type) : Type ≔ sig ( fst : A, snd : B )

def prod2 (A B : Type) : Type ≔ sig (
  fst : A, `line comment
  snd : B )

def prod3 (A B : Type) : Type ≔ sig (
  fst : `line comment
    A,
  snd : B )

def prod4 (A B : Type) : Type ≔ sig (
  fst `line comment
    : A,
  snd : B )

def triple : prod ℕ (prod ℕ ℕ) ≔ (0, (0, 0))

def triple2 : prod ℕ (prod ℕ ℕ) ≔ (
  0, `comment
  (0, 0))

def triple3 : prod ℕ (prod ℕ ℕ) ≔ (
  0, `comment
  (0, `comment
   0))

axiom f
  : A → A → A → A → A → A → A → A → A → A → A → A → A → A → A → A → A → A → A →
    A → A
    → ℕ

axiom f2
  : (x ` variable
    : A) ` first arg
    →
    B `second arg
    → C

axiom f3
  : (x : A) ` first arg
    →
    B `second arg
    → C

axiom f4
  : (x : A) → B `second arg
    → C

axiom f5
  : (x : A) → B `second arg
    →
    C → C → C → C → C → C → C → C → C → C → C → C → C → C → C → C → C → C → C
    → C

axiom a : A

def faaa
  ≔ f a `hello
      `goodbye
      a a

def faaa1
  ≔ f a {` hello `}
      `goodbye
      a a

def faaa2
  ≔ f a {` hello
      world `}
      `goodbye
      a a

def faaa3
  ≔ f a
      `goodbye
      a a

def faaa4 ≔ f a a a

def faaa5 ≔ f a a a

axiom a_long_thing : A

def flong : ℕ
  ≔ f a_long_thing a_long_thing a_long_thing a_long_thing a_long_thing
      a_long_thing a_long_thing a_long_thing a_long_thing a_long_thing
      a_long_thing a_long_thing a_long_thing a_long_thing a_long_thing
      a_long_thing a_long_thing a_long_thing a_long_thing a_long_thing
      a_long_thing

def flong2 : ℕ
  ≔ f a_long_thing a_long_thing a_long_thing a_long_thing a_long_thing
      a_long_thing a_long_thing a_long_thing a_long_thing a_long_thing
      a_long_thing a_long_thing a_long_thing a_long_thing a_long_thing
      a_long_thing a_long_thing a_long_thing a_long_thing a_long_thing
      a_long_thing
    : ℕ

def ftype
  : A → A → A → A → A → A → A → A → A → A → A → A → A → A → A → A → A → A → A →
    A
    → Type
  ≔ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ↦ ℕ

def flong3 : ℕ
  ≔ f a_long_thing a_long_thing a_long_thing a_long_thing a_long_thing
      a_long_thing a_long_thing a_long_thing a_long_thing a_long_thing
      a_long_thing a_long_thing a_long_thing a_long_thing a_long_thing
      a_long_thing a_long_thing a_long_thing a_long_thing a_long_thing
      a_long_thing
    : ftype a_long_thing a_long_thing a_long_thing a_long_thing a_long_thing
        a_long_thing a_long_thing a_long_thing a_long_thing a_long_thing
        a_long_thing a_long_thing a_long_thing a_long_thing a_long_thing
        a_long_thing a_long_thing a_long_thing a_long_thing a_long_thing

axiom ftoftype
  : A → A → A → A → A → A → A → A → A → A → A → A → A → A → A → A → A → A → A →
    A → A
    → ftype a_long_thing a_long_thing a_long_thing a_long_thing a_long_thing
        a_long_thing a_long_thing a_long_thing a_long_thing a_long_thing
        a_long_thing a_long_thing a_long_thing a_long_thing a_long_thing
        a_long_thing a_long_thing a_long_thing a_long_thing a_long_thing

axiom a_very_long_type_to_wrap_the_line : Type

axiom a_very_long_term_to_wrap_the_line : a_very_long_type_to_wrap_the_line

def a_very_long_thing_to_wrap_the_line : a_very_long_type_to_wrap_the_line
  ≔ a_very_long_term_to_wrap_the_line

axiom Q : ℕ → Type

{`
def qq
: Q
(f a_long_thing a_long_thing a_long_thing a_long_thing
a_long_thing a_long_thing a_long_thing a_long_thing
a_long_thing a_long_thing a_long_thing a_long_thing
a_long_thing a_long_thing a_long_thing a_long_thing
a_long_thing a_long_thing a_long_thing a_long_thing
a_long_thing)
→ Q
(f a_long_thing a_long_thing a_long_thing a_long_thing
a_long_thing a_long_thing a_long_thing a_long_thing
a_long_thing a_long_thing a_long_thing a_long_thing
a_long_thing a_long_thing a_long_thing a_long_thing
a_long_thing a_long_thing a_long_thing a_long_thing
a_long_thing)
≔ x ↦ ?
`}

def pair : prod ℕ ℕ ≔ (
  f a a a a a a a a a a a a a a a a a a a a a,
  f a a a a a a a a a a a a a a a a a a a a a)

def pair2 : prod ℕ ℕ ≔ (
  fst ≔ f a a a a a a a a a a a a a a a a a a a a a,
  snd ≔ f a a a a a a a a a a a a a a a a a a a a a)

def lpair2 : prod ℕ ℕ ≔ (
  fst ≔
    f a_long_thing a_long_thing a_long_thing a_long_thing a_long_thing
      a_long_thing a_long_thing a_long_thing a_long_thing a_long_thing
      a_long_thing a_long_thing a_long_thing a_long_thing a_long_thing
      a_long_thing a_long_thing a_long_thing a_long_thing a_long_thing
      a_long_thing,
  snd ≔
    f a_long_thing a_long_thing a_long_thing a_long_thing a_long_thing
      a_long_thing a_long_thing a_long_thing a_long_thing a_long_thing
      a_long_thing a_long_thing a_long_thing a_long_thing a_long_thing
      a_long_thing a_long_thing a_long_thing a_long_thing a_long_thing
      a_long_thing)

def triple4 : prod ℕ (prod ℕ ℕ) ≔ (
  fst ≔ f a a a a a a a a a a a a a a a a a a a a a,
  snd ≔ (
    f a a a a a a a a a a a a a a a a a a a a a,
    f a a a a a a a a a a a a a a a a a a a a a))

` This is the purpose of the 'trivial' intros data
def triple5 : prod ℕ (prod ℕ ℕ) ≔ (
  f a a a a a a a a a a a a a a a a a a a a a,
  (f a a a a a a a a a a a a a a a a a a a a a,
   f a a a a a a a a a a a a a a a a a a a a a))

def abstriple : ℕ → prod ℕ (prod ℕ ℕ) ≔ x ↦ (
  fst ≔ f a a a a a a a a a a a a a a a a a a a a a,
  snd ≔ (
    f a a a a a a a a a a a a a a a a a a a a a,
    f a a a a a a a a a a a a a a a a a a a a a))

def abstriple1 : ℕ → prod ℕ (prod ℕ ℕ)
  ≔ this_is_a_very_long_variable_name_to_wrap_the_line ↦ (
  fst ≔ f a a a a a a a a a a a a a a a a a a a a a,
  snd ≔ (
    f a a a a a a a a a a a a a a a a a a a a a,
    f a a a a a a a a a a a a a a a a a a a a a))

def id : ℕ → ℕ
  ≔ a_very_long_variable_name ↦ match a_very_long_variable_name [
| zero. ↦ zero.
| suc. x ↦ suc. x]

def id2 : ℕ → ℕ
  ≔ this_is_a_very_long_variable_name_to_wrap_the_line ↦
      match this_is_a_very_long_variable_name_to_wrap_the_line [
| zero. ↦ zero.
| suc. x ↦ suc. x]

def ⊤ : Type ≔ sig ()

def ⊥ : Type ≔ data []

def ℕeq : ℕ → ℕ → Type ≔ m n ↦ match m [
| zero. ↦ match n [ zero. ↦ ⊤ | suc. _ ↦ ⊥ ]
| suc. m ↦ match n [ zero. ↦ ⊥ | suc. n ↦ ℕeq m n ]]

def longfun : Type
  ≔ (x : A) (x : A) (x : A) (x : A) (x : A) (x : A) (x : A) (x : A) (x : A)
    (x : A)
    → C

def longfun1 : Type
  ≔ (x : A) → (x : A) → (x : A) → (x : A) → (x : A) → (x : A) → (x : A) →
    (x : A)
    → C

def longfun2 : Type ≔ A → A → A → A → A → A → A → A → A → A → B

def longfun3 : Type
  ≔ A → A → A → A → A → A → A → A → A → A → A → A → A → A → A → A → A → A → A
    → B

def longfun4 : Type
  ≔ (x : A) (x : A) (x : A) → A → (x : A) (_ : A) (x : A) (x : A) → (x : A)
    → C

axiom P : ℕ → Type

{` This looks a little weird, but I think only because "P" is so short. `}
def longfun5 : Type
  ≔ A → A → A →
    P
      (f a_long_thing a_long_thing a_long_thing a_long_thing a_long_thing
         a_long_thing a_long_thing a_long_thing a_long_thing a_long_thing
         a_long_thing a_long_thing a_long_thing a_long_thing a_long_thing
         a_long_thing a_long_thing a_long_thing a_long_thing a_long_thing
         a_long_thing) → A → A
    → B

def wrap (A : Type) : Type ≔ codata [ x .unwrap : A ]

axiom object
  : A → A → A → A → A → A → A
    → wrap
        (A → A → A → A → A → wrap (A → A → A → A → A → A → wrap (A → A → B)))

def objectb : B
  ≔ object a_long_thing a_long_thing a_long_thing a_long_thing a_long_thing
        a_long_thing a_long_thing
      .unwrap a_long_thing a_long_thing a_long_thing a_long_thing
        a_long_thing
      .unwrap a_long_thing a_long_thing a_long_thing a_long_thing
        a_long_thing a_long_thing
      .unwrap a_long_thing a_long_thing

axiom bareobj : wrap (A → A → A → A → A → B)

def bareb : B
  ≔ bareobj .unwrap a_long_thing a_long_thing a_long_thing a_long_thing
      a_long_thing

axiom toobj : A → A → A → A → A → A → A → A → wrap B

def tob : B
  ≔ toobj a_long_thing a_long_thing a_long_thing a_long_thing a_long_thing
      a_long_thing a_long_thing a_long_thing .unwrap

axiom wraps
  : wrap
      (wrap
         (wrap
            (wrap
               (wrap
                  (wrap
                     (wrap
                        (wrap
                           (wrap
                              (wrap
                                 (wrap
                                    (wrap
                                       (wrap
                                          (wrap
                                             (wrap
                                                (wrap
                                                   (wrap
                                                      (wrap (wrap (wrap B)))))))))))))))))))

def wrapb : B
  ≔ wraps .unwrap .unwrap .unwrap .unwrap .unwrap .unwrap .unwrap .unwrap
      .unwrap .unwrap .unwrap .unwrap .unwrap .unwrap .unwrap .unwrap .unwrap
      .unwrap .unwrap .unwrap

def bigabs
  : A → A → A → A → A → A → A → A → A → A → A → A → A → A → A → A → A → A → A →
    A
    → A
  ≔ longvar longvar longvar longvar longvar longvar longvar longvar longvar
      longvar longvar longvar longvar longvar longvar longvar longvar longvar
      longvar longvar ↦
    longvar

def plus : ℕ → ℕ → ℕ ≔ [ zero. ↦ n ↦ n | suc. m ↦ n ↦ suc. (plus m n) ]

def tlet0 : ℕ ≔ let a_long_variable : ℕ ≔ 0 in a_long_variable

def tlet00 : ℕ ≔
  let an_even_longer_variable_name : ℕ ≔ 0 in
  an_even_longer_variable_name

def tlet : ℕ ≔
  let a_long_variable : ℕ ≔ (plus (plus 0 (plus 0 0)) (plus 0 (plus 0 0))) in
  a_long_variable

def tlet1 : ℕ ≔
  let a_long_variable
    : A → A → A → A → A → A → A → A → A → A → A → A → A → A → ℕ
    ≔ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ↦
      (plus (plus 0 (plus 0 0)) (plus 0 (plus 0 0))) in
  a_long_variable a a a a a a a a a a a a a a

def tlet2 : prod ℕ ℕ ≔
  let a_long_variable : ℕ ≔ (plus (plus 0 (plus 0 0)) (plus 0 (plus 0 0))) in
  (a_long_variable, a_long_variable)

def dlet : ℕ ≔ let a_long_variable : ℕ ≔ 0 in let y : ℕ ≔ 0 in y

def dlet2 : ℕ ≔
  let a_long_variable : ℕ ≔ 0 in
  let another_long_variable : ℕ ≔ 0 in
  another_long_variable

{` TODO: Could we collapse those abstractions onto one line? `}
def dlet3 : A → A → A → A → ℕ ≔
  let a_long_variable : ℕ ≔ 0 in
  x y ↦
  z w ↦
  let another_long_variable : ℕ ≔ 0 in
  let yet_another_long_variable : ℕ ≔ 0 in
  another_long_variable

def dlet4 : A → A → A → A → ℕ ≔ x ↦
  let a_long_variable : ℕ ≔ 0 in
  y z ↦
  let another_long_variable : ℕ ≔ 0 in
  let yet_another_long_variable : ℕ ≔ 0 in
  w ↦ another_long_variable

def mlet : ℕ → ℕ → ℕ ≔
  let a_long_variable : ℕ ≔ (plus (plus 0 (plus 0 0)) (plus 0 (plus 0 0))) in
  match a_long_variable [
  | zero. ↦
      let another_long_variable : ℕ
        ≔ (plus (plus 0 (plus 0 0)) (plus 0 (plus 0 0))) in
      x ↦ y ↦ 0
  | suc. _ ↦ x ↦ y ↦ 0]

def mtup : ℕ → prod ℕ ℕ ≔ [ zero. ↦ (0, 0) | suc. n ↦ (n, n) ]

def mtup2 : ℕ → prod ℕ ℕ ≔ [
| zero. ↦ (
    0, `line comment
    0)
| suc. n ↦ (fst ≔ n, snd ≔ n)]

def mtm : ℕ → ℕ → prod ℕ ℕ ≔ m ↦ [
| zero. ↦ (match m [ zero. ↦ 0 | suc. m ↦ 0 ], 0)
| suc. n ↦ (fst ≔ n, snd ≔ match m [ zero. ↦ 0 | suc. m ↦ 0 ])]

axiom blahblah : A → A → A → A

axiom blahblah2 : A → A

axiom blahblah3 : A

def blahblah4 : A
  ≔ blahblah (blahblah2 blahblah3) (blahblah2 (blahblah2 blahblah3))
      (blahblah blahblah3 blahblah3 blahblah3)

def blahblah5 : A
  ≔ blahblah (blahblah2 blahblah3) ` line comment
      (blahblah2 (blahblah2 blahblah3))
      (blahblah blahblah3 blahblah3 blahblah3)

def blahblah6 : A
  ≔ blahblah ` line comment
      (blahblah2 blahblah3) (blahblah2 (blahblah2 blahblah3))
      (blahblah blahblah3 blahblah3 blahblah3)

def blahblah7 : A → A
  ≔ bleh ↦
    blahblah ` line comment
      (blahblah2 blahblah3) (blahblah2 (blahblah2 blahblah3))
      (blahblah blahblah3 blahblah3 blahblah3)

def blahblah8 : A → A → A → A → A → A → A → A → A → A → A → A → A
  ≔ blehbleh blehbleh blehbleh blehbleh blehbleh blehbleh blehbleh blehbleh
      blehbleh blehbleh blehbleh blehbleh ↦
    blahblah ` line comment
      (blahblah2 blahblah3) (blahblah2 (blahblah2 blahblah3))
      (blahblah blahblah3 blahblah3 blahblah3)

def blubblub : A → A → A → A → A → Type ≔ _ _ _ _ _ ↦ A

def bb : A ≔
  let bubble
    : blubblub blahblah3 blahblah3 (blahblah2 (blahblah2 blahblah3))
        blahblah3 blahblah3
    ≔ blahblah (blahblah2 blahblah3) (blahblah2 (blahblah2 blahblah3))
        (blahblah blahblah3 blahblah3 blahblah3) in
  bubble

axiom unpair : prod A A → A

def unpaired : A ≔ unpair (a, a)

def unpaired2 : A
  ≔ unpair
      (blahblah (blahblah2 blahblah3) (blahblah2 (blahblah2 blahblah3))
         (blahblah blahblah3 blahblah3 blahblah3),
       blahblah (blahblah2 blahblah3) (blahblah2 (blahblah2 blahblah3))
         (blahblah blahblah3 blahblah3 blahblah3))

def unpaired3 : A
  ≔ unpair (blahblah2 (blahblah2 blahblah3), blahblah2 (blahblah2 blahblah3))

def unpaired4 : A
  ≔ unpair
      (fst ≔ blahblah2 (blahblah2 blahblah3),
       snd ≔ blahblah2 (blahblah2 blahblah3))

def ml : ℕ → ℕ ≔ let x : ℕ ≔ 0 in [ zero. ↦ 0 | suc. _ ↦ 0 ]

def ml2 : ℕ → ℕ ≔
  let x : ℕ ≔ 0 in
  [ zero. ` line comment
    ↦
    0
  | suc. _ ↦ 0]

def ml3 : ℕ → ℕ ≔
  let x : ℕ ≔ 0 in
  [ zero. ↦ 0 ` line comment
  | suc. _ ↦ 0]

def stream (A : Type) : Type ≔ codata [ x .head : A | x .tail : stream A ]

def zeros : stream ℕ ≔ [ .head ↦ 0 | .tail ↦ zeros ]

def zeros2 : stream ℕ ≔ [
| .head ↦ 0 `comment
| .tail ↦ zeros]

def dup : ℕ → stream ℕ ≔ n ↦ [
| .head ↦ match n [ zero. ↦ 0 | suc. _ ↦ 0 ]
| .tail ↦ dup n]

def fs : stream ℕ ≔ [
| .head ↦
    f a_long_thing a_long_thing a_long_thing a a a a a a a a a a a a a a a a
      a_long_thing a_long_thing
| .tail ↦ zeros]

def ssz : stream (stream ℕ) ≔ [
| .head ↦ [ .head ↦ 0 | .tail ↦ ssz .head ]
| .tail ↦ ssz]

axiom fsn
  : A → A → A → A → A → A → A → A → A → A → stream (stream ℕ)
    → stream (stream ℕ)

def ssz2 : stream (stream ℕ) ≔ [
| .head ↦ [
  | .head ↦ 0
  | .tail ↦
      fsn a_long_thing a a_long_thing a a_long_thing a a_long_thing a
        a_long_thing a_long_thing ssz2 .head]
| .tail ↦ ssz]

def mss : ℕ → stream (stream (prod ℕ ℕ)) ≔ n ↦ [
| .head ↦ [
  | .head ↦ match n [ zero. ↦ (0, 0) | suc. n ↦ (0, n) ]
  | .tail ↦ mss 0 .head]
| .tail ↦ mss 0]

notation 3 prod : A "×" B ≔ prod A B

notation 3 prod₁ : AAAAAAAAAAAAAAAAAAAA "×₁" BBBBBBBBBBBBBBBBBBBB
  ≔ prod AAAAAAAAAAAAAAAAAAAA BBBBBBBBBBBBBBBBBBBB

notation 3 prod₂
  : AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA "×₂"
      BBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBB
  ≔ prod AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA
      BBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBB

echo ℕ

echo f a_long_thing a_long_thing a_long_thing a_long_thing a_long_thing

echo f a_long_thing a_long_thing a_long_thing a_long_thing a_long_thing
       a_long_thing a_long_thing a_long_thing a_long_thing a_long_thing

synth f a_long_thing a_long_thing a_long_thing a_long_thing a_long_thing
        a_long_thing a_long_thing a_long_thing a_long_thing a_long_thing

section foo ≔

  def x : ℕ ≔ 3

  def fooflong : ℕ
    ≔ f a_long_thing a_long_thing a_long_thing a_long_thing a_long_thing
        a_long_thing a_long_thing a_long_thing a_long_thing a_long_thing
        a_long_thing a_long_thing a_long_thing a_long_thing a_long_thing
        a_long_thing a_long_thing a_long_thing a_long_thing a_long_thing
        a_long_thing

  section bar ≔

    def y : ℕ ≔ f a a a a a a a a a a a a a a a a a a a a a

  end

end

def x : ℕ ≔ 0

and y : ℕ ≔ 0

{` block comment `}
def x2 : ℕ ≔ 0 ` line comment

`line comment
and y2 : ℕ ≔ 0

def xy : ℕ ≔ let rec x : ℕ ≔ 0 and y : ℕ ≔ 0 in x

def xy1 : ℕ ≔
  let rec x : ℕ ≔ 0 `line comment
  {` block comment `}
  and y : ℕ ≔ 0 in
  x

def xy2 : ℕ ≔
  let rec x : ℕ `line comment
    ≔ 0
  and y `line comment
    : ℕ
    ≔ 0 in
  x

import "importable"

import "importable" | all

import "importable"
  | seq (renaming squab squish,
         renaming squish squab,
         renaming squab squish,
         renaming squish squab)

{` long parameter lists `}
def eq (A : Type) (a : A) : A → Type ≔ data [ rfl. : eq A a a ]

def cat (A : Type) (x y z : A) (u : eq A x y) (v : eq A y z) : eq A x z
  ≔ match v [ rfl. ↦ u ]

def cat3 (A : Type) (x y z w : A) (p : eq A x y) (q : eq A y z)
  (r : eq A z w)
  : eq A x w
  ≔ match q, r [ rfl., rfl. ↦ p ]

{` empty match `}

def abort (A : Type) (e : ⊥) : A ≔ match e [ ]

{` fractional tightness notations `}
axiom binop : A → A → A

notation 1.5 binop : x "*+*" y ≔ binop x y

