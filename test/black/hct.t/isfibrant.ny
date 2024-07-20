{` Fibrancy is a higher coinductive predicate: an identification of fibrant types comes with transport and lifting functions in both directions, and its underlying correspondence is also fibrant. `}
def isFibrant (A : Type) : Type ≔ codata [
| x .trr.e : A.0 → A.1
| x .trl.e : A.1 → A.0
| x .liftr.e : (a₀ : A.0) → A.2 a₀ (x.2 .trr.1 a₀)
| x .liftl.e : (a₁ : A.1) → A.2 (x.2 .trl.1 a₁) a₁
| x .id.e : (a₀ : A.0) (a₁ : A.1) → isFibrant (A.2 a₀ a₁)
]

{` A fibrant type is a type that is fibrant. `}
def Fib : Type ≔ sig (
  t : Type,
  f : isFibrant t,
)

{` The identity types of a fibrant type are fibrant. `}
def Idf (A : Fib) (x y : A .t) : Fib
  ≔ (Id (A .t) x y, refl A .f .id.1 x y)

{` Basic higher groupoid operations, constructed as in cubical type theory. `}
def transport (A : Type) (B : A → Fib) (x y : A) (p : Id A x y)
  : B x .t → B y .t
  ≔ refl B x y p .f .trr.1

def concat (A : Fib) (x y z : A .t) (p : Id (A .t) x y) (q : Id (A .t) y z)
  : Id (A .t) x z
  ≔ refl (Idf A x) y z q .f .trr.1 p

def inverse (A : Fib) (x y : A .t) (p : Id (A .t) x y)
  : Id (A .t) y x
  ≔ refl ((z ↦ Idf A z x) : A .t → Fib) x y p .f .trr.1 (refl x)

def transport2 (A : Type) (B : A → Fib) (x y : A) (p q : Id A x y)
  (r : Id (Id A x y) p q) (b : B x .t)
  : Id (B y .t) (transport A B x y p b) (transport A B x y q b)
  ≔ B⁽ᵉᵉ⁾ x x (refl x) y y (refl y) p q r .f .id.1
       b (transport A B x y p b) (refl B x y p .f .liftr.1 b)
       b (transport A B x y q b) (refl B x y q .f .liftr.1 b)
       .trr.1 (refl b)

{` Uniform higher operations on squares, arising from higher coinductive fields `}
def refl_transport_1 (A : Type) (B : A → Fib)
  (x₀₀ x₀₁ : A) (x₀₂ : Id A x₀₀ x₀₁) (x₁₀ x₁₁ : A) (x₁₂ : Id A x₁₀ x₁₁)
  (x₂₀ : Id A x₀₀ x₁₀) (x₂₁ : Id A x₀₁ x₁₁)
  (x₂₂ : Id (Id A) x₀₀ x₀₁ x₀₂ x₁₀ x₁₁ x₁₂ x₂₀ x₂₁)
  (y₀ : B x₀₀ .t) (y₁ : B x₁₀ .t) (y₂ : Id B x₀₀ x₁₀ x₂₀ .t y₀ y₁)
  : Id B x₀₁ x₁₁ x₂₁ .t (transport A B x₀₀ x₀₁ x₀₂ y₀) (transport A B x₁₀ x₁₁ x₁₂ y₁)
  ≔ Id (Id B) x₀₀ x₀₁ x₀₂ x₁₀ x₁₁ x₁₂ x₂₀ x₂₁ x₂₂ .f .trr.1 y₀ y₁ y₂

def refl_transport_2 (A : Type) (B : A → Fib)
  (x₀₀ x₀₁ : A) (x₀₂ : Id A x₀₀ x₀₁) (x₁₀ x₁₁ : A) (x₁₂ : Id A x₁₀ x₁₁)
  (x₂₀ : Id A x₀₀ x₁₀) (x₂₁ : Id A x₀₁ x₁₁)
  (x₂₂ : Id (Id A) x₀₀ x₀₁ x₀₂ x₁₀ x₁₁ x₁₂ x₂₀ x₂₁)
  (y₀ : B x₀₀ .t) (y₁ : B x₀₁ .t) (y₂ : Id B x₀₀ x₀₁ x₀₂ .t y₀ y₁)
  : Id B x₁₀ x₁₁ x₁₂ .t (transport A B x₀₀ x₁₀ x₂₀ y₀) (transport A B x₀₁ x₁₁ x₂₁ y₁)
  ≔ Id (Id B) x₀₀ x₀₁ x₀₂ x₁₀ x₁₁ x₁₂ x₂₀ x₂₁ x₂₂ .f .trr.2 y₀ y₁ y₂

{` Two-dimensional globular identity types (which compute to squares with refl on two sides). `}
def Idf2 (A : Fib) (x y : A .t) (p q : Id (A .t) x y) : Fib
  ≔ Idf (Idf A x y) p q

{` The right identity law can be obtained by transporting along a cylinder. `}
def concat_p1 (A : Fib) (x y : A .t) (p : Id (A .t) x y)
  : Id (Id (A .t) x y) (concat A x y y p (refl y)) p
  ≔ refl ((q ↦ Idf2 A x y q p) : Id (A .t) x y → Fib)
       p (concat A x y y p (refl y))
       (refl (Idf A x) y y (refl y) .f .liftr.1 p)
       .f .trr.1 (refl p)

{` The Paulin-Möhring identity type eliminator, constructed as in cubical type theory. `}
def J (A : Fib) (a : A .t) (P : (y : A .t) → Id (A .t) a y → Fib)
      (pa : P a (refl a) .t) (b : A .t) (p : Id (A .t) a b)
  : P b p .t
  ≔ let sq ≔ refl (Idf A a) a b p .f in 
     let q ≔ sq .trr.1 (refl a) in
     let s ≔ sq .liftr.1 (refl a) in
     refl P a b q (refl a) p (sym s) .f .trr.1 pa

{` The type of squares in a fibrant type is also fibrant. `}
def Sqf (A : Fib) (x00 x01 : A .t) (x02 : Id (A .t) x00 x01)
  (x10 x11 : A .t) (x12 : Id (A .t) x10 x11)
  (x20 : Id (A .t) x00 x10) (x21 : Id (A .t) x01 x11)
  : Fib
  ≔ (A⁽ᵉᵉ⁾ .t x00 x01 x02 x10 x11 x12 x20 x21,
     A⁽ᵉᵉ⁾ .f .id.1 x00 x01 x02 x10 x11 x12 .id.1 x20 x21)

{` We can obtain connection squares by applying J to reflexivity squares. `}
def conn (A : Fib) (x y : A .t) (p : Id (A .t) x y)
  : Sqf A x y p y y (refl y) p (refl y) .t
  ≔ J A x (z q ↦ Sqf A x z q z z (refl z) q (refl z)) (refl (refl x)) y p

def coconn (A : Fib) (x y : A .t) (p : Id (A .t) x y)
  : Sqf A x x (refl x) x y p (refl x) p .t
  ≔ J A x (z q ↦ Sqf A x x (refl x) x z q (refl x) q) (refl (refl x)) y p

{` Using a connection square, we can prove the left identity law by a similar cylindrical transport. `}
def concat_1p (A : Fib) (x y : A .t) (p : Id (A .t) x y)
  : Id (Id (A .t) x y) (concat A x x y (refl x) p) p
  ≔ refl (Idf2 A x)
       x y p
       (refl x) (concat A x x y (refl x) p)
       (refl (Idf A x) x y p .f .liftr.1 (refl x))
       (refl x) p (coconn A x y p)
       .f .trr.1 (refl (refl x))

{` Finally, we can prove the typal β-rule for the J-eliminator. `}
def Jβ (A : Fib) (a : A .t) (P : (y : A .t) → Id (A .t) a y → Fib)
      (pa : P a (refl a) .t)
  : Id (P a (refl a) .t) pa (J A a P pa a (refl a))
  ≔ let sq ≔ refl (Idf A a) a a (refl a) .f in
     let q ≔ sq .trr.1 (refl a) in
     let s ≔ sq .liftr.1 (refl a) in
     let cube ≔ refl (Sqf A)
       a a (refl a) a a (refl a) (refl a) (refl a) a⁽ᵉᵉ⁾
       a a (refl a) a a (refl a) (refl a) q s
       (refl a) (refl a) a⁽ᵉᵉ⁾ (refl a) (refl a) a⁽ᵉᵉ⁾ .f in
	   let t ≔ cube .trr.1 a⁽ᵉᵉ⁾ in
	   let c ≔ cube .liftr.1 a⁽ᵉᵉ⁾ in
     P⁽ᵉᵉ⁾ a a (refl a) a a (refl a) (refl a) q (sym t)
       (refl a) (refl a) a⁽ᵉᵉ⁾ (refl a) (refl a) a⁽ᵉᵉ⁾ a⁽ᵉᵉ⁾ (sym s)
       c⁽³²¹⁾ .f .id.1
       pa pa (refl pa)
       pa (J A a P pa a (refl a))
          (refl P a a q (refl a) (refl a) (sym s) .f .liftr.1 pa)
       .trr.1 (refl pa)
