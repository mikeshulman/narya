import "isfibrant"
import "bookhott"
import "hott_bookhott"

option function boundaries ≔ implicit
option type boundaries ≔ implicit

{` Since identity types compute only up to definitional isomorphism, in order to prove that anything is fibrant by corecursion, we need to be able to transport fibrancy across definitional isomorphisms.  In fact, we can transport it across any Book-HoTT equivalence defined using the Martin-Lof identity type. `}

{` The unit type `}

def ⊤ : Type ≔ sig ()

def id_⊤_iso (x y : ⊤) : ⊤ ≅ Id ⊤ x y ≔ (
  to ≔ _ ↦ (),
  fro ≔ _ ↦ (),
  to_fro ≔ _ ↦ rfl.,
  fro_to ≔ _ ↦ rfl.,
  to_fro_to ≔ _ ↦ rfl.)

def 𝕗⊤ : isFibrant ⊤ ≔ [
| .trr.e ↦ x ↦ x
| .trl.e ↦ x ↦ x
| .liftr.e ↦ _ ↦ ()
| .liftl.e ↦ _ ↦ ()
| .id.e ↦ x y ↦ 𝕗eqv ⊤ (Id ⊤ x y) (id_⊤_iso x y) 𝕗⊤]

{` Product types `}

def prod (A B : Type) : Type ≔ sig ( fst : A, snd : B )

notation 2 prod : A "×" B ≔ prod A B

def id_prod_iso (A0 : Type) (A1 : Type) (A2 : Id Type A0 A1) (B0 : Type)
  (B1 : Type) (B2 : Id Type B0 B1) (a0 : A0) (a1 : A1) (b0 : B0) (b1 : B1)
  : A2 a0 a1 × B2 b0 b1 ≅ Id prod A2 B2 (a0, b0) (a1, b1)
  ≔ (
  to ≔ u ↦ (u .fst, u .snd),
  fro ≔ v ↦ (v .fst, v .snd),
  to_fro ≔ _ ↦ rfl.,
  fro_to ≔ _ ↦ rfl.,
  to_fro_to ≔ _ ↦ rfl.)

def 𝕗prod (A B : Type) (𝕗A : isFibrant A) (𝕗B : isFibrant B)
  : isFibrant (A × B)
  ≔ [
| .trr.e ↦ u0 ↦ (𝕗A.2 .trr.1 (u0 .fst), 𝕗B.2 .trr.1 (u0 .snd))
| .trl.e ↦ u1 ↦ (𝕗A.2 .trl.1 (u1 .fst), 𝕗B.2 .trl.1 (u1 .snd))
| .liftr.e ↦ u0 ↦ (𝕗A.2 .liftr.1 (u0 .fst), 𝕗B.2 .liftr.1 (u0 .snd))
| .liftl.e ↦ u1 ↦ (𝕗A.2 .liftl.1 (u1 .fst), 𝕗B.2 .liftl.1 (u1 .snd))
| .id.e ↦ u0 u1 ↦
    𝕗eqv (A.2 (u0 .fst) (u1 .fst) × B.2 (u0 .snd) (u1 .snd))
      (refl prod A.2 B.2 u0 u1)
      (id_prod_iso A.0 A.1 A.2 B.0 B.1 B.2 (u0 .fst) (u1 .fst) (u0 .snd)
         (u1 .snd))
      (𝕗prod (A.2 (u0 .fst) (u1 .fst)) (B.2 (u0 .snd) (u1 .snd))
         (𝕗A.2 .id.1 (u0 .fst) (u1 .fst)) (𝕗B.2 .id.1 (u0 .snd) (u1 .snd)))]

{` Σ-types `}

def Σ (A : Type) (B : A → Type) : Type ≔ sig ( fst : A, snd : B fst )

def id_Σ_iso (A0 : Type) (A1 : Type) (A2 : Id Type A0 A1) (B0 : A0 → Type)
  (B1 : A1 → Type) (B2 : Id Π A2 {_ ↦ Type} {_ ↦ Type} (_ ⤇ refl Type) B0 B1)
  (a0 : A0) (a1 : A1) (b0 : B0 a0) (b1 : B1 a1)
  : Σ (A2 a0 a1) (a2 ↦ B2 a2 b0 b1) ≅ Id Σ A2 B2 (a0, b0) (a1, b1)
  ≔ (
  to ≔ u ↦ (u .fst, u .snd),
  fro ≔ v ↦ (v .fst, v .snd),
  to_fro ≔ _ ↦ rfl.,
  fro_to ≔ _ ↦ rfl.,
  to_fro_to ≔ _ ↦ rfl.)

def 𝕗Σ (A : Type) (B : A → Type) (𝕗A : isFibrant A)
  (𝕗B : (x : A) → isFibrant (B x))
  : isFibrant (Σ A B)
  ≔ [
| .trr.e ↦ u0 ↦ (
    𝕗A.2 .trr.1 (u0 .fst),
    𝕗B.2 (𝕗A.2 .liftr.1 (u0 .fst)) .trr.1 (u0 .snd))
| .trl.e ↦ u1 ↦ (
    𝕗A.2 .trl.1 (u1 .fst),
    𝕗B.2 (𝕗A.2 .liftl.1 (u1 .fst)) .trl.1 (u1 .snd))
| .liftr.e ↦ u0 ↦ (
    𝕗A.2 .liftr.1 (u0 .fst),
    𝕗B.2 (𝕗A.2 .liftr.1 (u0 .fst)) .liftr.1 (u0 .snd))
| .liftl.e ↦ u1 ↦ (
    𝕗A.2 .liftl.1 (u1 .fst),
    𝕗B.2 (𝕗A.2 .liftl.1 (u1 .fst)) .liftl.1 (u1 .snd))
| .id.e ↦ u0 u1 ↦
    𝕗eqv (Σ (A.2 (u0 .fst) (u1 .fst)) (a2 ↦ B.2 a2 (u0 .snd) (u1 .snd)))
      (Id Σ A.2 B.2 u0 u1)
      (id_Σ_iso A.0 A.1 A.2 B.0 B.1 B.2 (u0 .fst) (u1 .fst) (u0 .snd)
         (u1 .snd))
      (𝕗Σ (A.2 (u0 .fst) (u1 .fst)) (a2 ↦ B.2 a2 (u0 .snd) (u1 .snd))
         (𝕗A.2 .id.1 (u0 .fst) (u1 .fst))
         (a2 ↦ 𝕗B.2 a2 .id.1 (u0 .snd) (u1 .snd)))]

{` Π-types `}

def id_Π_iso (A0 : Type) (A1 : Type) (A2 : Id Type A0 A1) (B0 : A0 → Type)
  (B1 : A1 → Type) (B2 : Id Π A2 {_ ↦ Type} {_ ↦ Type} (_ ⤇ refl Type) B0 B1)
  (f0 : (a0 : A0) → B0 a0) (f1 : (a1 : A1) → B1 a1)
  : ((a0 : A0) (a1 : A1) (a2 : A2 a0 a1) → B2 a2 (f0 a0) (f1 a1))
    ≅ Id Π A2 B2 f0 f1
  ≔ (
  to ≔ f ↦ a ⤇ f a.0 a.1 a.2,
  fro ≔ g ↦ a0 a1 a2 ↦ g a2,
  to_fro ≔ _ ↦ rfl.,
  fro_to ≔ _ ↦ rfl.,
  to_fro_to ≔ _ ↦ rfl.)

def 𝕗Π (A : Type) (B : A → Type) (𝕗A : isFibrant A)
  (𝕗B : (x : A) → isFibrant (B x))
  : isFibrant ((x : A) → B x)
  ≔ [
| .trr.e ↦ f0 a1 ↦ 𝕗B.2 (𝕗A.2 .liftl.1 a1) .trr.1 (f0 (𝕗A.2 .trl.1 a1))
| .trl.e ↦ f1 a0 ↦ 𝕗B.2 (𝕗A.2 .liftr.1 a0) .trl.1 (f1 (𝕗A.2 .trr.1 a0))
| .liftr.e ↦ f0 a ⤇
    refl 𝕗B.2
        (sym
           (sym (refl 𝕗A.2) .id.1 a.2 (𝕗A.2 .liftl.1 a.1) .liftl.1 (refl a.1)))
      .id.1
        (refl f0 (𝕗A.2⁽ᵉ¹⁾ .id.1 a.2 (𝕗A.2 .liftl.1 a.1) .trl.1 (refl a.1)))
        (refl (𝕗B.2 (𝕗A.2 .liftl.1 a.1) .trr.1 (f0 (𝕗A.2 .trl.1 a.1))))
      .trl.1 (𝕗B.2 (𝕗A.2 .liftl.1 a.1) .liftr.1 (f0 (𝕗A.2 .trl.1 a.1)))
| .liftl.e ↦ f1 a ⤇
    refl 𝕗B.2
        (sym
           (sym (refl 𝕗A.2) .id.1 a.2 (𝕗A.2 .liftr.1 a.0) .liftr.1 (refl a.0)))
      .id.1 (refl (𝕗B.2 (𝕗A.2 .liftr.1 a.0) .trl.1 (f1 (𝕗A.2 .trr.1 a.0))))
        (refl f1 (𝕗A.2⁽ᵉ¹⁾ .id.1 a.2 (𝕗A.2 .liftr.1 a.0) .trr.1 (refl a.0)))
      .trl.1 (𝕗B.2 (𝕗A.2 .liftr.1 a.0) .liftl.1 (f1 (𝕗A.2 .trr.1 a.0)))
| .id.e ↦ f0 f1 ↦
    𝕗eqv ((a0 : A.0) (a1 : A.1) (a2 : A.2 a0 a1) → B.2 a2 (f0 a0) (f1 a1))
      (Id Π A.2 B.2 f0 f1) (id_Π_iso A.0 A.1 A.2 B.0 B.1 B.2 f0 f1)
      (𝕗Π A.0 (a0 ↦ (a1 : A.1) (a2 : A.2 a0 a1) → B.2 a2 (f0 a0) (f1 a1))
         𝕗A.0
         (a0 ↦
          𝕗Π A.1 (a1 ↦ (a2 : A.2 a0 a1) → B.2 a2 (f0 a0) (f1 a1)) 𝕗A.1
            (a1 ↦
             𝕗Π (A.2 a0 a1) (a2 ↦ B.2 a2 (f0 a0) (f1 a1)) (𝕗A.2 .id.1 a0 a1)
               (a2 ↦ 𝕗B.2 a2 .id.1 (f0 a0) (f1 a1)))))]

{` Empty type `}

def ∅ : Type ≔ data []

def 𝕗∅ : isFibrant ∅ ≔ [
| .trr.e ↦ [ ]
| .trl.e ↦ [ ]
| .liftr.e ↦ [ ]
| .liftl.e ↦ [ ]
| .id.e ↦ [ ]]

{` Sum type `}

def sum (A B : Type) : Type ≔ data [ left. (_ : A) | right. (_ : B) ]

notation 1.5 sum : A "⊔" B ≔ sum A B

def sum_code (A0 A1 : Type) (A2 : Id Type A0 A1) (B0 B1 : Type)
  (B2 : Id Type B0 B1) (u0 : A0 ⊔ B0) (u1 : A1 ⊔ B1)
  : Type
  ≔ match u0, u1 [
| left. a0, left. a1 ↦ A2 a0 a1
| left. a0, right. b1 ↦ ∅
| right. b0, left. a1 ↦ ∅
| right. b0, right. b1 ↦ B2 b0 b1]

def id_sum_iso (A0 A1 : Type) (A2 : Id Type A0 A1) (B0 B1 : Type)
  (B2 : Id Type B0 B1) (u0 : A0 ⊔ B0) (u1 : A1 ⊔ B1)
  : sum_code A0 A1 A2 B0 B1 B2 u0 u1 ≅ Id sum A2 B2 u0 u1
  ≔ (
  to ≔ v2 ↦ match u0, u1 [
  | left. a0, left. a1 ↦ left. v2
  | left. a0, right. b1 ↦ match v2 [ ]
  | right. b0, left. a1 ↦ match v2 [ ]
  | right. b0, right. b1 ↦ right. v2],
  fro ≔ [ left. a2 ↦ a2 | right. b2 ↦ b2 ],
  to_fro ≔ [ left. a2 ↦ rfl. | right. b2 ↦ rfl. ],
  fro_to ≔ v2 ↦ match u0, u1 [
  | left. a0, left. a1 ↦ rfl.
  | left. a0, right. b1 ↦ match v2 [ ]
  | right. b0, left. a1 ↦ match v2 [ ]
  | right. b0, right. b1 ↦ rfl.],
  to_fro_to ≔ v2 ↦ match u0, u1 [
  | left. a0, left. a1 ↦ rfl.
  | left. a0, right. b1 ↦ match v2 [ ]
  | right. b0, left. a1 ↦ match v2 [ ]
  | right. b0, right. b1 ↦ rfl.])

def 𝕗sum (A B : Type) (𝕗A : isFibrant A) (𝕗B : isFibrant B)
  : isFibrant (A ⊔ B)
  ≔ [
| .trr.e ↦ [
  | left. a0 ↦ left. (𝕗A.2 .trr.1 a0)
  | right. b0 ↦ right. (𝕗B.2 .trr.1 b0)]
| .trl.e ↦ [
  | left. a1 ↦ left. (𝕗A.2 .trl.1 a1)
  | right. b1 ↦ right. (𝕗B.2 .trl.1 b1)]
| .liftr.e ↦ [
  | left. a0 ↦ left. (𝕗A.2 .liftr.1 a0)
  | right. b0 ↦ right. (𝕗B.2 .liftr.1 b0)]
| .liftl.e ↦ [
  | left. a1 ↦ left. (𝕗A.2 .liftl.1 a1)
  | right. b1 ↦ right. (𝕗B.2 .liftl.1 b1)]
| .id.e ↦ u0 u1 ↦ (
    𝕗eqv (sum_code A.0 A.1 A.2 B.0 B.1 B.2 u0 u1) (Id sum A.2 B.2 u0 u1)
      (id_sum_iso A.0 A.1 A.2 B.0 B.1 B.2 u0 u1)
      (match u0, u1 [
       | left. a0, left. a1 ↦ 𝕗A.2 .id.1 a0 a1
       | left. _, right. _ ↦ 𝕗∅
       | right. _, left. _ ↦ 𝕗∅
       | right. b0, right. b1 ↦ 𝕗B.2 .id.1 b0 b1]))]

{` The natural numbers `}

def ℕ : Type ≔ data [ zero. | suc. (_ : ℕ) ]

def ℕ_code (m n : ℕ) : Type ≔ match m, n [
| zero., zero. ↦ ⊤
| zero., suc. _ ↦ ∅
| suc. _, zero. ↦ ∅
| suc. m, suc. n ↦ ℕ_code m n]

def id_ℕ_iso (n0 n1 : ℕ) : ℕ_code n0 n1 ≅ Id ℕ n0 n1
  ≔ adjointify (ℕ_code n0 n1) (Id ℕ n0 n1)
      (m2 ↦
       match n0, n1 [
       | zero., zero. ↦ zero.
       | zero., suc. n1 ↦ match m2 [ ]
       | suc. n0, zero. ↦ match m2 [ ]
       | suc. n0, suc. n1 ↦ suc. (id_ℕ_iso n0 n1 .to m2)])
      ([ zero. ↦ () | suc. m2 ↦ id_ℕ_iso m2.0 m2.1 .fro m2.2 ])
      (m2 ↦
       match n0, n1 [
       | zero., zero. ↦ rfl.
       | zero., suc. n1 ↦ match m2 [ ]
       | suc. n0, zero. ↦ match m2 [ ]
       | suc. n0, suc. n1 ↦ id_ℕ_iso n0 n1 .fro_to m2])
      ([ zero. ↦ rfl.
       | suc. m2 ↦
           eq.ap (Id ℕ m2.0 m2.1) (Id ℕ (suc. m2.0) (suc. m2.1)) (x ↦ suc. x)
             (id_ℕ_iso m2.0 m2.1 .to (id_ℕ_iso m2.0 m2.1 .fro m2.2)) m2.2
             (id_ℕ_iso m2.0 m2.1 .to_fro m2.2)])

def 𝕗_ℕ_code (n0 n1 : ℕ) : isFibrant (ℕ_code n0 n1) ≔ match n0, n1 [
| zero., zero. ↦ 𝕗⊤
| zero., suc. n1 ↦ 𝕗∅
| suc. n0, zero. ↦ 𝕗∅
| suc. n0, suc. n1 ↦ 𝕗_ℕ_code n0 n1]

def 𝕗ℕ : isFibrant ℕ ≔ [
| .trr.e ↦ x ↦ x
| .trl.e ↦ x ↦ x
| .liftr.e ↦ x ↦ refl x
| .liftl.e ↦ x ↦ refl x
| .id.e ↦ n0 n1 ↦
    𝕗eqv (ℕ_code n0 n1) (Id ℕ n0 n1) (id_ℕ_iso n0 n1) (𝕗_ℕ_code n0 n1)]

{` Gel types `}

def Gel (A B : Type) (R : A → B → Type) : Id Type A B ≔ sig a b ↦ (
  ungel : R a b )

def Gel_iso (A B : Type) (R : A → B → Type) (a : A) (b : B)
  : R a b ≅ Gel A B R a b
  ≔ (
  to ≔ r ↦ (r,),
  fro ≔ g ↦ g .0,
  to_fro ≔ _ ↦ rfl.,
  fro_to ≔ _ ↦ rfl.,
  to_fro_to ≔ _ ↦ rfl.)

def 𝕗Gel (A B : Type) (R : A → B → Type)
  (𝕗R : (a : A) (b : B) → isFibrant (R a b)) (a : A) (b : B)
  : isFibrant (Gel A B R a b)
  ≔ 𝕗eqv (R a b) (Gel A B R a b) (Gel_iso A B R a b) (𝕗R a b)

{` The universe `}

{`
def over_and_back (B0 B1 : Fib) (B2 : Id Fib B0 B1) (b0 : B0 .t)
  : Id B0 .t (B2 .f .trl.1 (B2 .f .trr.1 b0)) b0
  ≔ B2⁽ᵉ¹⁾
      .f
      .id.1 (B2 .f .liftl.1 (B2 .f .trr.1 b0)) (B2 .f .liftr.1 b0)
      .trl.1 (refl (B2 .f .trr.1 b0))

def 𝕗Fib : isFibrant Fib ≔ [
| .trr.e ↦ X ↦ X
| .trl.e ↦ X ↦ X
| .liftr.e ↦ X ↦ refl X
| .liftl.e ↦ X ↦ refl X
| .id.e ↦ A B ↦ [
  | .trr.e ↦ C0 ↦ ?
  | .trl.e ↦ C1 ↦ ?
  | .liftr.e ↦ C0 ↦ ?
  | .liftl.e ↦ C1 ↦ ?
  | .id.e ↦ C0 C1 ↦ ?]]
 `}
