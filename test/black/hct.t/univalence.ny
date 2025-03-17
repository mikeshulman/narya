import "isfibrant"
import "fibrant_types"

{`
option function boundaries ≔ implicit
option type boundaries ≔ implicit
 `}

{` Univalence `}

def is11 (A B : Type) (R : A → B → Type) : Type ≔ sig (
  trr : A → B,
  liftr : (a : A) → R a (trr a),
  utrr : (a : A) (b : B) (r : R a b) → Id B b (trr a),
  uliftr : (a : A) (b : B) (r : R a b) → Id (R a) (utrr a b r) r (liftr a),
  trl : B → A,
  liftl : (b : B) → R (trl b) b,
  utrl : (a : A) (b : B) (r : R a b) → Id A a (trl b),
  uliftl : (a : A) (b : B) (r : R a b)
           → Id ((x ↦ R x b) : A → Type) (utrl a b r) r (liftl b) )

def is11_eqv (A B : Type) (R S : A → B → Type)
  (e : (a : A) (b : B) → R a b ≅ S a b) (re : is11 A B R)
  : is11 A B S
  ≔ (
  trr ≔ re .trr,
  liftr ≔ a ↦ e a (re .trr a) .to (re .liftr a),
  utrr ≔ a b s ↦ re .utrr a b (e a b .fro s),
  uliftr ≔ a b s ↦
    eq.trr (S a b)
      (x ↦
       Id S (refl a) (re .utrr a b (e a b .fro s)) x
         (e a (re .trr a) .to (re .liftr a))) (e a b .to (e a b .fro s)) s
      (e a b .to_fro s)
      (refl (e a) (re .utrr a b (e a b .fro s))
       .to (re .uliftr a b (e a b .fro s))),
  trl ≔ re .trl,
  liftl ≔ b ↦ e (re .trl b) b .to (re .liftl b),
  utrl ≔ a b s ↦ re .utrl a b (e a b .fro s),
  uliftl ≔ a b s ↦
    eq.trr (S a b)
      (x ↦
       Id S (re .utrl a b (e a b .fro s)) (refl b) x
         (e (re .trl b) b .to (re .liftl b))) (e a b .to (e a b .fro s)) s
      (e a b .to_fro s)
      (refl e (re .utrl a b (e a b .fro s)) (refl b)
       .to (re .uliftl a b (e a b .fro s))))

def pre_univalence (A : Type) (𝕗A : isFibrant A) (B : Type)
  (𝕗B : isFibrant B) (R : Id Type A B)
  (𝕗R : (a : A) (b : B) → isFibrant (R a b)) (re : is11 A B (x y ↦ R x y))
  : Id isFibrant R 𝕗A 𝕗B
  ≔ [
{` Here we use bitotality of our 1-1 correspondence. `}
| .trr.1 ↦ re .trr
| .trl.1 ↦ re .trl
| .liftr.1 ↦ a ↦ re .liftr a
| .liftl.1 ↦ b ↦ re .liftl b
{` Here we just use the fact that it is itself a family of fibrant types. `}
| .id.1 ↦ a b ↦ 𝕗R a b
| .trr.e ↦ a0 b0 r0 ↦ 𝕗R.2 (𝕗A.2 .liftr.1 a0) (𝕗B.2 .liftr.1 b0) .trr.1 r0
| .trl.e ↦ a1 b1 r1 ↦ 𝕗R.2 (𝕗A.2 .liftl.1 a1) (𝕗B.2 .liftl.1 b1) .trl.1 r1
| .liftr.e ↦ a0 b0 r0 ↦
    sym (𝕗R.2 (𝕗A.2 .liftr.1 a0) (𝕗B.2 .liftr.1 b0) .liftr.1 r0)
| .liftl.e ↦ a1 b1 r1 ↦
    sym (𝕗R.2 (𝕗A.2 .liftl.1 a1) (𝕗B.2 .liftl.1 b1) .liftl.1 r1)
{` Here we recursively use the fact that a 1-1 correspondence induces a 1-1 correspondence on identity types. `}
| .id.e ↦ a0 b0 r0 a1 b1 r1 ↦
    pre_univalence (A.2 a0 a1) (𝕗A.2 .id.1 a0 a1) (B.2 b0 b1)
      (𝕗B.2 .id.1 b0 b1) (sym R.2 r0 r1)
      (a2 b2 ↦
       𝕗eqv (R.2 a2 b2 r0 r1) (sym R.2 r0 r1 a2 b2)
         (sym_eqv A.0 A.1 A.2 B.0 B.1 B.2 R.0 R.1 R.2 a0 a1 a2 b0 b1 b2 r0 r1)
         (𝕗R.2 a2 b2 .id.1 r0 r1)) ?]

def univalence (A B : Fib) (R : A .t → B .t → Fib)
  (re : is11 (A .t) (B .t) (x y ↦ R x y .t))
  : Id Fib A B
  ≔
  let Rt : A .t → B .t → Type ≔ x y ↦ R x y .t in
  (Gel (A .t) (B .t) Rt,
   pre_univalence (A .t) (A .f) (B .t) (B .f) (Gel (A .t) (B .t) Rt)
     (a b ↦
      𝕗eqv (R a b .t) (Gel (A .t) (B .t) Rt a b)
        (Gel_iso (A .t) (B .t) Rt a b) (R a b .f))
     (is11_eqv (A .t) (B .t) (x y ↦ R x y .t)
        (a b ↦ Gel (A .t) (B .t) (x y ↦ R x y .t) a b)
        (a b ↦ Gel_iso (A .t) (B .t) (x y ↦ R x y .t) a b) re))
