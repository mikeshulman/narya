import "isfibrant"
import "fibrant_types"
import "bookhott"
import "hott_bookhott"

option function boundaries ≔ implicit
option type boundaries ≔ implicit

{` Fibrant Σ-types `}
def Σ𝕗 (A : Fib) (B : A .t → Fib) : Fib ≔ (
  t ≔ Σ (A .t) (a ↦ B a .t),
  f ≔ 𝕗Σ (A .t) (a ↦ B a .t) (A .f) (a ↦ B a .f))

{` Fibrant Π-types `}
def Π𝕗 (A : Fib) (B : A .t → Fib) : Fib ≔ (
  t ≔ (a : A .t) → B a .t,
  f ≔ 𝕗Π (A .t) (a ↦ B a .t) (A .f) (a ↦ B a .f))

{` Contractibility `}
def isContr (A : Fib) : Type ≔ sig (
  center : A .t,
  contract : (a : A .t) → Id (A .t) a center )

def iscontr_idfrom (A : Fib) (a0 : A .t) : isContr (Σ𝕗 A (a1 ↦ Id𝕗 A a0 a1))
  ≔ (
  center ≔ (a0, refl a0),
  contract ≔ a1_a2 ↦
    let a1 ≔ a1_a2 .fst in
    let a2 ≔ a1_a2 .snd in
    (refl ((z ↦ Id𝕗 A z a0) : A .t → Fib) a2 .f .trr.1 (refl a0),
     sym (refl ((z ↦ Id𝕗 A z a0) : A .t → Fib) a2 .f .liftr.1 (refl a0))))

def iscontr_idto (A : Fib) (a1 : A .t) : isContr (Σ𝕗 A (a0 ↦ Id𝕗 A a0 a1))
  ≔ (
  center ≔ (a1, refl a1),
  contract ≔ a0_a2 ↦
    let a0 ≔ a0_a2 .fst in
    let a2 ≔ a0_a2 .snd in
    (a2, conn A a0 a1 a2))

{` 1-1 correspondences `}

{` A correspondence is 1-1 if it is unique in both directions. `}
def is11 (A B : Fib) (R : A .t → B .t → Fib) : Type ≔ sig (
  contrr : (a : A .t) → isContr (Σ𝕗 B (b ↦ R a b)),
  contrl : (b : B .t) → isContr (Σ𝕗 A (a ↦ R a b)) )

{` A 1-1 correspondence induces another one on identity types.  This is where the real work of univalence lies. `}
def is11_Id (A0 A1 : Fib) (A2 : Id Fib A0 A1) (B0 B1 : Fib)
  (B2 : Id Fib B0 B1) (R0 : A0 .t → B0 .t → Fib) (re0 : is11 A0 B0 R0)
  (R1 : A1 .t → B1 .t → Fib) (re1 : is11 A1 B1 R1)
  (R2 : Id ((X Y ↦ (X .t → Y .t → Fib)) : (X Y : Fib) → Type) A2 B2 R0 R1)
  (re2 : refl is11 A2 B2 R2 re0 re1) (a0 : A0 .t) (a1 : A1 .t) (b0 : B0 .t)
  (b1 : B1 .t) (r0 : R0 a0 b0 .t) (r1 : R1 a1 b1 .t)
  : is11 (Idd𝕗 A0 A1 A2 a0 a1) (Idd𝕗 B0 B1 B2 b0 b1)
      (a2 b2 ↦ (R2 a2 b2 .t r0 r1, R2 a2 b2 .f .id.1 r0 r1))
  ≔ (
  contrr ≔ a2 ↦
    let S : (y0 : B0 .t) (y1 : B1 .t) → R0 a0 y0 .t → R1 a1 y1 .t → Fib
      ≔ y0 y1 z0 z1 ↦
        Σ𝕗 (Idd𝕗 B0 B1 B2 y0 y1)
          (y2 ↦ Idd𝕗 (R0 a0 y0) (R1 a1 y1) (R2 a2 y2) z0 z1) in
    let b0' : B0 .t ≔ re0 .contrr a0 .center .fst in
    let b1' : B1 .t ≔ re1 .contrr a1 .center .fst in
    let r0' : R0 a0 b0' .t ≔ re0 .contrr a0 .center .snd in
    let r1' : R1 a1 b1' .t ≔ re1 .contrr a1 .center .snd in
    let u : S b0' b1' r0' r1' .t ≔ (
      re2 .contrr a2 .center .fst,
      re2 .contrr a2 .center .snd) in
    let p0 : Id B0 .t b0 b0' ≔ re0 .contrr a0 .contract (b0, r0) .fst in
    let p1 : Id B1 .t b1 b1' ≔ re1 .contrr a1 .contract (b1, r1) .fst in
    let q0 : Id (R0 a0) p0 .t r0 r0'
      ≔ re0 .contrr a0 .contract (b0, r0) .snd in
    let q1 : Id (R1 a1) p1 .t r1 r1'
      ≔ re1 .contrr a1 .contract (b1, r1) .snd in
    (refl S p0 p1 q0 q1 .f .trl.1 u,
     v2 ↦
       let w
         ≔ re2 .contrr a2 .contract {(b0, r0)} {(b1, r1)} (v2 .fst, v2 .snd)
         in
       S⁽ᵉᵉ⁾ (sym (refl p0)) (sym (refl p1)) (sym (refl q0)) (sym (refl q1))
         .f
         .id.1 {v2} {u} (sym w .fst, sym w .snd)
           (refl S p0 p1 q0 q1 .f .liftl.1 u)
         .trl.1 (refl u)),
  contrl ≔ b2 ↦
    let S : (x0 : A0 .t) (x1 : A1 .t) → R0 x0 b0 .t → R1 x1 b1 .t → Fib
      ≔ x0 x1 z0 z1 ↦
        Σ𝕗 (Idd𝕗 A0 A1 A2 x0 x1)
          (x2 ↦ Idd𝕗 (R0 x0 b0) (R1 x1 b1) (R2 x2 b2) z0 z1) in
    let a0' : A0 .t ≔ re0 .contrl b0 .center .fst in
    let a1' : A1 .t ≔ re1 .contrl b1 .center .fst in
    let r0' : R0 a0' b0 .t ≔ re0 .contrl b0 .center .snd in
    let r1' : R1 a1' b1 .t ≔ re1 .contrl b1 .center .snd in
    let u : S a0' a1' r0' r1' .t ≔ (
      re2 .contrl b2 .center .fst,
      re2 .contrl b2 .center .snd) in
    let p0 : Id A0 .t a0 a0' ≔ re0 .contrl b0 .contract (a0, r0) .fst in
    let p1 : Id A1 .t a1 a1' ≔ re1 .contrl b1 .contract (a1, r1) .fst in
    let q0 : Id R0 p0 (refl b0) .t r0 r0'
      ≔ re0 .contrl b0 .contract (a0, r0) .snd in
    let q1 : Id R1 p1 (refl b1) .t r1 r1'
      ≔ re1 .contrl b1 .contract (a1, r1) .snd in
    (refl S p0 p1 q0 q1 .f .trl.1 u,
     v2 ↦
       let w
         ≔ re2 .contrl b2 .contract {(a0, r0)} {(a1, r1)} (v2 .fst, v2 .snd)
         in
       S⁽ᵉᵉ⁾ (sym (refl p0)) (sym (refl p1)) (sym (refl q0)) (sym (refl q1))
         .f
         .id.1 {v2} {u} (sym w .fst, sym w .snd)
           (refl S p0 p1 q0 q1 .f .liftl.1 u)
         .trl.1 (refl u)))

{` Bisimulations `}

{` A bisimulation between types is a bitotal relation that induces another bisimulation on identity types, higher-coinductively. `}
def isBisim (A B : Fib) (R : A .t → B .t → Fib) : Type ≔ codata [
| x .trr : A .t → B .t
| x .liftr : (a : A .t) → R a (x .trr a) .t
| x .trl : B .t → A .t
| x .liftl : (b : B .t) → R (x .trl b) b .t
| x .id.e
  : (a0 : A.0 .t) (b0 : B.0 .t) (r0 : R.0 a0 b0 .t) (a1 : A.1 .t)
    (b1 : B.1 .t) (r1 : R.1 a1 b1 .t)
    → isBisim (A.2 .t a0 a1, A.2 .f .id.1 a0 a1)
        (B.2 .t b0 b1, B.2 .f .id.1 b0 b1)
        (a2 b2 ↦ (R.2 a2 b2 .t r0 r1, R.2 a2 b2 .f .id.1 r0 r1)) ]

{` Any 1-1 correspondence is a bisimulation, because 1-1 correspondences lift to identity types. `}
def bisim_of_11 (A B : Fib) (R : A .t → B .t → Fib) (re : is11 A B R)
  : isBisim A B R
  ≔ [
| .trr ↦ a ↦ re .contrr a .center .fst
| .liftr ↦ a ↦ re .contrr a .center .snd
| .trl ↦ b ↦ re .contrl b .center .fst
| .liftl ↦ b ↦ re .contrl b .center .snd
| .id.e ↦ a0 b0 r0 a1 b1 r1 ↦
    bisim_of_11 (A.2 .t a0 a1, A.2 .f .id.1 a0 a1)
      (B.2 .t b0 b1, B.2 .f .id.1 b0 b1)
      (a2 b2 ↦ (R.2 a2 b2 .t r0 r1, R.2 a2 b2 .f .id.1 r0 r1))
      (is11_Id A.0 A.1 A.2 B.0 B.1 B.2 R.0 re.0 R.1 re.1 R.2 re.2 a0 a1 b0 b1
         r0 r1)]

{` Bisimulations transfer across Book HoTT equivalences. `}
def isbisim_eqv (A B : Fib) (R S : A .t → B .t → Fib)
  (e : (a : A .t) (b : B .t) → R a b .t ≅ S a b .t) (re : isBisim A B R)
  : isBisim A B S
  ≔ [
| .trr ↦ a ↦ re .trr a
| .liftr ↦ a ↦ e a (re .trr a) .to (re .liftr a)
| .trl ↦ b ↦ re .trl b
| .liftl ↦ b ↦ e (re .trl b) b .to (re .liftl b)
| .id.e ↦ a0 b0 s0 a1 b1 s1 ↦
    let r0 ≔ e.0 a0 b0 .fro s0 in
    let r1 ≔ e.1 a1 b1 .fro s1 in
    isbisim_eqv (A.2 .t a0 a1, A.2 .f .id.1 a0 a1)
      (B.2 .t b0 b1, B.2 .f .id.1 b0 b1)
      (a2 b2 ↦ (R.2 a2 b2 .t r0 r1, R.2 a2 b2 .f .id.1 r0 r1))
      (a2 b2 ↦ (S.2 a2 b2 .t s0 s1, S.2 a2 b2 .f .id.1 s0 s1))
      (a2 b2 ↦
       Id_eqv (R.0 a0 b0 .t) (R.1 a1 b1 .t) (R.2 a2 b2 .t) (S.0 a0 b0 .t)
         (S.1 a1 b1 .t) (S.2 a2 b2 .t) (e.0 a0 b0) (e.1 a1 b1) (e.2 a2 b2) s0
         s1) (re.2 .id.1 a0 b0 r0 a1 b1 r1)]
