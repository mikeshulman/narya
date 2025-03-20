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

{` Quasi-inverses `}

{` A quasi-inverse pair is like an equivalence without any coherence `}
def qinv (A B : Fib) : Type ≔ sig (
  to : A .t → B .t,
  fro : B .t → A .t,
  to_fro : (b : B .t) → Id𝕗 B (to (fro b)) b .t,
  fro_to : (a : A .t) → Id𝕗 A (fro (to a)) a .t )

{` The identity map is a quasi-inverse `}
def qinv_id (A : Fib) : qinv A A ≔ (a ↦ a, a ↦ a, a ↦ refl a, a ↦ refl a)

{` Symmetry is a quasi-inverse `}
def sym_qinv (A00 A01 : Fib) (A02 : Id Fib A00 A01) (A10 A11 : Fib)
  (A12 : Id Fib A10 A11) (A20 : Id Fib A00 A10) (A21 : Id Fib A01 A11)
  (A22 : Id (Id Fib) A02 A12 A20 A21) (a00 : A00 .t) (a01 : A01 .t)
  (a02 : A02 .t a00 a01) (a10 : A10 .t) (a11 : A11 .t) (a12 : A12 .t a10 a11)
  (a20 : A20 .t a00 a10) (a21 : A21 .t a01 a11)
  : qinv (A22 .t a02 a12 a20 a21, A22 .f .id.1 a02 a12 .id.1 a20 a21)
      (sym A22 .t a20 a21 a02 a12, sym A22 .f .id.1 a20 a21 .id.1 a02 a12)
  ≔ (
  to ≔ a22 ↦ sym a22,
  fro ≔ a22 ↦ sym a22,
  to_fro ≔ a22 ↦ refl a22,
  fro_to ≔ a22 ↦ refl a22)

{` Quasi-inverses dependent over a pair of quasi-inverses `}
def qinv2 (A0 B0 : Fib) (e0 : qinv A0 B0) (A1 B1 : Fib) (e1 : qinv A1 B1)
  (A2 : A0 .t → A1 .t → Fib) (B2 : B0 .t → B1 .t → Fib)
  : Type
  ≔ sig (
  to : (a0 : A0 .t) (a1 : A1 .t) → A2 a0 a1 .t
       → B2 (e0 .to a0) (e1 .to a1) .t,
  fro : (b0 : B0 .t) (b1 : B1 .t) → B2 b0 b1 .t
        → A2 (e0 .fro b0) (e1 .fro b1) .t,
  to_fro : (b0 : B0 .t) (b1 : B1 .t) (b2 : B2 b0 b1 .t)
           → Id B2 (e0 .to_fro b0) (e1 .to_fro b1)
              .t (to (e0 .fro b0) (e1 .fro b1) (fro b0 b1 b2)) b2,
  fro_to : (a0 : A0 .t) (a1 : A1 .t) (a2 : A2 a0 a1 .t)
           → Id A2 (e0 .fro_to a0) (e1 .fro_to a1)
              .t (fro (e0 .to a0) (e1 .to a1) (to a0 a1 a2)) a2 )

{` We can get one of those from a fiberwise quasi-inverse `}
def qinv2_qinv (A0 A1 : Fib) (A2 B2 : A0 .t → A1 .t → Fib)
  (e : (a0 : A0 .t) (a1 : A1 .t) → qinv (A2 a0 a1) (B2 a0 a1))
  : qinv2 A0 A0 (qinv_id A0) A1 A1 (qinv_id A1) A2 B2
  ≔ (
  to ≔ a0 a1 a2 ↦ e a0 a1 .to a2,
  fro ≔ a0 a1 b2 ↦ e a0 a1 .fro b2,
  to_fro ≔ a0 a1 b2 ↦ e a0 a1 .to_fro b2,
  fro_to ≔ a0 a1 a2 ↦ e a0 a1 .fro_to a2)

{` 1-1 correspondences `}

{` A correspondence is 1-1 if it is unique in both directions. `}
def is11 (A B : Fib) (R : A .t → B .t → Fib) : Type ≔ sig (
  contrr : (a : A .t) → isContr (Σ𝕗 B (b ↦ R a b)),
  contrl : (b : B .t) → isContr (Σ𝕗 A (a ↦ R a b)) )

{` Being 1-1 transfers across dependent quasi-inverses `}
def is11_qinv2 (A0 B0 : Fib) (e0 : qinv A0 B0) (A1 B1 : Fib)
  (e1 : qinv A1 B1) (A2 : A0 .t → A1 .t → Fib) (B2 : B0 .t → B1 .t → Fib)
  (e2 : qinv2 A0 B0 e0 A1 B1 e1 A2 B2) (ae : is11 A0 A1 A2)
  : is11 B0 B1 B2
  ≔ (
  contrr ≔ b0 ↦
    let a0 : A0 .t ≔ e0 .fro b0 in
    let a11_a21 ≔ ae .contrr a0 .center in
    let a11 : A1 .t ≔ a11_a21 .fst in
    let a21 : A2 a0 a11 .t ≔ a11_a21 .snd in
    let b11 : B1 .t ≔ e1 .to a11 in
    let b21 : B2 (e0 .to a0) b11 .t ≔ e2 .to a0 a11 a21 in
    (center ≔ (b11, refl B2 (e0 .to_fro b0) (refl b11) .f .trr.1 b21),
     contract ≔ b10_b20 ↦
       let b10 : B1 .t ≔ b10_b20 .fst in
       let b20 : B2 b0 b10 .t ≔ b10_b20 .snd in
       let a10 : A1 .t ≔ e1 .fro b10 in
       let a20 : A2 a0 a10 .t ≔ e2 .fro b0 b10 b20 in
       let a12_a22 ≔ ae .contrr a0 .contract (a10, a20) in
       let a12 : Id A1 .t a10 a11 ≔ a12_a22 .fst in
       let a22 : Id A2 (refl a0) a12 .t a20 a21 ≔ a12_a22 .snd in
       (B1⁽ᵉᵉ⁾ .f .id.1 (e1 .to_fro b10) (refl b11) .trr.1 (refl e1 .to a12),
        B2⁽ᵉᵉ⁾ (sym (refl (e0 .to_fro b0)))
            (B1⁽ᵉᵉ⁾
             .f
             .id.1 (e1 .to_fro b10) (refl b11)
             .liftr.1 (refl e1 .to a12))
          .f
          .id.1 (e2 .to_fro b0 b10 b20)
            (refl B2 (e0 .to_fro b0) (refl b11) .f .liftr.1 b21)
          .trr.1 (refl e2 .to (refl a0) a12 a22))),
  contrl ≔ b1 ↦
    let a1 : A1 .t ≔ e1 .fro b1 in
    let a01_a21 ≔ ae .contrl a1 .center in
    let a01 : A0 .t ≔ a01_a21 .fst in
    let a21 : A2 a01 a1 .t ≔ a01_a21 .snd in
    let b01 : B0 .t ≔ e0 .to a01 in
    let b21 : B2 b01 (e1 .to a1) .t ≔ e2 .to a01 a1 a21 in
    (center ≔ (b01, refl B2 (refl b01) (e1 .to_fro b1) .f .trr.1 b21),
     contract ≔ b00_b20 ↦
       let b00 : B0 .t ≔ b00_b20 .fst in
       let b20 : B2 b00 b1 .t ≔ b00_b20 .snd in
       let a00 : A0 .t ≔ e0 .fro b00 in
       let a20 : A2 a00 a1 .t ≔ e2 .fro b00 b1 b20 in
       let a02_a22 ≔ ae .contrl a1 .contract (a00, a20) in
       let a02 : Id A0 .t a00 a01 ≔ a02_a22 .fst in
       let a22 : Id A2 a02 (refl a1) .t a20 a21 ≔ a02_a22 .snd in
       (B0⁽ᵉᵉ⁾ .f .id.1 (e0 .to_fro b00) (refl b01) .trr.1 (refl e0 .to a02),
        B2⁽ᵉᵉ⁾
            (B0⁽ᵉᵉ⁾
             .f
             .id.1 (e0 .to_fro b00) (refl b01)
             .liftr.1 (refl e0 .to a02)) (sym (refl (e1 .to_fro b1)))
          .f
          .id.1 (e2 .to_fro b00 b1 b20)
            (refl B2 (refl b01) (e1 .to_fro b1) .f .liftr.1 b21)
          .trr.1 (refl e2 .to a02 (refl a1) a22))))

{` And hence, in particular, across fiberwise quasi-inverses `}
def is11_qinv (A0 A1 : Fib) (A2 : A0 .t → A1 .t → Fib)
  (B2 : A0 .t → A1 .t → Fib)
  (e : (a0 : A0 .t) (a1 : A1 .t) → qinv (A2 a0 a1) (B2 a0 a1))
  (ae : is11 A0 A1 A2)
  : is11 A0 A1 B2
  ≔ is11_qinv2 A0 A0 (qinv_id A0) A1 A1 (qinv_id A1) A2 B2
      (qinv2_qinv A0 A1 A2 B2 e) ae

{` A 1-1 correspondence induces another one on identity types. `}
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

{` 1-1-ness also transports across Book HoTT equivalences. `}
def is11_eqv (A B : Fib) (R S : A .t → B .t → Fib)
  (e : (a : A .t) (b : B .t) → R a b .t ≅ S a b .t) (re : is11 A B R)
  : is11 A B S
  ≔ (
  contrr ≔ a ↦ (
    (re .contrr a .center .fst,
     e a (re .contrr a .center .fst) .to (re .contrr a .center .snd)),
    bs ↦ (
      re .contrr a .contract (bs .fst, e a (bs .fst) .fro (bs .snd)) .fst,
      eq.trr (S a (bs .fst) .t)
        (s ↦
         refl S (refl a)
             (re
              .contrr a
              .contract (bs .fst, e a (bs .fst) .fro (bs .snd))
              .fst)
         .t s
           (e a (re .contrr a .center .fst) .to (re .contrr a .center .snd)))
        (e a (bs .fst) .to (e a (bs .fst) .fro (bs .snd))) (bs .snd)
        (e a (bs .fst) .to_fro (bs .snd))
        (refl (e a)
             (re
              .contrr a
              .contract (bs .fst, e a (bs .fst) .fro (bs .snd))
              .fst)
         .to
           (re
            .contrr a
            .contract (bs .fst, e a (bs .fst) .fro (bs .snd))
            .snd)))),
  contrl ≔ b ↦ (
    (re .contrl b .center .fst,
     e (re .contrl b .center .fst) b .to (re .contrl b .center .snd)),
    as ↦ (
      re .contrl b .contract (as .fst, e (as .fst) b .fro (as .snd)) .fst,
      eq.trr (S (as .fst) b .t)
        (s ↦
         refl S
             (re
              .contrl b
              .contract (as .fst, e (as .fst) b .fro (as .snd))
              .fst) (refl b)
         .t s
           (e (re .contrl b .center .fst) b .to (re .contrl b .center .snd)))
        (e (as .fst) b .to (e (as .fst) b .fro (as .snd))) (as .snd)
        (e (as .fst) b .to_fro (as .snd))
        (refl e
             (re
              .contrl b
              .contract (as .fst, e (as .fst) b .fro (as .snd))
              .fst) (refl b)
         .to
           (re
            .contrl b
            .contract (as .fst, e (as .fst) b .fro (as .snd))
            .snd)))))
