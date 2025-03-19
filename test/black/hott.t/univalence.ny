import "isfibrant"
import "bookhott"
import "hott_bookhott"
import "fibrant_types"
import "homotopy"

option function boundaries ≔ implicit
option type boundaries ≔ implicit

{` Univalence `}

{` We factor out the Gel bookkeeping and first prove a lemma assuming we already have something in "Id Type".  Something like this seems necessary for the coinductive hypothesis to be strong enough. `}
def pre_univalence (A : Fib) (B : Fib) (G : Id Type (A .t) (B .t))
  (𝕗G : (a : A .t) (b : B .t) → isFibrant (G a b))
  (re : is11 A B (x y ↦ (G x y, 𝕗G x y)))
  : Id isFibrant G (A .f) (B .f)
  ≔ [
{` The 0-dimensional methods are just transport and lifting. `}
| .trr.1 ↦ a ↦ re .contrr a .center .fst
| .trl.1 ↦ b ↦ re .contrl b .center .fst
| .liftr.1 ↦ a ↦ re .contrr a .center .snd
| .liftl.1 ↦ b ↦ re .contrl b .center .snd
{` This is just the assumption of pointwise fibrancy. `}
| .id.1 ↦ a b ↦ 𝕗G a b
{` The first few e-dimensional fields are also just pointwise fibrancy. `}
| .trr.e ↦ a0 b0 r0 ↦
    𝕗G.2 (A.2 .f .liftr.1 a0) (B.2 .f .liftr.1 b0) .trr.1 r0
| .trl.e ↦ a1 b1 r1 ↦
    𝕗G.2 (A.2 .f .liftl.1 a1) (B.2 .f .liftl.1 b1) .trl.1 r1
| .liftr.e ↦ a0 b0 r0 ↦
    sym (𝕗G.2 (A.2 .f .liftr.1 a0) (B.2 .f .liftr.1 b0) .liftr.1 r0)
| .liftl.e ↦ a1 b1 r1 ↦
    sym (𝕗G.2 (A.2 .f .liftl.1 a1) (B.2 .f .liftl.1 b1) .liftl.1 r1)
{` Here is the most interesting bit, where we coinductively use the fact that 1-1 correspondences lift to identity types. `}
| .id.e ↦ a0 b0 r0 a1 b1 r1 ↦
    let s
      : (a2 : A.2 .t a0 a1) (b2 : B.2 .t b0 b1)
        → G.2 a2 b2 r0 r1 ≅ sym G.2 r0 r1 a2 b2
      ≔ a2 b2 ↦
        sym_eqv (A.0 .t) (A.1 .t) (A.2 .t) (B.0 .t) (B.1 .t) (B.2 .t) G.0 G.1
          G.2 a0 a1 a2 b0 b1 b2 r0 r1 in
    let 𝕗sG
      : (a2 : A.2 .t a0 a1) (b2 : B.2 .t b0 b1)
        → isFibrant (sym G.2 r0 r1 a2 b2)
      ≔ a2 b2 ↦
        𝕗eqv (G.2 a2 b2 r0 r1) (sym G.2 r0 r1 a2 b2) (s a2 b2)
          (𝕗G.2 a2 b2 .id.1 r0 r1) in
    pre_univalence (Idd𝕗 A.0 A.1 A.2 a0 a1) (Idd𝕗 B.0 B.1 B.2 b0 b1)
      (sym G.2 r0 r1) 𝕗sG
      (is11_eqv (Idd𝕗 A.0 A.1 A.2 a0 a1) (Idd𝕗 B.0 B.1 B.2 b0 b1)
         (a2 b2 ↦ (G.2 a2 b2 r0 r1, 𝕗G.2 a2 b2 .id.1 r0 r1))
         (a2 b2 ↦ (sym G.2 r0 r1 a2 b2, 𝕗sG a2 b2)) s
         (is11_Id A.0 A.1 A.2 B.0 B.1 B.2 (a0 b0 ↦ (G.0 a0 b0, 𝕗G.0 a0 b0))
            re.0 (a1 b1 ↦ (G.1 a1 b1, 𝕗G.1 a1 b1)) re.1
            (a b ⤇ (G.2 a.2 b.2, 𝕗G.2 a.2 b.2)) re.2 a0 a1 b0 b1 r0 r1))]

{` Now we put this together with Gel to prove univalence for fibrant types, expressed relative to 1-1 correspondences. `}
def univalence_11 (A B : Fib) (R : A .t → B .t → Fib) (re : is11 A B R)
  : Id Fib A B
  ≔
  let Rt : A .t → B .t → Type ≔ x y ↦ R x y .t in
  let Rf : (a : A .t) (b : B .t) → isFibrant (Rt a b) ≔ x y ↦ R x y .f in
  (Gel (A .t) (B .t) Rt,
   pre_univalence A B (Gel (A .t) (B .t) Rt)
     (a b ↦
      𝕗eqv (R a b .t) (Gel (A .t) (B .t) Rt a b)
        (Gel_iso (A .t) (B .t) Rt a b) (R a b .f))
     (is11_eqv A B (x y ↦ R x y)
        (a b ↦ (Gel (A .t) (B .t) Rt a b, 𝕗Gel (A .t) (B .t) Rt Rf a b))
        (a b ↦ Gel_iso (A .t) (B .t) Rt a b) re))

{` Reflexivity of a type is a self-equivalence, but we don't have regularity, so its transports don't reduce to the identity.  However, with univalence we can build an alternative "strict reflexivity" that does. `}

def is11_Id𝕗 (A : Fib) : is11 A A (Id𝕗 A) ≔ (
  contrr ≔ iscontr_idfrom A,
  contrl ≔ iscontr_idto A)

def srefl (A : Fib) : Id Fib A A ≔ univalence_11 A A (Id𝕗 A) (is11_Id𝕗 A)

def srefl_is_strict (A : Fib) (a : A .t) : Id (A .t) (srefl A .f .trr.1 a) a
  ≔ refl a

{` More generally, given any Voevodsky equivalence we can easily make it into a 1-1 correspondence and hence an identification. `}

def univalence_vv (A B : Fib) (f : A .t → B .t)
  (fe : (b : B .t) → isContr (Σ𝕗 A (a ↦ Id𝕗 B (f a) b)))
  : Id Fib A B
  ≔ univalence_11 A B (a b ↦ Id𝕗 B (f a) b)
      (contrr ≔ a ↦ iscontr_idfrom B (f a), contrl ≔ fe)

{` This is "definitional univalence": we can extract both the function and its inverse definitionally. `}

def univalence_is_left_definitional (A B : Fib) (f : A .t → B .t)
  (fe : (b : B .t) → isContr (Σ𝕗 A (a ↦ Id𝕗 B (f a) b))) (a : A .t)
  : let E : Id Fib A B ≔ univalence_vv A B f fe in
    Id (B .t) (E .f .trr.1 a) (f a)
  ≔ refl (f a)

def univalence_is_right_definitional (A B : Fib) (f : A .t → B .t)
  (fe : (b : B .t) → isContr (Σ𝕗 A (a ↦ Id𝕗 B (f a) b))) (b : B .t)
  : let E : Id Fib A B ≔ univalence_vv A B f fe in
    Id (A .t) (E .f .trl.1 b) (fe b .center .fst)
  ≔ refl (fe b .center .fst)
