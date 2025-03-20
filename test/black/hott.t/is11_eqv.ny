{` OLD `}

{` 1-1-ness transports across Book HoTT equivalences of correspondences. `}
def is11_eqv (A B : Fib) (R S : A .t → B .t → Fib)
  (e : (a : A .t) (b : B .t) → R a b .t ≅ S a b .t) (re : is11 A B R)
  : is11 A B S
  ≔ (
  contrr ≔ a ↦ (
    (re .contrr a .fst .fst,
     e a (re .contrr a .fst .fst) .to (re .contrr a .fst .snd)),
    bs ↦ (
      re .contrr a .snd (bs .fst, e a (bs .fst) .fro (bs .snd)) .fst,
      eq.trr (S a (bs .fst) .t)
        (s ↦
         refl S (refl a)
             (re .contrr a .snd (bs .fst, e a (bs .fst) .fro (bs .snd)) .fst)
         .t s (e a (re .contrr a .fst .fst) .to (re .contrr a .fst .snd)))
        (e a (bs .fst) .to (e a (bs .fst) .fro (bs .snd))) (bs .snd)
        (e a (bs .fst) .to_fro (bs .snd))
        (refl (e a)
             (re .contrr a .snd (bs .fst, e a (bs .fst) .fro (bs .snd)) .fst)
         .to (re .contrr a .snd (bs .fst, e a (bs .fst) .fro (bs .snd)) .snd)))),
  contrl ≔ b ↦ (
    (re .contrl b .fst .fst,
     e (re .contrl b .fst .fst) b .to (re .contrl b .fst .snd)),
    as ↦ (
      re .contrl b .snd (as .fst, e (as .fst) b .fro (as .snd)) .fst,
      eq.trr (S (as .fst) b .t)
        (s ↦
         refl S
             (re .contrl b .snd (as .fst, e (as .fst) b .fro (as .snd)) .fst)
             (refl b)
         .t s (e (re .contrl b .fst .fst) b .to (re .contrl b .fst .snd)))
        (e (as .fst) b .to (e (as .fst) b .fro (as .snd))) (as .snd)
        (e (as .fst) b .to_fro (as .snd))
        (refl e
             (re .contrl b .snd (as .fst, e (as .fst) b .fro (as .snd)) .fst)
             (refl b)
         .to (re .contrl b .snd (as .fst, e (as .fst) b .fro (as .snd)) .snd)))))
