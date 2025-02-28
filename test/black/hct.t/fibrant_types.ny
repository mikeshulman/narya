import "isfibrant"

{` Since identity types compute only up to definitional isomorphism, in order to prove that anything is fibrant by corecursion, we need to be able to transport fibrancy across definitional isomorphisms.  In fact we can transport it across any Book-HoTT equivalence defined using the Martin-Lof identity type. `}

section eq ≔

def eq (A : Type) (a : A) : A → Type ≔ data [ rfl. : eq A a a ]

def cat (A : Type) (x y z : A) (u : eq A x y) (v : eq A y z)
  : eq A x z
  ≔ match v [ rfl. ↦ u ]

def cat3 (A : Type) (x y z w : A)
  (p : eq A x y) (q : eq A y z) (r : eq A z w)
  : eq A x w
  ≔ match q, r [ rfl., rfl. ↦ p ]

def idl (A : Type) (a0 a1 : A) (a2 : eq A a0 a1)
  : eq (eq A a0 a1) (cat A a0 a0 a1 rfl. a2) a2
  ≔ match a2 [ rfl. ↦ rfl. ]

def inv (A : Type) (a0 a1 : A) (a2 : eq A a0 a1)
  : eq A a1 a0
  ≔ match a2 [ rfl. ↦ rfl. ]

def ap (A B : Type) (f : A → B) (a0 a1 : A) (a2 : eq A a0 a1)
  : eq B (f a0) (f a1)
  ≔ match a2 [ rfl. ↦ rfl. ]

def ap_ap (A B C : Type) (f : A → B) (g : B → C)
  (a0 a1 : A) (a2 : eq A a0 a1)
  : eq (eq C (g (f a0)) (g (f a1)))
		   (ap B C g (f a0) (f a1) (ap A B f a0 a1 a2))
       (ap A C (x ↦ g (f x)) a0 a1 a2)
  ≔ match a2 [ rfl. ↦ rfl. ]

def trr (A:Type) (P:A→Type) (a0 a1 : A) (a2 : eq A a0 a1) (p : P a0) : P a1
  ≔ match a2 [ rfl. ↦ p ]

def trr_ap (A B : Type) (P : A → Type) (Q : B → Type)
  (f : A → B) (g : (x:A) → P x → Q (f x))
  (a0 a1 : A) (a2 : eq A a0 a1) (p : P a0)
  : eq (Q (f a1))
    (g a1 (trr A P a0 a1 a2 p))
    (trr B Q (f a0) (f a1) (ap A B f a0 a1 a2) (g a0 p))
  ≔ match a2 [ rfl. ↦ rfl. ]

def trr2 (A:Type) (B:Type) (P:A→B→Type)
  (a0 a1 : A) (a2 : eq A a0 a1) (b0 b1 : B) (b2 : eq B b0 b1)
  (p : P a0 b0) : P a1 b1
  ≔ match a2, b2 [ rfl., rfl. ↦ p ]

def trl2 (A:Type) (B:Type) (P:A→B→Type)
  (a0 a1 : A) (a2 : eq A a0 a1) (b0 b1 : B) (b2 : eq B b0 b1)
  (p : P a1 b1) : P a0 b0
  ≔ match a2, b2 [ rfl., rfl. ↦ p ]

def trr2_ap (A B : Type) (P : A → B → Type) (C D : Type) (Q : C → D → Type)
  (f : A → C) (g : B → D) (h : (x:A)(y:B) → P x y → Q (f x) (g y))
  (a0 a1 : A) (a2 : eq A a0 a1) (b0 b1 : B) (b2 : eq B b0 b1)
  (p : P a0 b0)
  : eq (Q (f a1) (g b1))
    (h a1 b1 (trr2 A B P a0 a1 a2 b0 b1 b2 p))
    (trr2 C D Q (f a0) (f a1) (ap A C f a0 a1 a2) (g b0) (g b1) (ap B D g b0 b1 b2) (h a0 b0 p))
  ≔ match a2, b2 [ rfl., rfl. ↦ rfl. ]

def whiskerR (A : Type) (a0 a1 a2 : A)
    (a01 a01' : eq A a0 a1) (a02 : eq (eq A a0 a1) a01 a01')
    (a12 : eq A a1 a2)
  : eq (eq A a0 a2) (cat A a0 a1 a2 a01 a12) (cat A a0 a1 a2 a01' a12)
  ≔ match a12 [ rfl. ↦ a02 ]

def unwhiskerR (A : Type) (a0 a1 a2 : A)
    (a01 a01' : eq A a0 a1)
    (a12 : eq A a1 a2)
    (a02 : eq (eq A a0 a2) (cat A a0 a1 a2 a01 a12) (cat A a0 a1 a2 a01' a12))
  : eq (eq A a0 a1) a01 a01'
  ≔ match a12 [ rfl. ↦ a02 ]

end

def eq ≔ eq.eq

section sq ≔

def sq (A : Type) (a00 : A)
  : (a01 : A) (a02 : eq A a00 a01) (a10 a11 : A) (a12 : eq A a10 a11)
    (a20 : eq A a00 a10) (a21 : eq A a01 a11) → Type ≔ data [
| rfl. : sq A a00 a00 rfl. a00 a00 rfl. rfl. rfl. ]

def hrfl (A : Type) (a0 a1 : A) (a2 : eq A a0 a1)
  : sq A a0 a0 rfl. a1 a1 rfl. a2 a2
  ≔ match a2 [ rfl. ↦ rfl. ]

def nat_toid (A : Type) (f : A → A) (p : (x:A) → eq A (f x) x)
  (a0 a1 : A) (a2 : eq A a0 a1)
  : sq A (f a0) (f a1) (eq.ap A A f a0 a1 a2) a0 a1 a2 (p a0) (p a1)
  ≔ match a2 [ rfl. ↦ hrfl A (f a0) a0 (p a0) ]

def ap (A B : Type) (f : A → B)
  (a00 a01 : A) (a02 : eq A a00 a01) (a10 a11 : A) (a12 : eq A a10 a11)
  (a20 : eq A a00 a10) (a21 : eq A a01 a11)
  (a22 : sq A a00 a01 a02 a10 a11 a12 a20 a21)
  : sq B (f a00) (f a01) (eq.ap A B f a00 a01 a02)
         (f a10) (f a11) (eq.ap A B f a10 a11 a12)
         (eq.ap A B f a00 a10 a20) (eq.ap A B f a01 a11 a21)
  ≔ match a22 [ rfl. ↦ rfl. ]

def act02 (A : Type)
  (a00 a01 : A) (a02 : eq A a00 a01) (a10 a11 : A) (a12 : eq A a10 a11)
  (a20 : eq A a00 a10) (a21 : eq A a01 a11)
  (a22 : sq A a00 a01 a02 a10 a11 a12 a20 a21)
  (a02' : eq A a00 a01) (p : eq (eq A a00 a01) a02 a02')
  : sq A a00 a01 a02' a10 a11 a12 a20 a21
  ≔ match p [ rfl. ↦ a22 ]

def act20 (A : Type)
  (a00 a01 : A) (a02 : eq A a00 a01) (a10 a11 : A) (a12 : eq A a10 a11)
  (a20 : eq A a00 a10) (a21 : eq A a01 a11)
  (a22 : sq A a00 a01 a02 a10 a11 a12 a20 a21)
  (a20' : eq A a00 a10) (p : eq (eq A a00 a10) a20 a20')
  : sq A a00 a01 a02 a10 a11 a12 a20' a21
  ≔ match p [ rfl. ↦ a22 ]

def to_cat (A : Type)
  (a00 a01 : A) (a02 : eq A a00 a01) (a10 a11 : A) (a12 : eq A a10 a11)
  (a20 : eq A a00 a10) (a21 : eq A a01 a11)
  (a22 : sq A a00 a01 a02 a10 a11 a12 a20 a21)
  : eq (eq A a00 a11)
       (eq.cat A a00 a01 a11 a02 a21) (eq.cat A a00 a10 a11 a20 a12)
  ≔ match a22 [ rfl. ↦ rfl. ]

def to_cat3 (A : Type)
  (a00 a01 : A) (a02 : eq A a00 a01) (a10 a11 : A) (a12 : eq A a10 a11)
  (a20 : eq A a00 a10) (a21 : eq A a01 a11)
  (a22 : sq A a00 a01 a02 a10 a11 a12 a20 a21)
  : eq (eq A a10 a11)
       a12
       (eq.cat3 A a10 a00 a01 a11 (eq.inv A a00 a10 a20) a02 a21)
  ≔ match a22 [ rfl. ↦ rfl. ]

def all_rfl_21 (A : Type) (a : A) (a2 : eq A a a)
  (a22 : sq A a a rfl. a a rfl. rfl. a2)
  : eq (eq A a a) a2 rfl.
  ≔ eq.cat (eq A a a) a2 (eq.cat A a a a rfl. a2) rfl.
      (eq.inv (eq A a a) (eq.cat A a a a rfl. a2) a2 (eq.idl A a a a2))
      (to_cat A a a rfl. a a rfl. rfl. a2 a22)

def unact21 (A : Type)
  (a00 a01 : A) (a02 : eq A a00 a01) (a10 a11 : A) (a12 : eq A a10 a11)
  (a20 : eq A a00 a10) (a21 : eq A a01 a11)
  (a22 : sq A a00 a01 a02 a10 a11 a12 a20 a21)
  (a21' : eq A a01 a11)
  (a22' : sq A a00 a01 a02 a10 a11 a12 a20 a21')
  : eq (eq A a01 a11) a21 a21'
  ≔ match a22 [ rfl. ↦
       eq.inv (eq A a00 a00) a21' rfl. (all_rfl_21 A a00 a21' a22') ]

def cancel_12_eq_21 (A : Type)
  (a00 a01 : A) (a02 : eq A a00 a01) (a11 : A) (a12 : eq A a01 a11)
  (a20 : eq A a00 a01)
  (a22 : sq A a00 a01 a02 a01 a11 a12 a20 a12)
  : eq (eq A a00 a01) a02 a20
  ≔ eq.unwhiskerR A a00 a01 a11 a02 a20 a12
      (to_cat A a00 a01 a02 a01 a11 a12 a20 a12 a22)

end

def sq ≔ sq.sq

def selfnat (A : Type) (f : A → A) (H : (x:A) → eq A (f x) x) (a : A)
  : eq (eq A (f (f a)) (f a)) (eq.ap A A f (f a) a (H a)) (H (f a))
  ≔ sq.cancel_12_eq_21 A (f (f a)) (f a) (eq.ap A A f (f a) a (H a))
       a (H a) (H (f a)) (sq.nat_toid A f H (f a) a (H a))

def eqv (A B : Type) : Type ≔ sig (
  to : A → B,
  fro : B → A,
  fro_to : (a:A) → eq A (fro (to a)) a,
  to_fro : (b:B) → eq B (to (fro b)) b,
  to_fro_to : (a:A) → eq (eq B (to (fro (to a))) (to a))
    (eq.ap A B to (fro (to a)) a (fro_to a))
    (to_fro (to a)),
)

notation 1 iso : A "≅" B ≔ eqv A B

def fro_to_fro (A B : Type) (e : A ≅ B) (y:B)
  : eq (eq A (e .fro (e .to (e .fro y))) (e .fro y))
       (eq.ap B A (e .fro) (e .to (e .fro y)) y (e .to_fro y))
       (e .fro_to (e .fro y)) ≔
  let f ≔ e .to in
  let g ≔ e .fro in
  let ap_f ≔ eq.ap A B f in
  let ap_g ≔ eq.ap B A g in
  let fg : B → B ≔ x ↦ e .to (e .fro x) in
  let ap_fg ≔ eq.ap B B fg in
  let gf : A → A ≔ x ↦ e .fro (e .to x) in
  let ap_gf ≔ eq.ap A A gf in
  let gfg : B → A ≔ x ↦ e .fro (e .to (e .fro x)) in
  let ap_gfg ≔ eq.ap B A gfg in
  let fgfg : B → B ≔ x ↦ e .to (e .fro (e .to (e .fro x))) in
  let gfgfg : B → A ≔ x ↦ e .fro (e .to (e .fro (e .to (e .fro x)))) in
  let η ≔ e .fro_to in
  let ε ≔ e .to_fro in
  sq.unact21 A (gfgfg y) (gfg y)
    (eq.ap A A gf (gfg y) (g y) (ap_g (fg y) y (ε y)))
    (gfg y) (g y) (ap_g (fg y) y (ε y))
    (η (gfg y)) (ap_g (fg y) y (ε y))
    (sq.act20 A (gfgfg y) (gfg y)
      (eq.ap A A gf (gfg y) (g y) (ap_g (fg y) y (ε y)))
      (gfg y) (g y) (ap_g (fg y) y (ε y))
      (ap_g (fgfg y) (fg y) (ε (fg y)))
      (ap_g (fg y) y (ε y))
      (sq.act02 A (gfgfg y) (gfg y)
        (ap_g (fgfg y) (fg y) (ap_fg (fg y) y (ε y)))
        (gfg y) (g y) (ap_g (fg y) y (ε y))
        (ap_g (fgfg y) (fg y) (ε (fg y)))
        (ap_g (fg y) y (ε y))
        (sq.ap B A g (fgfg y) (fg y) (ap_fg (fg y) y (ε y))
          (fg y) y (ε y) (ε (fg y)) (ε y)
          (sq.nat_toid B fg ε (fg y) y (ε y)))
        (ap_gf (gfg y) (g y) (ap_g (fg y) y (ε y)))
        (eq.cat (eq A (gfgfg y) (gfg y))
          (ap_g (fgfg y) (fg y) (ap_fg (fg y) y (ε y)))
          (ap_gfg (fg y) y (ε y))
          (ap_gf (gfg y) (g y) (ap_g (fg y) y (ε y)))
          (eq.ap_ap B B A fg g (fg y) y (ε y))
          (eq.inv (eq A (gfgfg y) (gfg y))
            (ap_gf (gfg y) (g y) (ap_g (fg y) y (ε y)))
            (ap_gfg (fg y) y (ε y))
            (eq.ap_ap B A A g gf (fg y) y (ε y)))))
      (η (gfg y))
      (eq.cat3 (eq A (gfgfg y) (gfg y))
        (ap_g (fgfg y) (fg y) (ε (fg y)))
        (ap_g (fgfg y) (fg y) (ap_f (gfg y) (g y) (η (g y))))
        (eq.ap A A gf (gfg y) (g y) (η (g y)))
        (η (gfg y))
        (eq.inv
          (eq A (gfgfg y) (gfg y))
          (ap_g (fgfg y) (fg y) (ap_f (gfg y) (g y) (η (g y))))
          (ap_g (fgfg y) (fg y) (ε (fg y)))
          (eq.ap (eq B (fgfg y) (fg y)) (eq A (gfgfg y) (gfg y))
            (ap_g (fgfg y) (fg y))
            (ap_f (gfg y) (g y) (η (g y)))
            (ε (fg y))
            (e .to_fro_to (g y))))
        (eq.ap_ap A B A f g (gfg y) (g y) (η (g y)))
        (selfnat A gf η (g y))))
    (η (g y))
    (sq.nat_toid A gf η (gfg y) (g y) (ap_g (fg y) y (ε y)))

def adjointify (A B : Type) (f : A → B) (g : B → A)
  (η : (a:A) → eq A (g (f a)) a)
  (ε : (b:B) → eq B (f (g b)) b)
  : A ≅ B ≔
  let ap_f ≔ eq.ap A B f in
  let ap_g ≔ eq.ap B A g in
  let fg : B → B ≔ x ↦ f (g x) in
  let ap_fg ≔ eq.ap B B fg in
  let gf : A → A ≔ x ↦ g (f x) in
  let ap_gf ≔ eq.ap A A gf in
  let fgf : A → B ≔ x ↦ f (g (f x)) in
  let ap_fgf ≔ eq.ap A B fgf in
  let gfg : B → A ≔ x ↦ g (f (g x)) in
  let ap_gfg ≔ eq.ap B A gfg in
  let gfgf : A → A ≔ x ↦ g (f (g (f x))) in
  let fgfg : B → B ≔ x ↦ f (g (f (g x))) in
  let fgfgf : A → B ≔ x ↦ f (g (f (g (f x)))) in
  let gfgfg : B → A ≔ x ↦ g (f (g (f (g x)))) in
  (
to ≔ f,
fro ≔ g,
fro_to ≔ η,
to_fro ≔ b ↦
  eq.cat3 B (fg b) (fgfg b) (fg b) b
    (eq.inv B (fgfg b) (fg b) (ε (fg b)))
    (ap_f (gfg b) (g b) (η (g b)))
    (ε b),
to_fro_to ≔ a ↦
  sq.to_cat3 B
    (fgfgf a) (fgf a) (ap_f (gfgf a) (gf a) (η (gf a)))
    (fgf a) (f a) (ap_f (gf a) a (η a)) (ε (fgf a)) (ε (f a))
    (sq.act02 B
      (fgfgf a) (fgf a) (ap_fg (fgf a) (f a) (ap_f (gf a) a (η a)))
      (fgf a) (f a) (ap_f (gf a) a (η a)) (ε (fgf a)) (ε (f a))
      (sq.nat_toid B fg ε (fgf a) (f a) (ap_f (gf a) a (η a)))
      (ap_f (gfgf a) (gf a) (η (gf a)))
      (eq.cat3 (eq B (fgfgf a) (fgf a))
        (ap_fg (fgf a) (f a) (ap_f (gf a) a (η a)))
        (ap_fgf (gf a) a (η a))
        (ap_f (gfgf a) (gf a) (ap_gf (gf a) a (η a)))
        (ap_f (gfgf a) (gf a) (η (gf a)))
        (eq.ap_ap A B B f fg (gf a) a (η a))
        (eq.inv (eq B (fgfgf a) (fgf a))
          (ap_f (gfgf a) (gf a) (ap_gf (gf a) a (η a)))
          (ap_fgf (gf a) a (η a))
          (eq.ap_ap A A B gf f (gf a) a (η a)))
        (eq.ap (eq A (gfgf a) (gf a)) (eq B (fgfgf a) (fgf a))
          (ap_f (gfgf a) (gf a)) (ap_gf (gf a) a (η a)) (η (gf a))
          (selfnat A gf η a)) )))

{` An Id of equalities induces an equality involving transport `}
def Id_eq
  (A0 A1 : Type) (A2 : Id Type A0 A1)
  (a00 : A0) (a01 : A1) (a02 : A2 a00 a01)
  (a10 : A0) (a11 : A1) (a12 : A2 a10 a11)
  (a20 : eq A0 a00 a10) (a21 : eq A1 a01 a11)
  (a22 : Id eq A0 A1 A2 a00 a01 a02 a10 a11 a12 a20 a21)
  : eq (A2 a10 a11)
       (eq.trr2 A0 A1 (x y ↦ A2 x y) a00 a10 a20 a01 a11 a21 a02)
       a12
  ≔ match a22 [ rfl. ↦ rfl. ]

{` An Id of equivalences induces an equivalence on Ids. `}
def eqvId (A0 : Type) (A1 : Type) (A2 : Id Type A0 A1)
          (B0 : Type) (B1 : Type) (B2 : Id Type B0 B1)
          (e0 : A0 ≅ B0) (e1 : A1 ≅ B1)
          (e2 : Id eqv A0 A1 A2 B0 B1 B2 e0 e1)
          (b0 : B0) (b1 : B1)
  : A2 (e0 .fro b0) (e1 .fro b1) ≅ B2 b0 b1 ≔
  let f0 ≔ e0 .to in
  let g0 ≔ e0 .fro in
  let ap_g0 ≔ eq.ap B0 A0 g0 in
  let fg0 : B0 → B0 ≔ x ↦ f0 (g0 x) in
  let gfg0 : B0 → A0 ≔ x ↦ g0 (f0 (g0 x)) in
  let ε0 ≔ e0 .to_fro in
  let η0 ≔ e0 .fro_to in
  let f1 ≔ e1 .to in
  let g1 ≔ e1 .fro in
  let ap_g1 ≔ eq.ap B1 A1 g1 in
  let fg1 : B1 → B1 ≔ x ↦ f1 (g1 x) in
  let gfg1 : B1 → A1 ≔ x ↦ g1 (f1 (g1 x)) in
  let ε1 ≔ e1 .to_fro in
  let η1 ≔ e1 .fro_to in
  let f2 ≔ e2 .to in
  let g2 ≔ e2 .fro in
  let η2 ≔ e2 .fro_to in
  let ε2 ≔ e2 .to_fro in
  adjointify (A2 (g0 b0) (g1 b1)) (B2 b0 b1)
  (a2 ↦ eq.trr2 B0 B1 (b0 b1 ↦ B2 b0 b1)
           (fg0 b0) b0 (ε0 b0) (fg1 b1) b1 (ε1 b1)
           (f2 (g0 b0) (g1 b1) a2))
  (b2 ↦ g2 b0 b1 b2)
  (a2 ↦ eq.cat (A2 (g0 b0) (g1 b1))
    (g2 b0 b1 (eq.trr2 B0 B1 (x y ↦ B2 x y) (fg0 b0) b0
                (ε0 b0) (fg1 b1) b1 (ε1 b1)
                (f2 (g0 b0) (g1 b1) a2)))
    (eq.trr2 A0 A1 (x y ↦ A2 x y)
      (gfg0 b0) (g0 b0) (ap_g0 (fg0 b0) b0 (ε0 b0))
      (gfg1 b1) (g1 b1) (ap_g1 (fg1 b1) b1 (ε1 b1))
      (g2 (fg0 b0) (fg1 b1) (f2 (g0 b0) (g1 b1) a2)))
    a2
    (eq.trr2_ap B0 B1 (x y ↦ B2 x y) A0 A1 (x y ↦ A2 x y)
      g0 g1 (x0 x1 x2 ↦ g2 x0 x1 x2)
      (fg0 b0) b0 (ε0 b0) (fg1 b1) b1 (ε1 b1)
      (f2 (g0 b0) (g1 b1) a2))
    (Id_eq A0 A1 A2
      (gfg0 b0) (gfg1 b1) (g2 (fg0 b0) (fg1 b1) (f2 (g0 b0) (g1 b1) a2))
      (g0 b0) (g1 b1) a2
      (ap_g0 (fg0 b0) b0 (ε0 b0)) (ap_g1 (fg1 b1) b1 (ε1 b1))
      (eq.trl2 (eq A0 (gfg0 b0) (g0 b0)) (eq A1 (gfg1 b1) (g1 b1))
        (u v ↦ Id eq A0 A1 A2 (gfg0 b0) (gfg1 b1)
                  (g2 (fg0 b0) (fg1 b1) (f2 (g0 b0) (g1 b1) a2))
                  (g0 b0) (g1 b1) a2 u v)
        (ap_g0 (fg0 b0) b0 (ε0 b0)) (η0 (g0 b0)) (fro_to_fro A0 B0 e0 b0)
        (ap_g1 (fg1 b1) b1 (ε1 b1)) (η1 (g1 b1)) (fro_to_fro A1 B1 e1 b1)
        (η2 (g0 b0) (g1 b1) a2))))
  (b2 ↦ Id_eq B0 B1 B2
           (fg0 b0) (fg1 b1) (f2 (g0 b0) (g1 b1) (g2 b0 b1 b2))
           b0 b1 b2 (ε0 b0) (ε1 b1)
           (ε2 b0 b1 b2))


{` Fibrancy transports across equivalences. `}
def 𝕗iso (A B : Type) (e : A ≅ B) (𝕗A : isFibrant A) : isFibrant B ≔ [
| .trr.e ↦ b0 ↦ e.1 .to (𝕗A.2 .trr.1 (e.0 .fro b0))
| .trl.e ↦ b1 ↦ e.0 .to (𝕗A.2 .trl.1 (e.1 .fro b1))
| .liftr.e ↦ b0 ↦
  eq.trr B.0 (b ↦ B.2 b (e.1 .to (𝕗A.2 .trr.1 (e.0 .fro b0))))
       (e.0 .to (e.0 .fro b0)) b0 (e.0 .to_fro b0)
       (e.2 .to (e.0 .fro b0) (𝕗A.2 .trr.1 (e.0 .fro b0))
                (𝕗A.2 .liftr.1 (e.0 .fro b0)))
| .liftl.e ↦ b1 ↦ 
	eq.trr B.1 (b ↦ B.2 (e.0 .to (𝕗A.2 .trl.1 (e.1 .fro b1))) b)
       (e.1 .to (e.1 .fro b1)) b1 (e.1 .to_fro b1)
       (e.2 .to (𝕗A.2 .trl.1 (e.1 .fro b1)) (e.1 .fro b1)
                (𝕗A.2 .liftl.1 (e.1 .fro b1)))
| .id.e ↦ b0 b1 ↦
  𝕗iso (A.2 (e.0 .fro b0) (e.1 .fro b1)) (B.2 b0 b1)
       (eqvId A.0 A.1 A.2 B.0 B.1 B.2 e.0 e.1 e.2 b0 b1)
       (𝕗A.2 .id.1 (e.0 .fro b0) (e.1 .fro b1)) ]

option function boundaries ≔ implicit
option type boundaries ≔ implicit

{` The unit type `}

def ⊤ : Type ≔ sig ()

def id_⊤_iso (x y : ⊤) : ⊤ ≅ Id ⊤ x y ≔ (
to ≔ _ ↦ (),
fro ≔ _ ↦ (),
to_fro ≔ _ ↦ rfl.,
fro_to ≔ _ ↦ rfl.,
to_fro_to ≔ _ ↦ rfl.,
)

def 𝕗⊤ : isFibrant ⊤ ≔ [
| .trr.e ↦ x ↦ x
| .trl.e ↦ x ↦ x
| .liftr.e ↦ _ ↦ ()
| .liftl.e ↦ _ ↦ ()
| .id.e ↦ x y ↦ 𝕗iso ⊤ (Id ⊤ x y) (id_⊤_iso x y) 𝕗⊤ ]

{` Product types `}

def prod (A B : Type) : Type ≔ sig (fst : A, snd : B)

notation 2 prod : A "×" B ≔ prod A B

def id_prod_iso
  (A0 : Type) (A1 : Type) (A2 : Id Type A0 A1)
  (B0 : Type) (B1 : Type) (B2 : Id Type B0 B1)
  (a0 : A0) (a1 : A1) (b0 : B0) (b1 : B1)
  : A2 a0 a1 × B2 b0 b1 ≅ Id prod A2 B2 (a0,b0) (a1,b1) ≔ (
to ≔ u ↦ (u .fst, u .snd),
fro ≔ v ↦ (v .fst, v .snd),
to_fro ≔ _ ↦ rfl.,
fro_to ≔ _ ↦ rfl.,
to_fro_to ≔ _ ↦ rfl. )

def 𝕗prod (A B : Type) (𝕗A : isFibrant A) (𝕗B : isFibrant B)
  : isFibrant (A × B) ≔ [
| .trr.e ↦ u0 ↦ (𝕗A.2 .trr.1 (u0 .fst), 𝕗B.2 .trr.1 (u0 .snd))
| .trl.e ↦ u1 ↦ (𝕗A.2 .trl.1 (u1 .fst), 𝕗B.2 .trl.1 (u1 .snd))
| .liftr.e ↦ u0 ↦ (𝕗A.2 .liftr.1 (u0 .fst), 𝕗B.2 .liftr.1 (u0 .snd))
| .liftl.e ↦ u1 ↦ (𝕗A.2 .liftl.1 (u1 .fst), 𝕗B.2 .liftl.1 (u1 .snd))
| .id.e ↦ u0 u1 ↦
  𝕗iso (A.2 (u0 .fst) (u1 .fst) × B.2 (u0 .snd) (u1 .snd))
      (refl prod A.2 B.2 u0 u1)
      (id_prod_iso A.0 A.1 A.2 B.0 B.1 B.2
                   (u0 .fst) (u1 .fst) (u0 .snd) (u1 .snd))
      (𝕗prod (A.2 (u0 .fst) (u1 .fst)) (B.2 (u0 .snd) (u1 .snd))
         (𝕗A.2 .id.1 (u0 .fst) (u1 .fst)) (𝕗B.2 .id.1 (u0 .snd) (u1 .snd))) ]

{` Σ-types `}

def Σ (A : Type) (B : A → Type) : Type ≔ sig (fst : A, snd : B fst)

def id_Σ_iso
  (A0 : Type) (A1 : Type) (A2 : Id Type A0 A1)
  (B0 : A0 → Type) (B1 : A1 → Type)
  (B2 : Id Π A2 {_ ↦ Type} {_ ↦ Type} (_ ⤇ refl Type) B0 B1)
  (a0 : A0) (a1 : A1) (b0 : B0 a0) (b1 : B1 a1)
  : Σ (A2 a0 a1) (a2 ↦ B2 a2 b0 b1)
    ≅ Id Σ A2 B2 (a0,b0) (a1,b1) ≔ (
to ≔ u ↦ (u .fst, u .snd),
fro ≔ v ↦ (v .fst, v .snd),
to_fro ≔ _ ↦ rfl.,
fro_to ≔ _ ↦ rfl.,
to_fro_to ≔ _ ↦ rfl. )

def 𝕗Σ (A : Type) (B : A → Type)
  (𝕗A : isFibrant A) (𝕗B : (x:A) → isFibrant (B x))
  : isFibrant (Σ A B) ≔ [
| .trr.e ↦ u0 ↦
  (𝕗A.2 .trr.1 (u0 .fst),
   𝕗B.2 (𝕗A.2 .liftr.1 (u0 .fst)) .trr.1 (u0 .snd))
| .trl.e ↦ u1 ↦
  (𝕗A.2 .trl.1 (u1 .fst),
   𝕗B.2 (𝕗A.2 .liftl.1 (u1 .fst)) .trl.1 (u1 .snd))
| .liftr.e ↦ u0 ↦
  (𝕗A.2 .liftr.1 (u0 .fst),
   𝕗B.2 (𝕗A.2 .liftr.1 (u0 .fst)) .liftr.1 (u0 .snd))
| .liftl.e ↦ u1 ↦
  (𝕗A.2 .liftl.1 (u1 .fst),
   𝕗B.2 (𝕗A.2 .liftl.1 (u1 .fst)) .liftl.1 (u1 .snd))
| .id.e ↦ u0 u1 ↦
  𝕗iso (Σ (A.2 (u0 .fst) (u1 .fst))
         (a2 ↦ B.2 a2 (u0 .snd) (u1 .snd)))
       (Id Σ A.2 B.2 u0 u1)
       (id_Σ_iso A.0 A.1 A.2 B.0 B.1 B.2
                 (u0 .fst) (u1 .fst) (u0 .snd) (u1 .snd))
       (𝕗Σ (A.2 (u0 .fst) (u1 .fst))
           (a2 ↦ B.2 a2 (u0 .snd) (u1 .snd))
           (𝕗A.2 .id.1 (u0 .fst) (u1 .fst))
           (a2 ↦ 𝕗B.2 a2 .id.1 (u0 .snd) (u1 .snd)))
]

{` Π-types `}

def id_Π_iso
  (A0 : Type) (A1 : Type) (A2 : Id Type A0 A1)
  (B0 : A0 → Type) (B1 : A1 → Type)
  (B2 : Id Π A2 {_ ↦ Type} {_ ↦ Type} (_ ⤇ refl Type) B0 B1)
  (f0 : (a0 : A0) → B0 a0) (f1 : (a1 : A1) → B1 a1)
  : ((a0 : A0) (a1 : A1) (a2 : A2 a0 a1) → B2 a2 (f0 a0) (f1 a1))
    ≅ Id Π A2 B2 f0 f1 ≔ (
to ≔ f ↦ a ⤇ f a.0 a.1 a.2,
fro ≔ g ↦ a0 a1 a2 ↦ g a2,
to_fro ≔ _ ↦ rfl.,
fro_to ≔ _ ↦ rfl.,
to_fro_to ≔ _ ↦ rfl. )

def 𝕗Π (A : Type) (B : A → Type)
  (𝕗A : isFibrant A) (𝕗B : (x:A) → isFibrant (B x))
  : isFibrant ((x:A) → B x)
  ≔ [
| .trr.e ↦ f0 a1 ↦
  𝕗B.2 (𝕗A.2 .liftl.1 a1) .trr.1 (f0 (𝕗A.2 .trl.1 a1))
| .trl.e ↦ f1 a0 ↦
  𝕗B.2 (𝕗A.2 .liftr.1 a0) .trl.1 (f1 (𝕗A.2 .trr.1 a0))
| .liftr.e ↦ f0 a0 a1 a2 ↦ ?
| .liftl.e ↦ f1 a0 a1 a2 ↦ ?
| .id.e ↦ f0 f1 ↦
  𝕗iso ((a0 : A.0) (a1 : A.1) (a2 : A.2 a0 a1) → B.2 a2 (f0 a0) (f1 a1))
    (Id Π A.2 B.2 f0 f1)
    (id_Π_iso A.0 A.1 A.2 B.0 B.1 B.2 f0 f1)
    (𝕗Π A.0 (a0 ↦ (a1:A.1)(a2:A.2 a0 a1)→B.2 a2 (f0 a0) (f1 a1)) 𝕗A.0
     (a0 ↦ 𝕗Π A.1 (a1 ↦ (a2:A.2 a0 a1)→B.2 a2 (f0 a0) (f1 a1)) 𝕗A.1
 		  (a1 ↦ 𝕗Π (A.2 a0 a1) (a2 ↦ B.2 a2 (f0 a0) (f1 a1))
                (𝕗A.2 .id.1 a0 a1)
       (a2 ↦ 𝕗B.2 a2 .id.1 (f0 a0) (f1 a1))))) ]

{` Empty type `}

def ∅ : Type ≔ data [ ]

def 𝕗∅ : isFibrant ∅ ≔ [
| .trr.e ↦ []
| .trl.e ↦ []
| .liftr.e ↦ []
| .liftl.e ↦ []
| .id.e ↦ [] ]

{` Sum type `}

def sum (A B : Type) : Type ≔ data [ left. (_:A) | right. (_:B) ]

notation 1.5 sum : A "⊔" B ≔ sum A B

def sum_code (A0 A1 : Type) (A2 : Id Type A0 A1)
  (B0 B1 : Type) (B2 : Id Type B0 B1)
  (u0 : A0 ⊔ B0) (u1 : A1 ⊔ B1)
  : Type ≔ match u0, u1 [
| left. a0, left. a1 ↦ A2 a0 a1
| left. a0, right. b1 ↦ ∅
| right. b0, left. a1 ↦ ∅
| right. b0, right. b1 ↦ B2 b0 b1 ]

def id_sum_iso  (A0 A1 : Type) (A2 : Id Type A0 A1)
  (B0 B1 : Type) (B2 : Id Type B0 B1)
  (u0 : A0 ⊔ B0) (u1 : A1 ⊔ B1)
  : sum_code A0 A1 A2 B0 B1 B2 u0 u1 ≅ Id sum A2 B2 u0 u1 ≔ (
to ≔ v2 ↦ match u0, u1 [
  | left. a0, left. a1 ↦ left. v2
  | left. a0, right. b1 ↦ match v2 []
  | right. b0, left. a1 ↦ match v2 []
  | right. b0, right. b1 ↦ right. v2 ],
fro ≔ [
  | left. a2 ↦ a2
  | right. b2 ↦ b2 ],
to_fro ≔ [
  | left. a2 ↦ rfl.
  | right. b2 ↦ rfl. ],
fro_to ≔ v2 ↦ match u0, u1 [
  | left. a0, left. a1 ↦ rfl.
  | left. a0, right. b1 ↦ match v2 []
  | right. b0, left. a1 ↦ match v2 []
  | right. b0, right. b1 ↦ rfl. ],
to_fro_to ≔ v2 ↦ match u0, u1 [
  | left. a0, left. a1 ↦ rfl.
  | left. a0, right. b1 ↦ match v2 []
  | right. b0, left. a1 ↦ match v2 []
  | right. b0, right. b1 ↦ rfl. ],
)

def 𝕗sum (A B : Type) (𝕗A : isFibrant A) (𝕗B : isFibrant B)
  : isFibrant (A ⊔ B) ≔ [
| .trr.e ↦ [
  | left. a0 ↦ left. (𝕗A.2 .trr.1 a0)
  | right. b0 ↦ right. (𝕗B.2 .trr.1 b0) ]
| .trl.e ↦ [
  | left. a1 ↦ left. (𝕗A.2 .trl.1 a1)
  | right. b1 ↦ right. (𝕗B.2 .trl.1 b1) ]
| .liftr.e ↦ [
  | left. a0 ↦ left. (𝕗A.2 .liftr.1 a0)
  | right. b0 ↦ right. (𝕗B.2 .liftr.1 b0) ]
| .liftl.e ↦ [
  | left. a1 ↦ left. (𝕗A.2 .liftl.1 a1)
  | right. b1 ↦ right. (𝕗B.2 .liftl.1 b1) ]
| .id.e ↦ u0 u1 ↦ (𝕗iso
    (sum_code A.0 A.1 A.2 B.0 B.1 B.2 u0 u1)
    (Id sum A.2 B.2 u0 u1)
    (id_sum_iso A.0 A.1 A.2 B.0 B.1 B.2 u0 u1)
    (match u0, u1 [
     | left. a0, left. a1 ↦ 𝕗A.2 .id.1 a0 a1
     | left. _, right. _ ↦ 𝕗∅
     | right. _, left. _ ↦ 𝕗∅
     | right. b0, right. b1 ↦ 𝕗B.2 .id.1 b0 b1 ] )) ]

{` The natural numbers `}

def ℕ : Type ≔ data [ zero. | suc. (_:ℕ) ]

def ℕ_code (m n : ℕ) : Type ≔ match m, n [
| zero., zero. ↦ ⊤
| zero., suc. _ ↦ ∅
| suc. _, zero. ↦ ∅
| suc. m, suc. n ↦ ℕ_code m n ]

def id_ℕ_iso (n0 n1 : ℕ) : ℕ_code n0 n1 ≅ Id ℕ n0 n1
  ≔ adjointify (ℕ_code n0 n1) (Id ℕ n0 n1)
  (m2 ↦ match n0, n1 [
  | zero., zero. ↦ zero.
  | zero., suc. n1 ↦ match m2 []
  | suc. n0, zero. ↦ match m2 []
  | suc. n0, suc. n1 ↦ suc. (id_ℕ_iso n0 n1 .to m2) ])
  ([
  | zero. ↦ ()
  | suc. m2 ↦ id_ℕ_iso m2.0 m2.1 .fro m2.2 ])
  (m2 ↦ match n0, n1 [
  | zero., zero. ↦ rfl.
  | zero., suc. n1 ↦ match m2 []
  | suc. n0, zero. ↦ match m2 []
  | suc. n0, suc. n1 ↦ id_ℕ_iso n0 n1 .fro_to m2 ])
  ([
  | zero. ↦ rfl.
  | suc. m2 ↦
      eq.ap (Id ℕ m2.0 m2.1) (Id ℕ (suc. m2.0) (suc. m2.1)) (x ↦ suc. x)
         (id_ℕ_iso m2.0 m2.1 .to (id_ℕ_iso m2.0 m2.1 .fro m2.2)) m2.2
         (id_ℕ_iso m2.0 m2.1 .to_fro m2.2) ])

def 𝕗_ℕ_code (n0 n1 : ℕ) : isFibrant (ℕ_code n0 n1) ≔ match n0, n1 [
| zero., zero. ↦ 𝕗⊤
| zero., suc. n1 ↦ 𝕗∅
| suc. n0, zero. ↦ 𝕗∅
| suc. n0, suc. n1 ↦ 𝕗_ℕ_code n0 n1 ]

def 𝕗ℕ : isFibrant ℕ ≔ [
| .trr.e ↦ x ↦ x
| .trl.e ↦ x ↦ x
| .liftr.e ↦ x ↦ refl x
| .liftl.e ↦ x ↦ refl x
| .id.e ↦ n0 n1 ↦ 𝕗iso (ℕ_code n0 n1) (Id ℕ n0 n1) (id_ℕ_iso n0 n1)
                        (𝕗_ℕ_code n0 n1) ]

{` Gel types `}

def Gel (A B : Type) (R : A → B → Type) : Id Type A B ≔
  sig a b ↦ ( ungel : R a b )

def Gel_iso (A B : Type) (R : A → B → Type) (a:A) (b:B) 
  : R a b ≅ Gel A B R a b ≔ (
to ≔ r ↦ (r,),
fro ≔ g ↦ g .0,
to_fro ≔ _ ↦ rfl.,
fro_to ≔ _ ↦ rfl.,
to_fro_to ≔ _ ↦ rfl. )

{` Univalence `}

def is11 (A B : Type) (R : A → B → Type) : Type ≔ sig (
  trr : A → B,
  liftr : (a:A) → R a (trr a),
  utrr : (a:A) (b:B) (r:R a b) → Id B b (trr a),
  uliftr : (a:A) (b:B) (r:R a b)
       → Id (R a)(utrr a b r) r (liftr a),
  trl : B → A,
  liftl : (b:B) → R (trl b) b,
  utrl : (a:A) (b:B) (r:R a b) → Id A a (trl b),
  uliftl : (a:A) (b:B) (r:R a b)
       → Id ((x ↦ R x b) : A → Type) (utrl a b r) r (liftl b) )

def is11_iso (A B : Type) (R S : A → B → Type)
  (e : (a:A)(b:B) → R a b ≅ S a b) (re : is11 A B R)
  : is11 A B S ≔ (
trr ≔ re .trr,
liftr ≔ a ↦ e a (re .trr a) .to (re .liftr a),
utrr ≔ a b s ↦ re .utrr a b (e a b .fro s),
uliftr ≔ a b s ↦
  eq.trr (S a b)
    (x ↦ Id S (refl a) (re .utrr a b (e a b .fro s))
          x (e a (re .trr a) .to (re .liftr a)))
    (e a b .to (e a b .fro s)) s (e a b .to_fro s)
    (refl (e a) (re .utrr a b (e a b .fro s))
      .to (re .uliftr a b (e a b .fro s))),
trl ≔ re .trl,
liftl ≔ b ↦ e (re .trl b) b .to (re .liftl b),
utrl ≔ a b s ↦ re .utrl a b (e a b .fro s),
uliftl ≔ a b s ↦
  eq.trr (S a b)
    (x ↦ Id S (re .utrl a b (e a b .fro s)) (refl b)
          x (e (re .trl b) b .to (re .liftl b)))
    (e a b .to (e a b .fro s)) s (e a b .to_fro s)
    (refl e (re .utrl a b (e a b .fro s)) (refl b)
      .to (re .uliftl a b (e a b .fro s))) )

def sym_iso (A00 A01 : Type) (A02 : Id Type A00 A01)
  (A10 A11 : Type) (A12 : Id Type A10 A11)
  (A20 : Id Type A00 A10) (A21 : Id Type A01 A11)
  (A22 : Id (Id Type) A02 A12 A20 A21)
  (a00 : A00) (a01 : A01) (a02 : A02 a00 a01)
  (a10 : A10) (a11 : A11) (a12 : A12 a10 a11)
  (a20 : A20 a00 a10) (a21 : A21 a01 a11)
  : A22 a02 a12 a20 a21 ≅ sym A22 a20 a21 a02 a12 ≔ (
to ≔ a22 ↦ sym a22,
fro ≔ a22 ↦ sym a22,
to_fro ≔ _ ↦ rfl.,
fro_to ≔ _ ↦ rfl.,
to_fro_to ≔ _ ↦ rfl. )

def pre_univalence (A B : Fib) (R : Id Type (A .t) (B .t))
  (𝕗R : (a : A .t) (b : B .t) → isFibrant (R a b))
  (re : is11 (A .t) (B .t) (x y ↦ R x y))
  : Id Fib A B ≔ ( R, [
| .trr.1 ↦ re .trr
| .trl.1 ↦ re .trl
| .liftr.1 ↦ a ↦ re .liftr a
| .liftl.1 ↦ b ↦ re .liftl b
| .id.1 ↦ a b ↦ 𝕗R a b
| .trr.e ↦ a0 b0 r0 ↦
     𝕗R.2 (A.2 .f .liftr.1 a0) (B.2 .f .liftr.1 b0) .trr.1 r0
| .trl.e ↦ a1 b1 r1 ↦
     𝕗R.2 (A.2 .f .liftl.1 a1) (B.2 .f .liftl.1 b1) .trl.1 r1
| .liftr.e ↦ a0 b0 r0 ↦
     sym (𝕗R.2 (A.2 .f .liftr.1 a0) (B.2 .f .liftr.1 b0) .liftr.1 r0)
| .liftl.e ↦ a1 b1 r1 ↦
     sym (𝕗R.2 (A.2 .f .liftl.1 a1) (B.2 .f .liftl.1 b1) .liftl.1 r1)
| .id.e ↦ a0 b0 r0 a1 b1 r1 ↦ pre_univalence
     (A.2 .t a0 a1, A.2 .f .id.1 a0 a1)
     (B.2 .t b0 b1, B.2 .f .id.1 b0 b1)
     (sym R.2 r0 r1)
     (a2 b2 ↦ 𝕗iso
       (R.2 a2 b2 r0 r1)
       (sym R.2 r0 r1 a2 b2)
       (sym_iso (A.0 .t) (A.1 .t) (A.2 .t) (B.0 .t) (B.1 .t) (B.2 .t)
                 R.0 R.1 R.2 a0 a1 a2 b0 b1 b2 r0 r1)
       (𝕗R.2 a2 b2 .id.1 r0 r1))
     (trr ≔ a2 ↦
        refl (B.2 .f .id.1) (re.0 .utrr a0 b0 r0) (re.1 .utrr a1 b1 r1)
          .trl.1 (re.2 .trr a2),
      liftr ≔ a2 ↦ ?,
      trl ≔ b2 ↦
        refl (A.2 .f .id.1) (re.0 .utrl a0 b0 r0) (re.1 .utrl a1 b1 r1)
          .trl.1 (re.2 .trl b2),
      liftl ≔ b2 ↦ ?,
      utrr ≔ a2 b2 r2 ↦ ?,
      uliftr ≔ a2 b2 r2 ↦ ?,
      utrl ≔ a2 b2 r2 ↦ ?,
      uliftl ≔ a2 b2 r2 ↦ ?)
     .f ])

def univalence (A B : Fib) (R : A .t → B .t → Fib)
  (re : is11 (A .t) (B .t) (x y ↦ R x y .t))
  : Id Fib A B
  ≔ let Rt : A .t → B .t → Type ≔ x y ↦ R x y .t in
    pre_univalence A B (Gel (A .t) (B .t) Rt)
      (a b ↦ 𝕗iso (R a b .t) (Gel (A .t) (B .t) Rt a b)
                  (Gel_iso (A .t) (B .t) Rt a b) (R a b .f))
      (is11_iso (A .t) (B .t) (x y ↦ R x y .t)
                (a b ↦ Gel (A .t) (B .t) (x y ↦ R x y .t) a b)
                (a b ↦ Gel_iso (A .t) (B .t) (x y ↦ R x y .t) a b)
                re)

{` The universe `}

def over_and_back (B0 B1 : Fib) (B2 : Id Fib B0 B1) (b0 : B0 .t)
  : Id B0 .t (B2 .f .trl.1 (B2 .f .trr.1 b0)) b0
  ≔ B2⁽ᵉ¹⁾ .f .id.1 (B2 .f .liftl.1 (B2 .f .trr.1 b0)) (B2 .f .liftr.1 b0)
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
  | .id.e ↦ C0 C1 ↦ ? ] ]


{` Attempted partial proof of .trr.e above.  But maybe it's better to just apply univalence.  And maybe .liftr.e etc. can be refl univalence. `}
{`
(
    t ≔ Gel (A.1 .t) (B.1 .t)
           (a1 b1 ↦ C0 .t (A.2 .f .trl.1 a1) (B.2 .f .trl.1 b1)),
    f ≔ [
      | .trr.1 ↦ a1 ↦ B.2 .f .trr.1 (C0 .f .trr.1 (A.2 .f .trl.1 a1))
      | .trr.e ↦ a10 b10 c10 ↦
        (sym C0.2 .f .id.1
          (A.20 .f .trl.1 a10) (A.21 .f .trl.1 (A.12 .f .trr.1 a10))
          (sym A.22 .f .trl.1 a10 (A.12 .f .trr.1 a10) (A.12 .f .liftr.1 a10))
          (B.20 .f .trl.1 b10) (B.21 .f .trl.1 (B.12 .f .trr.1 b10))
          (sym B.22 .f .trl.1 b10 (B.12 .f .trr.1 b10) (B.12 .f .liftr.1 b10))
          .trr.1 (c10 .0),)
      | .trl.1 ↦ b1 ↦ A.2 .f .trr.1 (C0 .f .trl.1 (B.2 .f .trl.1 b1))
      | .trl.e ↦ a11 b11 c11 ↦
        (sym C0.2 .f .id.1
          (A.20 .f .trl.1 (A.12 .f .trl.1 a11)) (A.21 .f .trl.1 a11)
          (sym A.22 .f .trl.1 (A.12 .f .trl.1 a11) a11 (A.12 .f .liftl.1 a11))
          (B.20 .f .trl.1 (B.12 .f .trl.1 b11)) (B.21 .f .trl.1 b11)
          (sym B.22 .f .trl.1 (B.12 .f .trl.1 b11) b11 (B.12 .f .liftl.1 b11))
          .trl.1 (c11 .0),)
      | .liftr.1 ↦ a1 ↦ (
        refl (C0 .f .id.1 (A.2 .f .trl.1 a1))
             (B.2 .f .trl.1 (B.2 .f .trr.1 (C0 .f .trr.1 (A.2 .f .trl.1 a1))))
             (C0 .f .trr.1 (A.2 .f .trl.1 a1))
             (over_and_back B.0 B.1 B.2 (C0 .f .trr.1 (A.2 .f .trl.1 a1)))
        .trl.1 (C0 .f .liftr.1 (A.2 .f .trl.1 a1)),)
      | .liftr.e ↦ a10 b10 c10 ↦ ?
      | .liftl.1 ↦ b1 ↦ ?
      | .liftl.e ↦ a11 b11 c11 ↦ ?
      | .id.1 ↦ a1 b1 ↦ 𝕗iso
        (C0 .t (A.2 .f .trl.1 a1) (B.2 .f .trl.1 b1))
        (Gel (A.1 .t) (B.1 .t)
          (a10 b10 ↦ C0 .t (A.2 .f .trl.1 a10) (B.2 .f .trl.1 b10)) a1 b1)
        (Gel_iso (A.1 .t) (B.1 .t)
          (a10 b10 ↦ C0 .t (A.2 .f .trl.1 a10) (B.2 .f .trl.1 b10)) a1 b1)
        (C0 .f .id.1 (A.2 .f .trl.1 a1) (B.2 .f .trl.1 b1))
      | .id.e ↦ a10 b10 c10 a11 b11 c11 ↦ ? ])
 `}
