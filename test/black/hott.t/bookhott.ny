{` Basic facts from Book HoTT using the Martin-Lof identity type.  We are treating this as the outer layer of 2LTT used in Orton-Pitts style to build an inner HOTT layer. `}

section eq ≔

  def eq (A : Type) (a : A) : A → Type ≔ data [ rfl. : eq A a a ]

  def cat (A : Type) (x y z : A) (u : eq A x y) (v : eq A y z) : eq A x z
    ≔ match v [ rfl. ↦ u ]

  def cat3 (A : Type) (x y z w : A) (p : eq A x y) (q : eq A y z)
    (r : eq A z w)
    : eq A x w
    ≔ match q, r [ rfl., rfl. ↦ p ]

  def idl (A : Type) (a0 a1 : A) (a2 : eq A a0 a1)
    : eq (eq A a0 a1) (cat A a0 a0 a1 rfl. a2) a2
    ≔ match a2 [ rfl. ↦ rfl. ]

  def inv (A : Type) (a0 a1 : A) (a2 : eq A a0 a1) : eq A a1 a0 ≔ match a2 [
  | rfl. ↦ rfl.]

  def ap (A B : Type) (f : A → B) (a0 a1 : A) (a2 : eq A a0 a1)
    : eq B (f a0) (f a1)
    ≔ match a2 [ rfl. ↦ rfl. ]

  def ap_ap (A B C : Type) (f : A → B) (g : B → C) (a0 a1 : A)
    (a2 : eq A a0 a1)
    : eq (eq C (g (f a0)) (g (f a1)))
        (ap B C g (f a0) (f a1) (ap A B f a0 a1 a2))
        (ap A C (x ↦ g (f x)) a0 a1 a2)
    ≔ match a2 [ rfl. ↦ rfl. ]

  def trr (A : Type) (P : A → Type) (a0 a1 : A) (a2 : eq A a0 a1) (p : P a0)
    : P a1
    ≔ match a2 [ rfl. ↦ p ]

  def trr_ap (A B : Type) (P : A → Type) (Q : B → Type) (f : A → B)
    (g : (x : A) → P x → Q (f x)) (a0 a1 : A) (a2 : eq A a0 a1) (p : P a0)
    : eq (Q (f a1)) (g a1 (trr A P a0 a1 a2 p))
        (trr B Q (f a0) (f a1) (ap A B f a0 a1 a2) (g a0 p))
    ≔ match a2 [ rfl. ↦ rfl. ]

  def trr2 (A : Type) (B : Type) (P : A → B → Type) (a0 a1 : A)
    (a2 : eq A a0 a1) (b0 b1 : B) (b2 : eq B b0 b1) (p : P a0 b0)
    : P a1 b1
    ≔ match a2, b2 [ rfl., rfl. ↦ p ]

  def trl2 (A : Type) (B : Type) (P : A → B → Type) (a0 a1 : A)
    (a2 : eq A a0 a1) (b0 b1 : B) (b2 : eq B b0 b1) (p : P a1 b1)
    : P a0 b0
    ≔ match a2, b2 [ rfl., rfl. ↦ p ]

  def trr2_ap (A B : Type) (P : A → B → Type) (C D : Type) (Q : C → D → Type)
    (f : A → C) (g : B → D) (h : (x : A) (y : B) → P x y → Q (f x) (g y))
    (a0 a1 : A) (a2 : eq A a0 a1) (b0 b1 : B) (b2 : eq B b0 b1) (p : P a0 b0)
    : eq (Q (f a1) (g b1)) (h a1 b1 (trr2 A B P a0 a1 a2 b0 b1 b2 p))
        (trr2 C D Q (f a0) (f a1) (ap A C f a0 a1 a2) (g b0) (g b1)
           (ap B D g b0 b1 b2) (h a0 b0 p))
    ≔ match a2, b2 [ rfl., rfl. ↦ rfl. ]

  def whiskerR (A : Type) (a0 a1 a2 : A) (a01 a01' : eq A a0 a1)
    (a02 : eq (eq A a0 a1) a01 a01') (a12 : eq A a1 a2)
    : eq (eq A a0 a2) (cat A a0 a1 a2 a01 a12) (cat A a0 a1 a2 a01' a12)
    ≔ match a12 [ rfl. ↦ a02 ]

  def unwhiskerR (A : Type) (a0 a1 a2 : A) (a01 a01' : eq A a0 a1)
    (a12 : eq A a1 a2)
    (a02 : eq (eq A a0 a2) (cat A a0 a1 a2 a01 a12) (cat A a0 a1 a2 a01' a12))
    : eq (eq A a0 a1) a01 a01'
    ≔ match a12 [ rfl. ↦ a02 ]

end

def eq ≔ eq.eq

section sq ≔

  def sq (A : Type) (a00 : A)
    : (a01 : A) (a02 : eq A a00 a01) (a10 a11 : A) (a12 : eq A a10 a11)
      (a20 : eq A a00 a10) (a21 : eq A a01 a11)
      → Type
    ≔ data [
  | rfl. : sq A a00 a00 rfl. a00 a00 rfl. rfl. rfl. ]

  def hrfl (A : Type) (a0 a1 : A) (a2 : eq A a0 a1)
    : sq A a0 a0 rfl. a1 a1 rfl. a2 a2
    ≔ match a2 [ rfl. ↦ rfl. ]

  def nat_toid (A : Type) (f : A → A) (p : (x : A) → eq A (f x) x)
    (a0 a1 : A) (a2 : eq A a0 a1)
    : sq A (f a0) (f a1) (eq.ap A A f a0 a1 a2) a0 a1 a2 (p a0) (p a1)
    ≔ match a2 [ rfl. ↦ hrfl A (f a0) a0 (p a0) ]

  def ap (A B : Type) (f : A → B) (a00 a01 : A) (a02 : eq A a00 a01)
    (a10 a11 : A) (a12 : eq A a10 a11) (a20 : eq A a00 a10)
    (a21 : eq A a01 a11) (a22 : sq A a00 a01 a02 a10 a11 a12 a20 a21)
    : sq B (f a00) (f a01) (eq.ap A B f a00 a01 a02) (f a10) (f a11)
        (eq.ap A B f a10 a11 a12) (eq.ap A B f a00 a10 a20)
        (eq.ap A B f a01 a11 a21)
    ≔ match a22 [ rfl. ↦ rfl. ]

  def act02 (A : Type) (a00 a01 : A) (a02 : eq A a00 a01) (a10 a11 : A)
    (a12 : eq A a10 a11) (a20 : eq A a00 a10) (a21 : eq A a01 a11)
    (a22 : sq A a00 a01 a02 a10 a11 a12 a20 a21) (a02' : eq A a00 a01)
    (p : eq (eq A a00 a01) a02 a02')
    : sq A a00 a01 a02' a10 a11 a12 a20 a21
    ≔ match p [ rfl. ↦ a22 ]

  def act20 (A : Type) (a00 a01 : A) (a02 : eq A a00 a01) (a10 a11 : A)
    (a12 : eq A a10 a11) (a20 : eq A a00 a10) (a21 : eq A a01 a11)
    (a22 : sq A a00 a01 a02 a10 a11 a12 a20 a21) (a20' : eq A a00 a10)
    (p : eq (eq A a00 a10) a20 a20')
    : sq A a00 a01 a02 a10 a11 a12 a20' a21
    ≔ match p [ rfl. ↦ a22 ]

  def to_cat (A : Type) (a00 a01 : A) (a02 : eq A a00 a01) (a10 a11 : A)
    (a12 : eq A a10 a11) (a20 : eq A a00 a10) (a21 : eq A a01 a11)
    (a22 : sq A a00 a01 a02 a10 a11 a12 a20 a21)
    : eq (eq A a00 a11) (eq.cat A a00 a01 a11 a02 a21)
        (eq.cat A a00 a10 a11 a20 a12)
    ≔ match a22 [ rfl. ↦ rfl. ]

  def to_cat3 (A : Type) (a00 a01 : A) (a02 : eq A a00 a01) (a10 a11 : A)
    (a12 : eq A a10 a11) (a20 : eq A a00 a10) (a21 : eq A a01 a11)
    (a22 : sq A a00 a01 a02 a10 a11 a12 a20 a21)
    : eq (eq A a10 a11) a12
        (eq.cat3 A a10 a00 a01 a11 (eq.inv A a00 a10 a20) a02 a21)
    ≔ match a22 [ rfl. ↦ rfl. ]

  def all_rfl_21 (A : Type) (a : A) (a2 : eq A a a)
    (a22 : sq A a a rfl. a a rfl. rfl. a2)
    : eq (eq A a a) a2 rfl.
    ≔ eq.cat (eq A a a) a2 (eq.cat A a a a rfl. a2) rfl.
        (eq.inv (eq A a a) (eq.cat A a a a rfl. a2) a2 (eq.idl A a a a2))
        (to_cat A a a rfl. a a rfl. rfl. a2 a22)

  def unact21 (A : Type) (a00 a01 : A) (a02 : eq A a00 a01) (a10 a11 : A)
    (a12 : eq A a10 a11) (a20 : eq A a00 a10) (a21 : eq A a01 a11)
    (a22 : sq A a00 a01 a02 a10 a11 a12 a20 a21) (a21' : eq A a01 a11)
    (a22' : sq A a00 a01 a02 a10 a11 a12 a20 a21')
    : eq (eq A a01 a11) a21 a21'
    ≔ match a22 [
  | rfl. ↦ eq.inv (eq A a00 a00) a21' rfl. (all_rfl_21 A a00 a21' a22')]

  def cancel_12_eq_21 (A : Type) (a00 a01 : A) (a02 : eq A a00 a01) (a11 : A)
    (a12 : eq A a01 a11) (a20 : eq A a00 a01)
    (a22 : sq A a00 a01 a02 a01 a11 a12 a20 a12)
    : eq (eq A a00 a01) a02 a20
    ≔ eq.unwhiskerR A a00 a01 a11 a02 a20 a12
        (to_cat A a00 a01 a02 a01 a11 a12 a20 a12 a22)

end

def sq ≔ sq.sq

def selfnat (A : Type) (f : A → A) (H : (x : A) → eq A (f x) x) (a : A)
  : eq (eq A (f (f a)) (f a)) (eq.ap A A f (f a) a (H a)) (H (f a))
  ≔ sq.cancel_12_eq_21 A (f (f a)) (f a) (eq.ap A A f (f a) a (H a)) a (H a)
      (H (f a)) (sq.nat_toid A f H (f a) a (H a))

def eqv (A B : Type) : Type ≔ sig (
  to : A → B,
  fro : B → A,
  fro_to : (a : A) → eq A (fro (to a)) a,
  to_fro : (b : B) → eq B (to (fro b)) b,
  to_fro_to : (a : A)
              → eq (eq B (to (fro (to a))) (to a))
                  (eq.ap A B to (fro (to a)) a (fro_to a)) (to_fro (to a)) )

notation 1 eqv : A "≅" B ≔ eqv A B

def fro_to_fro (A B : Type) (e : A ≅ B) (y : B)
  : eq (eq A (e .fro (e .to (e .fro y))) (e .fro y))
      (eq.ap B A (e .fro) (e .to (e .fro y)) y (e .to_fro y))
      (e .fro_to (e .fro y))
  ≔
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
    (eq.ap A A gf (gfg y) (g y) (ap_g (fg y) y (ε y))) (gfg y) (g y)
    (ap_g (fg y) y (ε y)) (η (gfg y)) (ap_g (fg y) y (ε y))
    (sq.act20 A (gfgfg y) (gfg y)
       (eq.ap A A gf (gfg y) (g y) (ap_g (fg y) y (ε y))) (gfg y) (g y)
       (ap_g (fg y) y (ε y)) (ap_g (fgfg y) (fg y) (ε (fg y)))
       (ap_g (fg y) y (ε y))
       (sq.act02 A (gfgfg y) (gfg y)
          (ap_g (fgfg y) (fg y) (ap_fg (fg y) y (ε y))) (gfg y) (g y)
          (ap_g (fg y) y (ε y)) (ap_g (fgfg y) (fg y) (ε (fg y)))
          (ap_g (fg y) y (ε y))
          (sq.ap B A g (fgfg y) (fg y) (ap_fg (fg y) y (ε y)) (fg y) y (ε y)
             (ε (fg y)) (ε y) (sq.nat_toid B fg ε (fg y) y (ε y)))
          (ap_gf (gfg y) (g y) (ap_g (fg y) y (ε y)))
          (eq.cat (eq A (gfgfg y) (gfg y))
             (ap_g (fgfg y) (fg y) (ap_fg (fg y) y (ε y)))
             (ap_gfg (fg y) y (ε y))
             (ap_gf (gfg y) (g y) (ap_g (fg y) y (ε y)))
             (eq.ap_ap B B A fg g (fg y) y (ε y))
             (eq.inv (eq A (gfgfg y) (gfg y))
                (ap_gf (gfg y) (g y) (ap_g (fg y) y (ε y)))
                (ap_gfg (fg y) y (ε y)) (eq.ap_ap B A A g gf (fg y) y (ε y)))))
       (η (gfg y))
       (eq.cat3 (eq A (gfgfg y) (gfg y)) (ap_g (fgfg y) (fg y) (ε (fg y)))
          (ap_g (fgfg y) (fg y) (ap_f (gfg y) (g y) (η (g y))))
          (eq.ap A A gf (gfg y) (g y) (η (g y))) (η (gfg y))
          (eq.inv (eq A (gfgfg y) (gfg y))
             (ap_g (fgfg y) (fg y) (ap_f (gfg y) (g y) (η (g y))))
             (ap_g (fgfg y) (fg y) (ε (fg y)))
             (eq.ap (eq B (fgfg y) (fg y)) (eq A (gfgfg y) (gfg y))
                (ap_g (fgfg y) (fg y)) (ap_f (gfg y) (g y) (η (g y)))
                (ε (fg y)) (e .to_fro_to (g y))))
          (eq.ap_ap A B A f g (gfg y) (g y) (η (g y))) (selfnat A gf η (g y))))
    (η (g y)) (sq.nat_toid A gf η (gfg y) (g y) (ap_g (fg y) y (ε y)))

def adjointify (A B : Type) (f : A → B) (g : B → A)
  (η : (a : A) → eq A (g (f a)) a) (ε : (b : B) → eq B (f (g b)) b)
  : A ≅ B
  ≔
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
  (to ≔ f,
   fro ≔ g,
   fro_to ≔ η,
   to_fro ≔ b ↦
     eq.cat3 B (fg b) (fgfg b) (fg b) b (eq.inv B (fgfg b) (fg b) (ε (fg b)))
       (ap_f (gfg b) (g b) (η (g b))) (ε b),
   to_fro_to ≔ a ↦
     sq.to_cat3 B (fgfgf a) (fgf a) (ap_f (gfgf a) (gf a) (η (gf a))) (fgf a)
       (f a) (ap_f (gf a) a (η a)) (ε (fgf a)) (ε (f a))
       (sq.act02 B (fgfgf a) (fgf a)
          (ap_fg (fgf a) (f a) (ap_f (gf a) a (η a))) (fgf a) (f a)
          (ap_f (gf a) a (η a)) (ε (fgf a)) (ε (f a))
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
                (ap_fgf (gf a) a (η a)) (eq.ap_ap A A B gf f (gf a) a (η a)))
             (eq.ap (eq A (gfgf a) (gf a)) (eq B (fgfgf a) (fgf a))
                (ap_f (gfgf a) (gf a)) (ap_gf (gf a) a (η a)) (η (gf a))
                (selfnat A gf η a)))))
