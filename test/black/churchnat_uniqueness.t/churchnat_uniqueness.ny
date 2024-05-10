{` Uniqueness of iteration for Church encoded Nat from parametricity (from Thorsten) `}

def prod (A B : Type) : Type ≔ sig (fst : A, snd : B)
notation 0 prod : A "><" B := prod A B
def Σ (A : Type) (B : A → Type) : Type ≔ sig (fst : A, snd : B fst)
def Gel (A B : Type) (R : A → B → Type) : Id Type A B ≔ sig x y ↦ ( ungel : R x y )

{` First we define a Martin-Lof equality type, with congruence, transitivity, reversal, and transport. `}
def eq (X:Type) (x:X) : X → Type ≔ data [ rfl. : eq X x x ]
def eqr (X:Type) (x:X) : eq X x x ≔ rfl.
def cong (X Y : Type) (f : X → Y) (x y : X) (e : eq X x y) : eq Y (f x) (f y) ≔ match e [ rfl. ↦ rfl. ]
def trans (X:Type) (x y z : X) (p : eq X x y) (q : eq X y z) : eq X x z ≔ match q [ rfl. ↦ p ]
def rev (X:Type) (x y : X) (p : eq X x y) : eq X y x ≔ match p [ rfl. ↦ rfl. ]
def tr (X:Type) (P : X → Type) (x y : X) (p : eq X x y) : (P x) → (P y) ≔ match p [ rfl. ↦ u ↦ u ]

{` Now we define the Church-encoded natural numbers. `}

def cnat : Type ≔ (A:Type) → A → (A → A) → A
def czero : cnat ≔ A z s ↦ z
def csuc : cnat → cnat ≔ n A z s ↦ s (n A z s)
def cone : cnat := csuc czero
def ite (A:Type) (z : A) (s : A → A) (n : cnat) : A ≔ n A z s

{` We postulate funext for such natural numbers.  (Doing it
explicitly, for nat only, avoids the need to introduce dependent
equality types to express general funext for dependent
function-types.) `}

axiom cnatfunext : (m n : cnat)
  → ((A:Type) (z:A) (s:A→A) → eq A (m A z s) (n A z s))
  → eq cnat m n

{` - by parametricity, we can prove that the following triangle
    commutes if f is a CNat-homomorphism:

        ite_A
    N --------> A
      \         /
       \ite_B  / f          f (ite_A n) = ite_B n
        \     /
         v   v
           B
we just use (binary) parametricity for n:
`}

def itecnat  
    ` two nat-algebras
		(A:Type) (zA:A) (sA : A→A) (B:Type) (zB:B) (sB : B→B)
    ` and a nat-homomorphism between them
    (f : A → B) (zf : eq B (f zA) zB) (sf : (a:A) → eq B (f (sA a)) (sB (f a)))
    (n:cnat)
  : eq B (f (ite A zA sA n)) (ite B zB sB n)
  ≔
  refl n A B (Gel A B (a b ↦ eq B (f a) b))
    zA zB (_ ≔ zf) sA sB
    (a b r ↦ (_ ≔ trans B (f (sA a)) (sB (f a)) (sB b) (sf a) (cong B B sB (f a) b (r .0)))) .0

{` - now we apply this to

      ite_X (ite_Nat n) = ite_X n

    i.e.

      n Nat zero suc X z_X s_X = n X z_X s_X

    by η/funext we get

      ite_N n = n Nat zero suc = n
`}

def itenn (n:cnat) : eq cnat (ite cnat czero csuc n) n
  ≔ cnatfunext (ite cnat czero csuc n) n
       (X zX sX ↦ itecnat cnat czero csuc X zX sX (ite X zX sX) (eqr X zX)
                     (m ↦ eqr X (sX (ite X zX sX m))) n)

{` - so now we can apply this to any f : N → A homomorphism and obtain

    f n = f (ite_N n) = ite_A n
`}

def uniq (A:Type) (zA:A) (sA:A→A)
  (f:cnat→A) (zf : eq A (f czero) zA) (sf : (n:cnat) → eq A (f (csuc n)) (sA (f n)))
  (n : cnat)
	: eq A (f n) (ite A zA sA n)
  ≔
  trans A (f n) (f (ite cnat czero csuc n)) (ite A zA sA n)
    (cong cnat A f n (ite cnat czero csuc n) (rev cnat (ite cnat czero csuc n) n (itenn n)))
    (itecnat cnat czero csuc A zA sA f zf sf n)

{` We can define recursor using iterator.

   Using zA : A and fA : N -> (A -> A), we can define 

   f : N -> A as f(n):= proj2 (ite (N x A) (0,zA) ((m,a) ↦ (m+1, fA m a))) `}

def cnat_rec (A : Type) (zA : A) (fA : cnat → (A → A)) (n : cnat) : A
  := ((ite (cnat >< A) (czero , zA) (ma ↦ (csuc (ma .0) , fA (ma .0) (ma .1))) n)) .1

{` For the induction principle, we can use 'uniq' above. 

   For P : N → Type, p0 : P 0, ps n : P n → P (n + 1), we want to define 
   a dependent function (n : N) → P n .

   Define an auxilary type P' = (Σ cnat P), then we have a nat-algebra (P', pz', ps')

   By uniqueness, we have (proj1 o (ite P' pz' ps')) = id_N  

   Transport along this equality at n : N, we can define the desired dependent function. `}

def cnat_ind (P : cnat → Type)
    (p0 : (P czero)) (ps : (n : cnat) (x : (P n)) → (P (csuc n)))
    (n : cnat) : (P n)
  := tr cnat P
        (((ite (Σ cnat P) (czero , p0) (ma ↦ (csuc (ma .0) , ps (ma .0) (ma .1))) n)) .0)
        n
        (trans cnat (((ite (Σ cnat P) (czero , p0) (ma ↦ (csuc (ma .0) , ps (ma .0) (ma .1))) n)) .0)
                    (ite cnat czero csuc n)
                    n
                    (uniq cnat czero csuc
                          (m ↦ ((ite (Σ cnat P) (czero , p0) (ma ↦ (csuc (ma .0) , ps (ma .0) (ma .1))) m)) .0)
                          (eqr cnat czero)
                          (m ↦ eqr cnat (csuc ((m (Σ cnat P) (czero , p0) (ma ↦ (csuc (ma .0) , ps (ma .0) (ma .1)))) .0)))
                          n)
                    (itenn n))
        (((ite (Σ cnat P) (czero , p0) (ma ↦ (csuc (ma .0) , ps (ma .0) (ma .1))) n)) .1)

{` By recursion, we can define _+_ and _x_ on N, and
   
   by induction, we can prove N is a commutative semiring. `}

def cnat_add : cnat → (cnat → cnat) := cnat_rec (cnat → cnat) (n ↦ n) (m g n ↦ csuc (g n))

def cnat_add_assoc : (i j k : cnat) → eq cnat (cnat_add (cnat_add i j) k) (cnat_add i (cnat_add j k))
  := cnat_ind (i ↦ (j k : cnat) → eq cnat (cnat_add (cnat_add i j) k) (cnat_add i (cnat_add j k)))
              (j k ↦ eqr cnat (cnat_add j k))
              (i f j k ↦ cong cnat cnat csuc (cnat_add (cnat_add i j) k) (cnat_add i (cnat_add j k)) (f j k))

def cnat_right_add_zero : (i : cnat) → eq cnat (cnat_add i czero) i
  := cnat_ind (i ↦ eq cnat (cnat_add i czero) i)
              (eqr cnat czero)
              (i f ↦ cong cnat cnat csuc (cnat_add i czero) i f)

def cnat_left_add_zero : (i : cnat) → eq cnat (cnat_add czero i) i
  := (i ↦ eqr cnat i)            

def cnat_add_succ : (i j : cnat) → eq cnat (cnat_add i (csuc j)) (csuc (cnat_add i j))
  := cnat_ind (i ↦ (j :cnat) →  eq cnat (cnat_add i (csuc j)) (csuc (cnat_add i j)))
              (j ↦ eqr cnat (csuc j))
              (i f j ↦ cong cnat cnat csuc (cnat_add i (csuc j)) (csuc (cnat_add i j)) (f j))

def cnat_add_comm : (i j : cnat) → eq cnat (cnat_add i j) (cnat_add j i)
 := cnat_ind (i ↦ (j : cnat) → eq cnat (cnat_add i j) (cnat_add j i))
             (j ↦ (rev cnat (cnat_add j czero) j (cnat_right_add_zero j)))
             (i f j ↦ trans cnat
                             (cnat_add (csuc i) j)
                             (csuc (cnat_add j i))
                             (cnat_add j (csuc i))
                             (cong cnat cnat csuc (cnat_add i j) (cnat_add j i) (f j))
                             (rev cnat (cnat_add j (csuc i)) (csuc (cnat_add j i)) (cnat_add_succ j i)))

def cnat_mul : cnat → (cnat → cnat) := cnat_rec (cnat → cnat) (n ↦ czero) (m g n ↦ cnat_add (g n) n)

def cnat_right_mul_zero : (i : cnat) -> eq cnat (cnat_mul i czero) czero
  := cnat_ind (i ↦  eq cnat (cnat_mul i czero) czero)
              (eqr cnat czero)
              (i f ↦ trans cnat
                            (cnat_add (cnat_mul i czero) czero)
                            (cnat_mul i czero)
                            czero
                            (cnat_right_add_zero (cnat_mul i czero))
                            f)

def cnat_left_mul_zero : (i : cnat) → eq cnat (cnat_mul czero i) czero
  := (i ↦ eqr cnat czero)

def cnat_right_mul_one : (i : cnat) → eq cnat (cnat_mul i cone) i
  := cnat_ind (i ↦ eq cnat (cnat_mul i cone) i)
              (eqr cnat czero)
              (i f ↦ trans cnat
                            (cnat_add (cnat_mul i cone) cone)
                            (csuc (cnat_add (cnat_mul i cone) czero))
                            (csuc i)
                            (cnat_add_succ (cnat_mul i cone) czero)
                            (cong cnat cnat csuc
                                  (cnat_add (cnat_mul i cone) czero)
                                  i
                                  (trans cnat
                                     (cnat_add (cnat_mul i cone) czero)
                                     (cnat_mul i cone)
                                     i
                                     (cnat_right_add_zero (cnat_mul i cone))
                                     f)))

def cnat_left_mul_one : (i : cnat) → eq cnat (cnat_mul cone i) i
  := (i ↦ cnat_left_add_zero i)

def cnat_mul_succ : (i j : cnat) → eq cnat (cnat_mul i (csuc j)) (cnat_add i (cnat_mul i j))
  := cnat_ind (i ↦ (j : cnat) → eq cnat (cnat_mul i (csuc j)) (cnat_add i (cnat_mul i j)))
              (j ↦ eqr cnat czero)
              (i f j ↦ trans cnat
                              (cnat_mul (csuc i) (csuc j))
                              (cnat_add (cnat_add i (cnat_mul i j)) (csuc j))
                              (cnat_add (csuc i) (cnat_mul (csuc i) j))
                              (cong cnat cnat (k ↦ cnat_add k (csuc j))
                                    (cnat_mul i (csuc j)) (cnat_add i (cnat_mul i j)) (f j))
                              (trans cnat
                                     (cnat_add (cnat_add i (cnat_mul i j)) (csuc j))
                                     (csuc (cnat_add (cnat_add i (cnat_mul i j)) j))
                                     (cnat_add (csuc i) (cnat_mul (csuc i) j))
                                     (cnat_add_succ (cnat_add i (cnat_mul i j)) j)
                                     (cong cnat cnat csuc (cnat_add (cnat_add i (cnat_mul i j)) j)
                                           (cnat_add i (cnat_add (cnat_mul i j) j))
                                           (cnat_add_assoc i (cnat_mul i j) j))))

def cnat_mul_comm : (i j : cnat) → eq cnat (cnat_mul i j) (cnat_mul j i)
 := cnat_ind (i ↦ (j : cnat) → eq cnat (cnat_mul i j) (cnat_mul j i))
             (j ↦ rev cnat (cnat_mul j czero) czero (cnat_right_mul_zero j))
             (i f j ↦ trans cnat
                             (cnat_mul (csuc i) j)
                             (cnat_add (cnat_mul j i) j)
                             (cnat_mul j (csuc i))
                             (cong cnat cnat (k |-> cnat_add k j) (cnat_mul i j) (cnat_mul j i) (f j))
                             (trans cnat (cnat_add (cnat_mul j i) j)
                                         (cnat_add j (cnat_mul j i))
                                         (cnat_mul j (csuc i))
                                         (cnat_add_comm (cnat_mul j i) j)
                                         (rev cnat (cnat_mul j (csuc i)) (cnat_add j (cnat_mul j i)) (cnat_mul_succ j i))))

def cnat_left_distr_mul_add : (i j k : cnat) → eq cnat (cnat_mul i (cnat_add j k)) (cnat_add (cnat_mul i j) (cnat_mul i k))
  := cnat_ind (i ↦ (j k : cnat) → eq cnat (cnat_mul i (cnat_add j k)) (cnat_add (cnat_mul i j) (cnat_mul i k)))
              (j k ↦ eqr cnat czero)
              (i f j k ↦ trans cnat
                                (cnat_mul (csuc i) (cnat_add j k))
                                (cnat_add (cnat_add (cnat_mul i j) (cnat_mul i k)) (cnat_add j k))
                                (cnat_add (cnat_mul (csuc i) j) (cnat_mul (csuc i) k))
                                (cong cnat cnat (n ↦ (cnat_add n (cnat_add j k)))
                                        (cnat_mul i (cnat_add j k)) (cnat_add (cnat_mul i j) (cnat_mul i k)) (f j k))
                                (trans cnat
                                       (cnat_add (cnat_add (cnat_mul i j) (cnat_mul i k)) (cnat_add j k))
                                       (cnat_add (cnat_mul i j) (cnat_add (cnat_mul i k) (cnat_add j k)))
                                       (cnat_add (cnat_mul (csuc i) j) (cnat_mul (csuc i) k))
                                       (cnat_add_assoc (cnat_mul i j) (cnat_mul i k) (cnat_add j k))
                                       (trans cnat
                                              (cnat_add (cnat_mul i j) (cnat_add (cnat_mul i k) (cnat_add j k)))
                                              (cnat_add (cnat_mul i j) (cnat_add (cnat_add (cnat_mul i k) j) k))
                                              (cnat_add (cnat_mul (csuc i) j) (cnat_mul (csuc i) k))
                                              (cong cnat cnat (n ↦ cnat_add (cnat_mul i j) n)
                                                   (cnat_add (cnat_mul i k) (cnat_add j k))
                                                   (cnat_add (cnat_add (cnat_mul i k) j) k)
                                                   (rev cnat
                                                        (cnat_add (cnat_add (cnat_mul i k) j) k)
                                                        (cnat_add (cnat_mul i k) (cnat_add j k))
                                                        (cnat_add_assoc (cnat_mul i k) j k)))
                                              (trans cnat
                                                     (cnat_add (cnat_mul i j) (cnat_add (cnat_add (cnat_mul i k) j) k))
                                                     (cnat_add (cnat_mul i j) (cnat_add (cnat_add j (cnat_mul i k)) k))
                                                     (cnat_add (cnat_mul (csuc i) j) (cnat_mul (csuc i) k))
                                                     (cong cnat cnat (n ↦ cnat_add (cnat_mul i j) (cnat_add n k))
                                                           (cnat_add (cnat_mul i k) j)
                                                           (cnat_add j (cnat_mul i k))
                                                           (cnat_add_comm (cnat_mul i k) j))
                                                     (trans cnat
                                                           (cnat_add (cnat_mul i j) (cnat_add (cnat_add j (cnat_mul i k)) k))
                                                           (cnat_add (cnat_mul i j) (cnat_add j (cnat_add (cnat_mul i k) k)))
                                                           (cnat_add (cnat_mul (csuc i) j) (cnat_mul (csuc i) k))
                                                           (cong cnat cnat (n ↦ cnat_add (cnat_mul i j) n)
                                                                 (cnat_add (cnat_add j (cnat_mul i k)) k)
                                                                 (cnat_add j (cnat_add (cnat_mul i k) k))
                                                                 (cnat_add_assoc j (cnat_mul i k) k))
                                                           (rev cnat
                                                                (cnat_add (cnat_mul (csuc i) j) (cnat_mul (csuc i) k))
                                                                (cnat_add (cnat_mul i j) (cnat_add j (cnat_mul (csuc i) k)))
                                                                (cnat_add_assoc (cnat_mul i j) j (cnat_add (cnat_mul i k) k))))))))

def cnat_right_distr_mul_add : (i j k : cnat) → eq cnat (cnat_mul (cnat_add j k) i) (cnat_add (cnat_mul j i) (cnat_mul k i))
  := (i j k ↦ trans cnat
                     (cnat_mul (cnat_add j k) i)
                     (cnat_mul i (cnat_add j k))
                     (cnat_add (cnat_mul j i) (cnat_mul k i))
                     (cnat_mul_comm (cnat_add j k) i)
                     (trans cnat
                            (cnat_mul i (cnat_add j k))
                            (cnat_add (cnat_mul i j) (cnat_mul i k))
                            (cnat_add (cnat_mul j i) (cnat_mul k i))
                            (cnat_left_distr_mul_add i j k)
                            (trans cnat
                                   (cnat_add (cnat_mul i j) (cnat_mul i k))
                                   (cnat_add (cnat_mul j i) (cnat_mul i k))
                                   (cnat_add (cnat_mul j i) (cnat_mul k i))
                                   (cong cnat cnat (n ↦ cnat_add n (cnat_mul i k))
                                         (cnat_mul i j) (cnat_mul j i) (cnat_mul_comm i j))
                                   (cong cnat cnat (n ↦ cnat_add (cnat_mul j i) n)
                                         (cnat_mul i k) (cnat_mul k i) (cnat_mul_comm i k)))))
     
def cnat_mul_assoc : (i j k : cnat) → eq cnat (cnat_mul (cnat_mul i j) k) (cnat_mul i (cnat_mul j k))
  := cnat_ind (i ↦ (j k : cnat) -> eq cnat (cnat_mul (cnat_mul i j) k) (cnat_mul i (cnat_mul j k)))
              (j k ↦ eqr cnat czero)
              (i f j k ↦ trans cnat
                                (cnat_mul (cnat_mul (csuc i) j) k)
                                (cnat_add (cnat_mul (cnat_mul i j) k) (cnat_mul j k))
                                (cnat_mul (csuc i) (cnat_mul j k))
                                (cnat_right_distr_mul_add k (cnat_mul i j) j)
                                (cong cnat cnat (n ↦ cnat_add n (cnat_mul j k))
                                     (cnat_mul (cnat_mul i j) k) (cnat_mul i (cnat_mul j k)) (f j k)))
