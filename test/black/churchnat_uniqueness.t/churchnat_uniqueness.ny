{` Uniqueness of iteration for Church encoded Nat from parametricity (from Thorsten) `}

{` First we postulate an equality type, with congruence, transitivity, and reversal. `}
axiom eq : (X:Type) → X → X → Type
axiom eqr : (X:Type) (x:X) → eq X x x
axiom cong : (X Y : Type) (f : X → Y) (x y : X) (e : eq X x y) → eq Y (f x) (f y)
axiom trans : (X:Type) (x y z : X) (p : eq X x y) (q : eq X y z) → eq X x z
axiom rev : (X:Type) (x y : X) (p : eq X x y) → eq X y x

{` Now we define the Church-encoded natural numbers. `}

def nat : Type ≔ (A:Type) → A → (A → A) → A
def zero : nat ≔ A z s ↦ z
def suc : nat → nat ≔ n A z s ↦ s (n A z s)
def ite (A:Type) (z : A) (s : A → A) (n : nat) : A ≔ n A z s

{` We postulate funext for such natural numbers.  (Doing it
explicitly, for nat only, avoids the need to introduce dependent
equality types to express general funext for dependent
function-types.) `}

axiom natfunext : (m n : nat)
  → ((A:Type) (z:A) (s:A→A) → eq A (m A z s) (n A z s))
  → eq nat m n

{` - by parametricity, we can prove that the following triangle
    commutes if f is a Nat-homomorphism:

        ite_A
    N --------> A
      \         /
       \ite_B  / f          f (ite_A n) = ite_B n
        \     /
         v   v
           B
we just use (binary) parametricity for n:
`}

def itenat
    ` two nat-algebras
		(A:Type) (zA:A) (sA : A→A) (B:Type) (zB:B) (sB : B→B)
    ` and a nat-homomorphism between them
    (f : A → B) (zf : eq B (f zA) zB) (sf : (a:A) → eq B (f (sA a)) (sB (f a)))
    (n:nat)
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

def itenn (n:nat) : eq nat (ite nat zero suc n) n
  ≔ natfunext (ite nat zero suc n) n
       (X zX sX ↦ itenat nat zero suc X zX sX (ite X zX sX) (eqr X zX)
                     (m ↦ eqr X (sX (ite X zX sX m))) n)

{` - so now we can apply this to any f : N → A homomorphism and obtain

    f n = f (ite_N n) = ite_A n
`}

def uniq (A:Type) (zA:A) (sA:A→A)
  (f:nat→A) (zf : eq A (f zero) zA) (sf : (n:nat) → eq A (f (suc n)) (sA (f n)))
  (n : nat)
	: eq A (f n) (ite A zA sA n)
  ≔
  trans A (f n) (f (ite nat zero suc n)) (ite A zA sA n)
    (cong nat A f n (ite nat zero suc n) (rev nat (ite nat zero suc n) n (itenn n)))
    (itenat nat zero suc A zA sA f zf sf n)
