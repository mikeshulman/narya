Using the Martin-Löf "Jdentity type" as an indexed datatype, we can try to prove versions of Axiom K.

  $ cat >jd.ny <<EOF
  > def Jd (A:Type) (a:A) : A → Type ≔ data [
  > | rfl. : Jd A a a
  > ]

  $ narya jd.ny -e 'def USIP (A:Type) (a:A) (e:Jd A a a) : Jd (Jd A a a) e rfl. := match e [ rfl. |-> rfl. ]'
   ￫ error[E1305]
   ￭ command-line exec string
   1 | def USIP (A:Type) (a:A) (e:Jd A a a) : Jd (Jd A a a) e rfl. := match e [ rfl. |-> rfl. ]
     ^ unable to find a consistent permutation of the context;
       this probably indicates a cyclic dependency among index terms
       or an attempt to prove a version of Axiom K
  
  [1]

  $ narya jd.ny -e 'def K (A:Type) (a:A) (P : Jd A a a -> Type) (p : P rfl.) (e : Jd A a a) : P e := match e [ rfl. |-> p ]'
   ￫ error[E1305]
   ￭ command-line exec string
   1 | def K (A:Type) (a:A) (P : Jd A a a -> Type) (p : P rfl.) (e : Jd A a a) : P e := match e [ rfl. |-> p ]
     ^ unable to find a consistent permutation of the context;
       this probably indicates a cyclic dependency among index terms
       or an attempt to prove a version of Axiom K
  
  [1]

This "weak K" is mentioned in the "Pattern-matching without K" paper as justifying their second "injectivity" restriction on unification.

  $ narya jd.ny -e 'def weakK (A:Type) (a:A) (P : Jd (Jd A a a) rfl. rfl. -> Type) (p : P rfl.) (e : Jd (Jd A a a) rfl. rfl.) : P e := match e [ rfl. |-> p ]'
   ￫ error[E1202]
   ￭ command-line exec string
   1 | def weakK (A:Type) (a:A) (P : Jd (Jd A a a) rfl. rfl. -> Type) (p : P rfl.) (e : Jd (Jd A a a) rfl. rfl.) : P e := match e [ rfl. |-> p ]
     ^ match variable has invalid or duplicate index:
         rfl.
       match indices must be distinct free variables without degeneracies
  
  [1]

The following indexed datatype appears in Agda bug #1025.

  $ cat >foo.ny <<EOF
  > axiom A : Type
  > axiom a : A
  > def Foo : Jd A a a → Type ≔ data [ foo. : Foo rfl. ]

  $ narya jd.ny foo.ny -e 'def test (e : Jd A a a) (f : Foo e) (i : Jd (Foo e) f f) : Jd (Jd (Foo e) f f) i rfl. ≔ match f [ foo. ↦ match i [ rfl. ↦ rfl. ]]'
   ￫ error[E1202]
   ￭ command-line exec string
   1 | def test (e : Jd A a a) (f : Foo e) (i : Jd (Foo e) f f) : Jd (Jd (Foo e) f f) i rfl. ≔ match f [ foo. ↦ match i [ rfl. ↦ rfl. ]]
     ^ match variable has invalid or duplicate index:
         foo.
       match indices must be distinct free variables without degeneracies
  
  [1]

The heterogeneous Jdentity type also figures in some inconsistencies, such as Agda bug #1408.

  $ cat >hjd.ny <<EOF
  > def Hd (A:Type) (a:A) : (B:Type) (b:B) → Type ≔ data [ rfl. : Hd A a A a ]
  > def Bool : Type ≔ data [ true. | false. ]
  > def D : Bool → Type ≔ data [ x. : D true. | y. : D false. ]
  > def ∅ : Type ≔ data []

  $ narya hjd.ny -e 'def notpdf (u : D false.) (e : Hd (D false.) u (D true.) x.) : ∅ ≔ match e [ ]'
   ￫ error[E1202]
   ￭ command-line exec string
   1 | def notpdf (u : D false.) (e : Hd (D false.) u (D true.) x.) : ∅ ≔ match e [ ]
     ^ match variable has invalid or duplicate index:
         D true.
       match indices must be distinct free variables without degeneracies
  
  [1]
