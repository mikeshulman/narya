Using the Martin-Löf "Jdentity type" as an indexed datatype, we can try to prove versions of Axiom K.

  $ cat >jd.ny <<EOF
  > def Jd (A:Type) (a:A) : A → Type ≔ data [
  > | rfl. : Jd A a a
  > ]

  $ narya -source-only jd.ny -v -e 'def USIP (A:Type) (a:A) (e:Jd A a a) : Jd (Jd A a a) e rfl. := match e [ rfl. |-> rfl. ]'
   ￫ info[I0000]
   ￮ constant Jd defined
  
   ￫ hint[E1101]
   ￭ command-line exec string
   1 | def USIP (A:Type) (a:A) (e:Jd A a a) : Jd (Jd A a a) e rfl. := match e [ rfl. |-> rfl. ]
     ^ match will not refine the goal or context (no consistent permutation of context)
  
   ￫ error[E1003]
   ￭ command-line exec string
   1 | def USIP (A:Type) (a:A) (e:Jd A a a) : Jd (Jd A a a) e rfl. := match e [ rfl. |-> rfl. ]
     ^ index
         e
       of constructor application doesn't match the corresponding index
         rfl.
       of datatype instance
  
  [1]

  $ narya -source-only jd.ny -v -e 'def K (A:Type) (a:A) (P : Jd A a a -> Type) (p : P rfl.) (e : Jd A a a) : P e := match e [ rfl. |-> p ]'
   ￫ info[I0000]
   ￮ constant Jd defined
  
   ￫ hint[E1101]
   ￭ command-line exec string
   1 | def K (A:Type) (a:A) (P : Jd A a a -> Type) (p : P rfl.) (e : Jd A a a) : P e := match e [ rfl. |-> p ]
     ^ match will not refine the goal or context (no consistent permutation of context)
  
   ￫ error[E0401]
   ￭ command-line exec string
   1 | def K (A:Type) (a:A) (P : Jd A a a -> Type) (p : P rfl.) (e : Jd A a a) : P e := match e [ rfl. |-> p ]
     ^ term synthesized type P rfl. but is being checked against type P e
  
  [1]

This "weak K" is mentioned in the "Pattern-matching without K" paper as justifying their second "injectivity" restriction on unification.

  $ narya -source-only jd.ny -v -e 'def weakK (A:Type) (a:A) (P : Jd (Jd A a a) rfl. rfl. -> Type) (p : P rfl.) (e : Jd (Jd A a a) rfl. rfl.) : P e := match e [ rfl. |-> p ]'
   ￫ info[I0000]
   ￮ constant Jd defined
  
   ￫ hint[E1101]
   ￭ command-line exec string
   1 | def weakK (A:Type) (a:A) (P : Jd (Jd A a a) rfl. rfl. -> Type) (p : P rfl.) (e : Jd (Jd A a a) rfl. rfl.) : P e := match e [ rfl. |-> p ]
     ^ match will not refine the goal or context (index is not a free variable):
         rfl.
  
   ￫ error[E0401]
   ￭ command-line exec string
   1 | def weakK (A:Type) (a:A) (P : Jd (Jd A a a) rfl. rfl. -> Type) (p : P rfl.) (e : Jd (Jd A a a) rfl. rfl.) : P e := match e [ rfl. |-> p ]
     ^ term synthesized type P rfl. but is being checked against type P e
  
  [1]

The following indexed datatype appears in Agda bug #1025.

  $ cat >foo.ny <<EOF
  > import "jd"
  > axiom A : Type
  > axiom a : A
  > def Foo : Jd A a a → Type ≔ data [ foo. : Foo rfl. ]

  $ narya -source-only jd.ny foo.ny -v -e 'def test (e : Jd A a a) (f : Foo e) (i : Jd (Foo e) f f) : Jd (Jd (Foo e) f f) i rfl. ≔ match f [ foo. ↦ match i [ rfl. ↦ rfl. ]]'
   ￫ info[I0000]
   ￮ constant Jd defined
  
   ￫ info[I0001]
   ￮ axiom A assumed
  
   ￫ info[I0001]
   ￮ axiom a assumed
  
   ￫ info[I0000]
   ￮ constant Foo defined
  
   ￫ hint[E1101]
   ￭ command-line exec string
   1 | def test (e : Jd A a a) (f : Foo e) (i : Jd (Foo e) f f) : Jd (Jd (Foo e) f f) i rfl. ≔ match f [ foo. ↦ match i [ rfl. ↦ rfl. ]]
     ^ match will not refine the goal or context (index is not a free variable):
         foo.
  
   ￫ error[E1003]
   ￭ command-line exec string
   1 | def test (e : Jd A a a) (f : Foo e) (i : Jd (Foo e) f f) : Jd (Jd (Foo e) f f) i rfl. ≔ match f [ foo. ↦ match i [ rfl. ↦ rfl. ]]
     ^ index
         i
       of constructor application doesn't match the corresponding index
         rfl.
       of datatype instance
  
  [1]

The heterogeneous Jdentity type also figures in some inconsistencies, such as Agda bug #1408.

  $ cat >hjd.ny <<EOF
  > def Hd (A:Type) (a:A) : (B:Type) (b:B) → Type ≔ data [ rfl. : Hd A a A a ]
  > def Bool : Type ≔ data [ true. | false. ]
  > def D : Bool → Type ≔ data [ x. : D true. | y. : D false. ]
  > def ∅ : Type ≔ data []

  $ narya -source-only hjd.ny -v -e 'def notpdf (u : D false.) (e : Hd (D false.) u (D true.) x.) : ∅ ≔ match e [ ]'
   ￫ info[I0000]
   ￮ constant Hd defined
  
   ￫ info[I0000]
   ￮ constant Bool defined
  
   ￫ info[I0000]
   ￮ constant D defined
  
   ￫ info[I0000]
   ￮ constant ∅ defined
  
   ￫ error[E1300]
   ￭ command-line exec string
   1 | def notpdf (u : D false.) (e : Hd (D false.) u (D true.) x.) : ∅ ≔ match e [ ]
     ^ missing match clause for constructor rfl
  
  [1]
