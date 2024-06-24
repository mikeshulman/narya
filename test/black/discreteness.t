  $ cat >jd.ny <<EOF
  > def Jd (X:Type) (x:X) : X → Type ≔ data [ rfl. : Jd X x x ]
  > EOF

Arbitrary types are not discrete:

  $ cat >arb.ny <<EOF
  > axiom A : Type
  > axiom a : A
  > def T ≔ A⁽ᵈ⁾ a
  > EOF

  $ narya -source-only -arity 1 -direction d arb.ny jd.ny -e 'def test (t1 : T) (t2 : T) : Jd T t1 t2 ≔ rfl.'
   ￫ error[E1003]
   ￭ command-line exec string
   1 | def test (t1 : T) (t2 : T) : Jd T t1 t2 ≔ rfl.
     ^ index
         t1
       of constructor application doesn't match the corresponding index
         t2
       of datatype instance
  
  [1]

They remain so even when discreteness is on:

  $ narya -source-only -arity 1 -direction d -discreteness arb.ny jd.ny -e 'def test (t1 : T) (t2 : T) : Jd T t1 t2 ≔ rfl.'
   ￫ error[E1003]
   ￭ command-line exec string
   1 | def test (t1 : T) (t2 : T) : Jd T t1 t2 ≔ rfl.
     ^ index
         t1
       of constructor application doesn't match the corresponding index
         t2
       of datatype instance
  
  [1]

There are no discrete datatypes if discreteness is off:

  $ cat >natd.ny <<EOF
  > def ℕ : Type ≔ data [ zero. | suc. (_:ℕ) ]
  > axiom n : ℕ
  > def T ≔ ℕ⁽ᵈ⁾ n
  > EOF

  $ narya -source-only -v -arity 1 -direction d natd.ny jd.ny -e 'def test (t1 : T) (t2 : T) : Jd T t1 t2 ≔ rfl.'
   ￫ info[I0000]
   ￮ constant ℕ defined
  
   ￫ info[I0001]
   ￮ axiom n assumed
  
   ￫ info[I0000]
   ￮ constant T defined
  
   ￫ info[I0000]
   ￮ constant Jd defined
  
   ￫ error[E1003]
   ￭ command-line exec string
   1 | def test (t1 : T) (t2 : T) : Jd T t1 t2 ≔ rfl.
     ^ index
         t1
       of constructor application doesn't match the corresponding index
         t2
       of datatype instance
  
  [1]

Discrete datatypes are not themselves propositions:

  $ cat >nat.ny <<EOF
  > def T : Type ≔ data [ zero. | suc. (_:T) ]
  > EOF

  $ narya -source-only -v -arity 1 -direction d -discreteness nat.ny jd.ny -e 'def test (t1 : T) (t2 : T) : Jd T t1 t2 ≔ rfl.'
   ￫ info[I0000]
   ￮ constant T defined (discrete)
  
   ￫ info[I0000]
   ￮ constant Jd defined
  
   ￫ error[E1003]
   ￭ command-line exec string
   1 | def test (t1 : T) (t2 : T) : Jd T t1 t2 ≔ rfl.
     ^ index
         t1
       of constructor application doesn't match the corresponding index
         t2
       of datatype instance
  
  [1]

But their degenerate versions are:

  $ cat >natd.ny <<EOF
  > def ℕ : Type ≔ data [ zero. | suc. (_:ℕ) ]
  > axiom n : ℕ
  > def T ≔ ℕ⁽ᵈ⁾ n
  > EOF

  $ narya -source-only -v -arity 1 -direction d -discreteness natd.ny jd.ny -e 'def test (t1 : T) (t2 : T) : Jd T t1 t2 ≔ rfl.'
   ￫ info[I0000]
   ￮ constant ℕ defined (discrete)
  
   ￫ info[I0001]
   ￮ axiom n assumed
  
   ￫ info[I0000]
   ￮ constant T defined
  
   ￫ info[I0000]
   ￮ constant Jd defined
  
   ￫ info[I0000]
   ￮ constant test defined
  

Non-discrete datatypes are not discrete:

  $ cat >param.ny <<EOF
  > def List (A:Type) : Type ≔ data [ nil. | cons. (_:A) (_:List A) ]
  > axiom A : Type
  > axiom l : List A
  > def T ≔ (List A)⁽ᵈ⁾ l

  $ narya -source-only -v -arity 1 -direction d -discreteness param.ny jd.ny -e 'def test (t1 : T) (t2 : T) : Jd T t1 t2 ≔ rfl.'
   ￫ info[I0000]
   ￮ constant List defined
  
   ￫ info[I0001]
   ￮ axiom A assumed
  
   ￫ info[I0001]
   ￮ axiom l assumed
  
   ￫ info[I0000]
   ￮ constant T defined
  
   ￫ info[I0000]
   ￮ constant Jd defined
  
   ￫ error[E1003]
   ￭ command-line exec string
   1 | def test (t1 : T) (t2 : T) : Jd T t1 t2 ≔ rfl.
     ^ index
         t1
       of constructor application doesn't match the corresponding index
         t2
       of datatype instance
  
  [1]

  $ cat >index.ny <<EOF
  > def ℕ : Type ≔ data [ zero. | suc. (_:ℕ) ]
  > def iszero : ℕ → Type ≔ data [ iszero. : iszero zero. ]
  > axiom n : ℕ
  > axiom z : iszero n
  > def T ≔ (iszero n)⁽ᵈ⁾ z

  $ narya -source-only -v -arity 1 -direction d -discreteness index.ny jd.ny -e 'def test (t1 : T) (t2 : T) : Jd T t1 t2 ≔ rfl.'
   ￫ info[I0000]
   ￮ constant ℕ defined (discrete)
  
   ￫ info[I0000]
   ￮ constant iszero defined
  
   ￫ info[I0001]
   ￮ axiom n assumed
  
   ￫ info[I0001]
   ￮ axiom z assumed
  
   ￫ info[I0000]
   ￮ constant T defined
  
   ￫ info[I0000]
   ￮ constant Jd defined
  
   ￫ error[E1003]
   ￭ command-line exec string
   1 | def test (t1 : T) (t2 : T) : Jd T t1 t2 ≔ rfl.
     ^ index
         t1
       of constructor application doesn't match the corresponding index
         t2
       of datatype instance
  
  [1]

  $ cat >constr.ny <<EOF
  > def foo : Type ≔ data [ foo. (_:Type) ]
  > axiom f : foo
  > def T ≔ foo⁽ᵈ⁾ f

  $ narya -source-only -v -arity 1 -direction d -discreteness constr.ny jd.ny -e 'def test (t1 : T) (t2 : T) : Jd T t1 t2 ≔ rfl.'
   ￫ info[I0000]
   ￮ constant foo defined
  
   ￫ info[I0001]
   ￮ axiom f assumed
  
   ￫ info[I0000]
   ￮ constant T defined
  
   ￫ info[I0000]
   ￮ constant Jd defined
  
   ￫ error[E1003]
   ￭ command-line exec string
   1 | def test (t1 : T) (t2 : T) : Jd T t1 t2 ≔ rfl.
     ^ index
         t1
       of constructor application doesn't match the corresponding index
         t2
       of datatype instance
  
  [1]

  $ cat >mutual.ny <<EOF
  > def even : Type ≔ data [ zero. | suc. (_ : odd) ]
  > and odd : Type ≔ data [ suc. (_:even) ]
  > axiom e : even
  > def T ≔ even⁽ᵈ⁾ e
  > EOF

  $ narya -source-only -v -arity 1 -direction d -discreteness mutual.ny jd.ny -e 'def test (t1 : T) (t2 : T) : Jd T t1 t2 ≔ rfl.'
   ￫ info[I0000]
   ￮ constants defined mutually:
       even
       odd
  
   ￫ info[I0001]
   ￮ axiom e assumed
  
   ￫ info[I0000]
   ￮ constant T defined
  
   ￫ info[I0000]
   ￮ constant Jd defined
  
   ￫ error[E1003]
   ￭ command-line exec string
   1 | def test (t1 : T) (t2 : T) : Jd T t1 t2 ≔ rfl.
     ^ index
         t1
       of constructor application doesn't match the corresponding index
         t2
       of datatype instance
  
  [1]

Some other discrete types:

  $ narya -source-only -v -arity 1 -direction d -discreteness -e 'def ℕ : Type ≔ data [ zero. | suc. (_:ℕ) ]' -e 'def ℤ : Type ≔ data [ zero. | suc. (_:ℕ) | negsuc. (_:ℕ) ]' -e 'def btree : Type ≔ data [ leaf. | node. (_:btree) (_:btree) ]'
   ￫ info[I0000]
   ￮ constant ℕ defined (discrete)
  
   ￫ info[I0000]
   ￮ constant ℤ defined (discrete)
  
   ￫ info[I0000]
   ￮ constant btree defined (discrete)
  

