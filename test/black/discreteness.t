  $ cat >isprop.ny <<EOF
  > axiom t1 : T
  > axiom t2 : T
  > def Jd (X:Type) (x:X) : X → Type ≔ data [ rfl. : Jd X x x ]
  > def test : Jd T t1 t2 ≔ rfl.
  > EOF

Arbitrary types are not discrete:

  $ cat >arb.ny <<EOF
  > axiom A : Type
  > axiom a : A
  > def T ≔ A⁽ᵈ⁾ a
  > EOF

  $ narya -arity 1 -direction d arb.ny isprop.ny
   ￫ error[E1003]
   ￭ isprop.ny
   4 | def test : Jd T t1 t2 ≔ rfl.
     ^ index
         t1
       of constructor application doesn't match the corresponding index
         t2
       of datatype instance
  
  [1]

They remain so even when discreteness is on:

  $ narya -arity 1 -direction d -discreteness arb.ny isprop.ny
   ￫ error[E1003]
   ￭ isprop.ny
   4 | def test : Jd T t1 t2 ≔ rfl.
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

  $ narya -v -arity 1 -direction d natd.ny isprop.ny
   ￫ info[I0000]
   ￮ Constant ℕ defined
  
   ￫ info[I0001]
   ￮ Axiom n assumed
  
   ￫ info[I0000]
   ￮ Constant T defined
  
   ￫ info[I0001]
   ￮ Axiom t1 assumed
  
   ￫ info[I0001]
   ￮ Axiom t2 assumed
  
   ￫ info[I0000]
   ￮ Constant Jd defined
  
   ￫ error[E1003]
   ￭ isprop.ny
   4 | def test : Jd T t1 t2 ≔ rfl.
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

  $ narya -v -arity 1 -direction d -discreteness nat.ny isprop.ny
   ￫ info[I0000]
   ￮ Constant T defined (discrete)
  
   ￫ info[I0001]
   ￮ Axiom t1 assumed
  
   ￫ info[I0001]
   ￮ Axiom t2 assumed
  
   ￫ info[I0000]
   ￮ Constant Jd defined
  
   ￫ error[E1003]
   ￭ isprop.ny
   4 | def test : Jd T t1 t2 ≔ rfl.
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

  $ narya -v -arity 1 -direction d -discreteness natd.ny isprop.ny
   ￫ info[I0000]
   ￮ Constant ℕ defined (discrete)
  
   ￫ info[I0001]
   ￮ Axiom n assumed
  
   ￫ info[I0000]
   ￮ Constant T defined
  
   ￫ info[I0001]
   ￮ Axiom t1 assumed
  
   ￫ info[I0001]
   ￮ Axiom t2 assumed
  
   ￫ info[I0000]
   ￮ Constant Jd defined
  
   ￫ info[I0000]
   ￮ Constant test defined
  

Non-discrete datatypes are not discrete:

  $ cat >param.ny <<EOF
  > def List (A:Type) : Type ≔ data [ nil. | cons. (_:A) (_:List A) ]
  > axiom A : Type
  > axiom l : List A
  > def T ≔ (List A)⁽ᵈ⁾ l

  $ narya -v -arity 1 -direction d -discreteness param.ny isprop.ny
   ￫ info[I0000]
   ￮ Constant List defined
  
   ￫ info[I0001]
   ￮ Axiom A assumed
  
   ￫ info[I0001]
   ￮ Axiom l assumed
  
   ￫ info[I0000]
   ￮ Constant T defined
  
   ￫ info[I0001]
   ￮ Axiom t1 assumed
  
   ￫ info[I0001]
   ￮ Axiom t2 assumed
  
   ￫ info[I0000]
   ￮ Constant Jd defined
  
   ￫ error[E1003]
   ￭ isprop.ny
   4 | def test : Jd T t1 t2 ≔ rfl.
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

  $ narya -v -arity 1 -direction d -discreteness index.ny isprop.ny
   ￫ info[I0000]
   ￮ Constant ℕ defined (discrete)
  
   ￫ info[I0000]
   ￮ Constant iszero defined
  
   ￫ info[I0001]
   ￮ Axiom n assumed
  
   ￫ info[I0001]
   ￮ Axiom z assumed
  
   ￫ info[I0000]
   ￮ Constant T defined
  
   ￫ info[I0001]
   ￮ Axiom t1 assumed
  
   ￫ info[I0001]
   ￮ Axiom t2 assumed
  
   ￫ info[I0000]
   ￮ Constant Jd defined
  
   ￫ error[E1003]
   ￭ isprop.ny
   4 | def test : Jd T t1 t2 ≔ rfl.
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

  $ narya -v -arity 1 -direction d -discreteness constr.ny isprop.ny
   ￫ info[I0000]
   ￮ Constant foo defined
  
   ￫ info[I0001]
   ￮ Axiom f assumed
  
   ￫ info[I0000]
   ￮ Constant T defined
  
   ￫ info[I0001]
   ￮ Axiom t1 assumed
  
   ￫ info[I0001]
   ￮ Axiom t2 assumed
  
   ￫ info[I0000]
   ￮ Constant Jd defined
  
   ￫ error[E1003]
   ￭ isprop.ny
   4 | def test : Jd T t1 t2 ≔ rfl.
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

  $ narya -v -arity 1 -direction d -discreteness mutual.ny isprop.ny
   ￫ info[I0000]
   ￮ Constants defined mutually:
       even
       odd
  
   ￫ info[I0001]
   ￮ Axiom e assumed
  
   ￫ info[I0000]
   ￮ Constant T defined
  
   ￫ info[I0001]
   ￮ Axiom t1 assumed
  
   ￫ info[I0001]
   ￮ Axiom t2 assumed
  
   ￫ info[I0000]
   ￮ Constant Jd defined
  
   ￫ error[E1003]
   ￭ isprop.ny
   4 | def test : Jd T t1 t2 ≔ rfl.
     ^ index
         t1
       of constructor application doesn't match the corresponding index
         t2
       of datatype instance
  
  [1]

Some other discrete types:

  $ narya -v -arity 1 -direction d -discreteness -e 'def ℕ : Type ≔ data [ zero. | suc. (_:ℕ) ]' -e 'def ℤ : Type ≔ data [ zero. | suc. (_:ℕ) | negsuc. (_:ℕ) ]' -e 'def btree : Type ≔ data [ leaf. | node. (_:btree) (_:btree) ]'
   ￫ info[I0000]
   ￮ Constant ℕ defined (discrete)
  
   ￫ info[I0000]
   ￮ Constant ℤ defined (discrete)
  
   ￫ info[I0000]
   ￮ Constant btree defined (discrete)
  

