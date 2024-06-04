  $ narya -v matchterm.ny
   ￫ info[I0000]
   ￮ Constant ℕ defined
  
   ￫ info[I0000]
   ￮ Constant plus defined
  
   ￫ info[I0000]
   ￮ Constant bool defined
  
   ￫ info[I0000]
   ￮ Constant plus_is_1 defined
  
  true.
    : bool
  
  false.
    : bool
  
  true.
    : bool
  
  false.
    : bool
  
  false.
    : bool
  
   ￫ info[I0000]
   ￮ Constant ⊥ defined
  
   ￫ info[I0000]
   ￮ Constant contra defined
  
   ￫ hint[E1101]
   ￭ matchterm.ny
   12 | def doublematch (n : ℕ) : bool ≔ match n [ zero. ↦ false. | suc. k ↦ match n [ zero. ↦ true. | suc. _ ↦ false. ]]
      ^ match will not refine the goal or context (discriminee is let-bound): n
  
   ￫ info[I0000]
   ￮ Constant doublematch defined
  
   ￫ info[I0000]
   ￮ Constant doublematch' defined
  
   ￫ info[I0000]
   ￮ Constant ⊤ defined
  
   ￫ info[I0000]
   ￮ Constant zero_or_suc defined
  
   ￫ info[I0000]
   ￮ Constant plus_zero_or_suc defined
  
   ￫ info[I0000]
   ￮ Constant Vec defined
  
   ￫ info[I0000]
   ￮ Constant idvec defined
  
   ￫ info[I0000]
   ￮ Constant nil_or_cons defined
  
   ￫ info[I0000]
   ￮ Constant idvec_nil_or_cons defined
  

  $ narya -v multi.ny
   ￫ info[I0000]
   ￮ Constant bool defined
  
   ￫ info[I0000]
   ￮ Constant ℕ defined
  
   ￫ info[I0000]
   ￮ Constant bool.and defined
  
  true.
    : bool
  
  false.
    : bool
  
   ￫ info[I0000]
   ￮ Constant plus defined
  
   ￫ info[I0002]
   ￮ Notation plus defined
  
   ￫ info[I0000]
   ￮ Constant fib defined
  
  13
    : ℕ
  
  21
    : ℕ
  
   ￫ info[I0000]
   ￮ Constant fib' defined
  
   ￫ info[I0000]
   ￮ Constant fib'' defined
  
   ￫ info[I0000]
   ￮ Constant even defined
  
   ￫ info[I0000]
   ￮ Constant minus2 defined
  
  2
    : ℕ
  
   ￫ info[I0000]
   ￮ Constant bothzero defined
  
  false.
    : bool
  
  false.
    : bool
  
  true.
    : bool
  
   ￫ info[I0000]
   ￮ Constant ⊥ defined
  
   ￫ info[I0000]
   ￮ Constant abort1 defined
  
   ￫ info[I0000]
   ￮ Constant abort2 defined
  
   ￫ info[I0000]
   ￮ Constant Gel defined
  
   ￫ info[I0000]
   ￮ Constant ⊤ defined
  
   ￫ hint[H0403]
   ￭ multi.ny
   82 | def ⊤eq⊥ : Id Type ⊤ ⊥ ≔ Gel ⊤ ⊥ []
      ^ matching lambda encountered outside case tree, wrapping in implicit let-binding
  
   ￫ info[I0000]
   ￮ Constant ⊤eq⊥ defined
  
   ￫ info[I0000]
   ￮ Constant foo defined
  
   ￫ info[I0000]
   ￮ Constant one_not_even defined
  
   ￫ info[I0000]
   ￮ Constant suc_even_not_even defined
  
   ￫ info[I0000]
   ￮ Constant suc_even_not_even' defined
  
   ￫ info[I0000]
   ￮ Constant sum defined
  
   ￫ info[I0000]
   ￮ Constant sum⊥ defined
  
   ￫ info[I0000]
   ￮ Constant sum⊥' defined
  
   ￫ info[I0001]
   ￮ Axiom oops assumed
  
  sum⊥' Type (inr. oops)
    : Type
  
   ￫ info[I0000]
   ￮ Constant sum⊥'' defined
  
   ￫ info[I0000]
   ￮ Constant sum⊥''' defined
  
   ￫ info[I0000]
   ￮ Constant is_zero defined
  
   ￫ info[I0000]
   ￮ Constant is_zero_eq_zero defined
  
   ￫ info[I0000]
   ￮ Constant is_zero_eq_zero' defined
  
   ￫ info[I0000]
   ￮ Constant is_zero_eq_zero_rev defined
  
   ￫ info[I0000]
   ￮ Constant is_zero_eq_zero_rev' defined
  


  $ narya -e 'def bool : Type ≔ data [ true. | false. ]' -e 'def bool.and (x y : bool) : bool ≔ match x,y [ true. , true. ↦ true. | true. , false. ↦ false. | _ , false. ↦ false. ]'
   ￫ error[E1307]
   ￭ command-line exec string
   1 | def bool.and (x y : bool) : bool ≔ match x,y [ true. , true. ↦ true. | true. , false. ↦ false. | _ , false. ↦ false. ]
     ^ overlapping patterns in match
  
  [1]

  $ narya -e 'def bool : Type ≔ data [ true. | false. ]' -e 'def test (x y : bool) : bool ≔ match x,y [ true. , true. ↦ true. | false. ↦ false. ]'
   ￫ error[E1305]
   ￭ command-line exec string
   1 | def test (x y : bool) : bool ≔ match x,y [ true. , true. ↦ true. | false. ↦ false. ]
     ^ wrong number of patterns for match
  
  [1]

  $ narya -e 'def bool : Type ≔ data [ true. | false. ]' -e 'def test (x y : bool) : bool ≔ match x,y [ true. , true. ↦ true. | true., false., false. ↦ false. ]'
   ￫ error[E0200]
   ￭ command-line exec string
   1 | def test (x y : bool) : bool ≔ match x,y [ true. , true. ↦ true. | true., false., false. ↦ false. ]
     ^ parse error
  
  [1]

  $ narya -e 'def bool : Type ≔ data [ true. | false. ]' -e 'def neg (x : bool) : bool ≔ match x [ true. ↦ false. | false. ↦ . ]'
   ￫ error[E1309]
   ￭ command-line exec string
   1 | def neg (x : bool) : bool ≔ match x [ true. ↦ false. | false. ↦ . ]
     ^ invalid refutation: no discriminee has an empty type
  
  [1]

  $ narya -v -e 'def bool : Type ≔ data [ true. | false. ]' -e 'def ⊥ : Type ≔ data [ ]' -e 'def foo (x : ⊥) (y : bool) : ⊥ ≔ match x, y [ ]' -e 'def foo2 (x : ⊥) (y : bool) : ⊥ ≔ match y, x [ ]' -e 'def unit : Type := data [ star. ]' -e 'def foo3 (x : bool) (y : unit) : ⊥ ≔ match x, y [ ]'
   ￫ info[I0000]
   ￮ Constant bool defined
  
   ￫ info[I0000]
   ￮ Constant ⊥ defined
  
   ￫ info[I0000]
   ￮ Constant foo defined
  
   ￫ info[I0000]
   ￮ Constant foo2 defined
  
   ￫ info[I0000]
   ￮ Constant unit defined
  
   ￫ error[E1300]
   ￭ command-line exec string
   1 | def foo3 (x : bool) (y : unit) : ⊥ ≔ match x, y [ ]
     ^ missing match clause for constructor true
  
  [1]

  $ narya -e 'def bool : Type ≔ data [ true. | false. ]' -e 'def foo (x : bool) : bool ≔ match x [ true. ↦ false. | false. y ↦ true. ]'
   ￫ error[E1303]
   ￭ command-line exec string
   1 | def foo (x : bool) : bool ≔ match x [ true. ↦ false. | false. y ↦ true. ]
     ^ too many arguments to constructor false in match pattern (1 extra)
  
  [1]


  $ narya -e 'def bool : Type ≔ data [ true. | false. ]' -e 'def foo (x : bool) : bool ≔ match x [ true. ↦ false. | true. y ↦ true. ]'
   ￫ error[E1306]
   ￭ command-line exec string
   1 | def foo (x : bool) : bool ≔ match x [ true. ↦ false. | true. y ↦ true. ]
     ^ inconsistent patterns in match
  
  [1]
  $ narya -e 'def prod (A B : Type) : Type ≔ data [ pair. (_:A) (_:B) ]' -e 'def proj1 (A B C : Type) (u : prod (prod A B) C) : C ≔ match u [ pair. (pair. x x) x ↦ x ]'
   ￫ error[E1304]
   ￭ command-line exec string
   1 | def proj1 (A B C : Type) (u : prod (prod A B) C) : C ≔ match u [ pair. (pair. x x) x ↦ x ]
     ^ variable name 'x' used more than once in match patterns
  
  [1]

  $ narya -e 'def prod (A B : Type) : Type ≔ data [ pair. (_:A) (_:B) ]' -e 'def proj1 (A B : Type) (u : prod A B) : A ≔ match u return _ ↦ A [ pair. x x ↦ x ]'
   ￫ error[E1304]
   ￭ command-line exec string
   1 | def proj1 (A B : Type) (u : prod A B) : A ≔ match u return _ ↦ A [ pair. x x ↦ x ]
     ^ variable name 'x' used more than once in match patterns
  
  [1]

  $ narya -e 'def bool : Type ≔ data [ true. | false. ]' -e 'def foo : bool → bool → bool ≔ [ ]'
   ￫ error[E1300]
   ￭ command-line exec string
   1 | def foo : bool → bool → bool ≔ [ ]
     ^ missing match clause for constructor true
  
  [1]

  $ narya -e 'def bool : Type ≔ data [ true. | false. ]' -e 'def foo : Type → bool → bool ≔ [ ]'
   ￫ error[E1200]
   ￭ command-line exec string
   1 | def foo : Type → bool → bool ≔ [ ]
     ^ can't match on variable belonging to non-datatype Type
  
  [1]
