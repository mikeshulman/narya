  $ cat >multierr.ny <<EOF
  > axiom A:Type
  > axiom B:Type
  > axiom C:Type
  > axiom a:A
  > def prod (X Y : Type) : Type := sig (fst:X, snd:Y)
  > def foo : prod B C := (a,a)
  > EOF

  $ narya -v multierr.ny
   ￫ info[I0001]
   ￮ axiom A assumed
  
   ￫ info[I0001]
   ￮ axiom B assumed
  
   ￫ info[I0001]
   ￮ axiom C assumed
  
   ￫ info[I0001]
   ￮ axiom a assumed
  
   ￫ info[I0000]
   ￮ constant prod defined
  
   ￫ error[E0401]
   ￭ $TESTCASE_ROOT/multierr.ny
   6 | def foo : prod B C := (a,a)
     ^ term synthesized type A but is being checked against type B
  
   ￫ error[E0401]
   ￭ $TESTCASE_ROOT/multierr.ny
   6 | def foo : prod B C := (a,a)
     ^ term synthesized type A but is being checked against type C
  
  [1]

  $ cat >multierr.ny <<EOF
  > axiom A:Type
  > axiom B:Type
  > axiom C:Type
  > axiom a:A
  > axiom c:C
  > def prod (X Y : Type) : Type := sig (fst:X, snd:Y)
  > def foo : prod B C := (a,c)
  > EOF

  $ narya -v multierr.ny
   ￫ info[I0001]
   ￮ axiom A assumed
  
   ￫ info[I0001]
   ￮ axiom B assumed
  
   ￫ info[I0001]
   ￮ axiom C assumed
  
   ￫ info[I0001]
   ￮ axiom a assumed
  
   ￫ info[I0001]
   ￮ axiom c assumed
  
   ￫ info[I0000]
   ￮ constant prod defined
  
   ￫ error[E0401]
   ￭ $TESTCASE_ROOT/multierr.ny
   7 | def foo : prod B C := (a,c)
     ^ term synthesized type A but is being checked against type B
  
  [1]


  $ cat >multierr.ny <<EOF
  > axiom A:Type
  > axiom B:Type
  > axiom C:Type
  > axiom a:A
  > def prod (X Y : Type) : Type := sig (fst:X, snd:Y)
  > def foo : prod (prod B C) (prod C B) := ((a,a),(a,a))
  > EOF

  $ narya -v multierr.ny
   ￫ info[I0001]
   ￮ axiom A assumed
  
   ￫ info[I0001]
   ￮ axiom B assumed
  
   ￫ info[I0001]
   ￮ axiom C assumed
  
   ￫ info[I0001]
   ￮ axiom a assumed
  
   ￫ info[I0000]
   ￮ constant prod defined
  
   ￫ error[E0401]
   ￭ $TESTCASE_ROOT/multierr.ny
   6 | def foo : prod (prod B C) (prod C B) := ((a,a),(a,a))
     ^ term synthesized type A but is being checked against type B
  
   ￫ error[E0401]
   ￭ $TESTCASE_ROOT/multierr.ny
   6 | def foo : prod (prod B C) (prod C B) := ((a,a),(a,a))
     ^ term synthesized type A but is being checked against type C
  
   ￫ error[E0401]
   ￭ $TESTCASE_ROOT/multierr.ny
   6 | def foo : prod (prod B C) (prod C B) := ((a,a),(a,a))
     ^ term synthesized type A but is being checked against type C
  
   ￫ error[E0401]
   ￭ $TESTCASE_ROOT/multierr.ny
   6 | def foo : prod (prod B C) (prod C B) := ((a,a),(a,a))
     ^ term synthesized type A but is being checked against type B
  
  [1]

  $ cat >multierr.ny <<EOF
  > axiom A:Type
  > axiom B:Type
  > axiom P:B->Type
  > axiom a:A
  > def Sigma (X : Type) (Y : X -> Type) : Type := sig (fst:X, snd:Y fst)
  > def foo : Sigma B P := (a,a)
  > EOF

  $ narya -v multierr.ny
   ￫ info[I0001]
   ￮ axiom A assumed
  
   ￫ info[I0001]
   ￮ axiom B assumed
  
   ￫ info[I0001]
   ￮ axiom P assumed
  
   ￫ info[I0001]
   ￮ axiom a assumed
  
   ￫ info[I0000]
   ￮ constant Sigma defined
  
   ￫ error[E0401]
   ￭ $TESTCASE_ROOT/multierr.ny
   6 | def foo : Sigma B P := (a,a)
     ^ term synthesized type A but is being checked against type B
  
  [1]

  $ cat >multierr.ny <<EOF
  > axiom A:Type
  > axiom B:Type
  > axiom a:A
  > def bool : Type := data [ true. | false. ]
  > def P : bool -> Type := [ true. |-> A | false. |-> B ]
  > def Sigma (X : Type) (Y : X -> Type) : Type := sig (fst:X, snd:Y fst)
  > def foo : Sigma bool P := (a, a)
  > EOF

  $ narya -v multierr.ny
   ￫ info[I0001]
   ￮ axiom A assumed
  
   ￫ info[I0001]
   ￮ axiom B assumed
  
   ￫ info[I0001]
   ￮ axiom a assumed
  
   ￫ info[I0000]
   ￮ constant bool defined
  
   ￫ info[I0000]
   ￮ constant P defined
  
   ￫ info[I0000]
   ￮ constant Sigma defined
  
   ￫ error[E0401]
   ￭ $TESTCASE_ROOT/multierr.ny
   7 | def foo : Sigma bool P := (a, a)
     ^ term synthesized type A but is being checked against type bool
  
  [1]

Even trivial dependency blocks going on, as long as there is the potential for dependency.  Avoiding this would probably involve more laziness in function arguments.

  $ cat >multierr.ny <<EOF
  > axiom A:Type
  > axiom B:Type
  > axiom a:A
  > def Sigma (X : Type) (Y : X -> Type) : Type := sig (fst:X, snd:Y fst)
  > def foo : Sigma B (_ ↦ B) := (a, a)
  > EOF

  $ narya -v multierr.ny
   ￫ info[I0001]
   ￮ axiom A assumed
  
   ￫ info[I0001]
   ￮ axiom B assumed
  
   ￫ info[I0001]
   ￮ axiom a assumed
  
   ￫ info[I0000]
   ￮ constant Sigma defined
  
   ￫ error[E0401]
   ￭ $TESTCASE_ROOT/multierr.ny
   5 | def foo : Sigma B (_ ↦ B) := (a, a)
     ^ term synthesized type A but is being checked against type B
  
  [1]


  $ cat >multierr.ny <<EOF
  > axiom A:Type
  > axiom B:Type
  > axiom a:A
  > def streamB : Type := codata [ x .head : B | x .tail : streamB ]
  > def foo : streamB := [ .head ↦ a | .tail ↦ a ]
  > EOF

  $ narya -v multierr.ny
   ￫ info[I0001]
   ￮ axiom A assumed
  
   ￫ info[I0001]
   ￮ axiom B assumed
  
   ￫ info[I0001]
   ￮ axiom a assumed
  
   ￫ info[I0000]
   ￮ constant streamB defined
  
   ￫ error[E0401]
   ￭ $TESTCASE_ROOT/multierr.ny
   5 | def foo : streamB := [ .head ↦ a | .tail ↦ a ]
     ^ term synthesized type A but is being checked against type B
  
   ￫ error[E0401]
   ￭ $TESTCASE_ROOT/multierr.ny
   5 | def foo : streamB := [ .head ↦ a | .tail ↦ a ]
     ^ term synthesized type A but is being checked against type streamB
  
  [1]

  $ cat >multierr.ny <<EOF
  > axiom A:Type
  > axiom B:Type
  > axiom a:A
  > def streamB : Type := codata [ x .head : B | x .tail : streamB ]
  > def foo : B := let x : streamB := [ .head ↦ a | .tail ↦ a ] in x .head
  > EOF

  $ narya -v multierr.ny
   ￫ info[I0001]
   ￮ axiom A assumed
  
   ￫ info[I0001]
   ￮ axiom B assumed
  
   ￫ info[I0001]
   ￮ axiom a assumed
  
   ￫ info[I0000]
   ￮ constant streamB defined
  
   ￫ error[E0401]
   ￭ $TESTCASE_ROOT/multierr.ny
   5 | def foo : B := let x : streamB := [ .head ↦ a | .tail ↦ a ] in x .head
     ^ term synthesized type A but is being checked against type B
  
   ￫ error[E0401]
   ￭ $TESTCASE_ROOT/multierr.ny
   5 | def foo : B := let x : streamB := [ .head ↦ a | .tail ↦ a ] in x .head
     ^ term synthesized type A but is being checked against type streamB
  
  [1]

  $ cat >multierr.ny <<EOF
  > axiom A:Type
  > axiom B:Type
  > axiom a:A
  > def bool : Type := data [ true. | false. ]
  > def foo (x : bool) : B := match x [ true. ↦ a | false. ↦ a ]
  > EOF

  $ narya -v multierr.ny
   ￫ info[I0001]
   ￮ axiom A assumed
  
   ￫ info[I0001]
   ￮ axiom B assumed
  
   ￫ info[I0001]
   ￮ axiom a assumed
  
   ￫ info[I0000]
   ￮ constant bool defined
  
   ￫ error[E0401]
   ￭ $TESTCASE_ROOT/multierr.ny
   5 | def foo (x : bool) : B := match x [ true. ↦ a | false. ↦ a ]
     ^ term synthesized type A but is being checked against type B
  
   ￫ error[E0401]
   ￭ $TESTCASE_ROOT/multierr.ny
   5 | def foo (x : bool) : B := match x [ true. ↦ a | false. ↦ a ]
     ^ term synthesized type A but is being checked against type B
  
  [1]
