  $ cat >wrap.ny <<EOF
  > axiom A:Type
  > axiom a:A
  > def wrapA : Type := sig ( unwrap : A)
  > def wa1 : wrapA := (unwrap := a)
  > def wa2 : wrapA := (_ := a)
  > def wa3 : wrapA := (a,)
  > def wa4 : wrapA := (a)
  > EOF

  $ narya -v wrap.ny
   ￫ info[I0001]
   ￮ Axiom A assumed
  
   ￫ info[I0001]
   ￮ Axiom a assumed
  
   ￫ info[I0000]
   ￮ Constant wrapA defined
  
   ￫ info[I0000]
   ￮ Constant wa1 defined
  
   ￫ info[I0000]
   ￮ Constant wa2 defined
  
   ￫ info[I0000]
   ￮ Constant wa3 defined
  
   ￫ error[E0401]
   ￭ $TESTCASE_ROOT/wrap.ny
   7 | def wa4 : wrapA := (a)
     ^ term synthesized type A but is being checked against type wrapA
  
  [1]
