  $ cat >one.ny <<EOF
  > def A : Type ≔ Type
  > EOF

  $ cat >two.ny <<EOF
  > import "one"
  > def A : Type ≔ sig ()
  > EOF

  $ narya -v two.ny
   ￫ info[I0003]
   ￮ loading file: $TESTCASE_ROOT/one.ny
  
   ￫ info[I0000]
   ￮ constant A defined
  
   ￫ info[I0004]
   ￮ file loaded: $TESTCASE_ROOT/one.ny (source)
  
   ￫ error[E2100]
   ￭ $TESTCASE_ROOT/two.ny
   2 | def A : Type ≔ sig ()
     ^ name already defined: A
   ￭ $TESTCASE_ROOT/one.ny
   1 | def A : Type ≔ Type
     ^ previous definition
  
  [1]
