Require files

  $ cat >one.ny <<EOF
  > axiom A : Type
  > EOF

  $ cat >two.ny <<EOF
  > require "one.ny"
  > axiom a0 : A
  > EOF

  $ narya -v two.ny
   ￫ info[I0003]
   ￮ loading file: $TESTCASE_ROOT/one.ny
  
   ￫ info[I0001]
   ￮ Axiom A assumed
  
   ￫ info[I0004]
   ￮ file loaded: $TESTCASE_ROOT/one.ny
  
   ￫ info[I0001]
   ￮ Axiom a0 assumed
  

Command-line strings see namespaces from explicitly loaded files only

  $ narya -v two.ny -e 'axiom a1 : A'
   ￫ info[I0003]
   ￮ loading file: $TESTCASE_ROOT/one.ny
  
   ￫ info[I0001]
   ￮ Axiom A assumed
  
   ￫ info[I0004]
   ￮ file loaded: $TESTCASE_ROOT/one.ny
  
   ￫ info[I0001]
   ￮ Axiom a0 assumed
  
   ￫ error[E0300]
   ￭ command-line exec string
   1 | axiom a1 : A
     ^ unbound variable: A
  
  [1]

  $ narya -v one.ny -e 'axiom a1 : A'
   ￫ info[I0001]
   ￮ Axiom A assumed
  
   ￫ info[I0001]
   ￮ Axiom a1 assumed
  

Requiring a file multiple times

  $ cat >three.ny <<EOF
  > require "one.ny"
  > axiom a1 : A
  > EOF

  $ cat >twothree.ny <<EOF
  > require "two.ny"
  > require "three.ny"
  > axiom a2 : Id A a0 a1

  $ narya -v twothree.ny
   ￫ info[I0003]
   ￮ loading file: $TESTCASE_ROOT/two.ny
  
   ￫ info[I0003]
   ￮ loading file: $TESTCASE_ROOT/one.ny
  
   ￫ info[I0001]
   ￮ Axiom A assumed
  
   ￫ info[I0004]
   ￮ file loaded: $TESTCASE_ROOT/one.ny
  
   ￫ info[I0001]
   ￮ Axiom a0 assumed
  
   ￫ info[I0004]
   ￮ file loaded: $TESTCASE_ROOT/two.ny
  
   ￫ info[I0003]
   ￮ loading file: $TESTCASE_ROOT/three.ny
  
   ￫ info[I0001]
   ￮ Axiom a1 assumed
  
   ￫ info[I0004]
   ￮ file loaded: $TESTCASE_ROOT/three.ny
  
   ￫ error[E0300]
   ￭ twothree.ny
   3 | axiom a2 : Id A a0 a1
     ^ unbound variable: A
  
  [1]

  $ cat >four.ny <<EOF
  > require "one.ny"
  > require "two.ny"
  > require "three.ny"
  > axiom a2 : Id A a0 a1

  $ narya -v four.ny
   ￫ info[I0003]
   ￮ loading file: $TESTCASE_ROOT/one.ny
  
   ￫ info[I0001]
   ￮ Axiom A assumed
  
   ￫ info[I0004]
   ￮ file loaded: $TESTCASE_ROOT/one.ny
  
   ￫ info[I0003]
   ￮ loading file: $TESTCASE_ROOT/two.ny
  
   ￫ info[I0001]
   ￮ Axiom a0 assumed
  
   ￫ info[I0004]
   ￮ file loaded: $TESTCASE_ROOT/two.ny
  
   ￫ info[I0003]
   ￮ loading file: $TESTCASE_ROOT/three.ny
  
   ￫ info[I0001]
   ￮ Axiom a1 assumed
  
   ￫ info[I0004]
   ￮ file loaded: $TESTCASE_ROOT/three.ny
  
   ￫ info[I0001]
   ￮ Axiom a2 assumed
  

Circular dependency

  $ cat >foo.ny <<EOF
  > require "bar.ny"
  > EOF

  $ cat >bar.ny <<EOF
  > require "foo.ny"
  > EOF

  $ narya foo.ny
   ￫ error[E2300]
   ￮ circular dependency:
     $TESTCASE_ROOT/foo.ny
       requires $TESTCASE_ROOT/bar.ny
       requires $TESTCASE_ROOT/foo.ny
  
  [1]

Require is relative to the file's directory

  $ mkdir subdir

  $ cat >subdir/one.ny <<EOF
  > axiom A:Type
  > EOF

  $ cat >subdir/two.ny <<EOF
  > require "one.ny"
  > axiom a : A
  > EOF

  $ narya -v -e 'require "subdir/two.ny"'
   ￫ info[I0003]
   ￮ loading file: $TESTCASE_ROOT/subdir/two.ny
  
   ￫ info[I0003]
   ￮ loading file: $TESTCASE_ROOT/subdir/one.ny
  
   ￫ info[I0001]
   ￮ Axiom A assumed
  
   ￫ info[I0004]
   ￮ file loaded: $TESTCASE_ROOT/subdir/one.ny
  
   ￫ info[I0001]
   ￮ Axiom a assumed
  
   ￫ info[I0004]
   ￮ file loaded: $TESTCASE_ROOT/subdir/two.ny
  

A file isn't loaded twice even if referred to in different ways

  $ narya -v subdir/one.ny -e 'require "subdir/two.ny"'
   ￫ info[I0001]
   ￮ Axiom A assumed
  
   ￫ info[I0003]
   ￮ loading file: $TESTCASE_ROOT/subdir/two.ny
  
   ￫ info[I0001]
   ￮ Axiom a assumed
  
   ￫ info[I0004]
   ￮ file loaded: $TESTCASE_ROOT/subdir/two.ny
  