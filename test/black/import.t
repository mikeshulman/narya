Import files

  $ cat >one.ny <<EOF
  > axiom A : Type
  > EOF

  $ cat >two.ny <<EOF
  > import "one"
  > axiom a0 : A
  > EOF

  $ narya -source-only -v two.ny
   ￫ info[I0003]
   ￮ loading file: $TESTCASE_ROOT/one.ny
  
   ￫ info[I0001]
   ￮ axiom A assumed
  
   ￫ info[I0004]
   ￮ file loaded: $TESTCASE_ROOT/one.ny (source)
  
   ￫ info[I0001]
   ￮ axiom a0 assumed
  

Command-line strings see namespaces from explicitly loaded files only

  $ narya -source-only -v two.ny -e 'axiom a1 : A'
   ￫ info[I0003]
   ￮ loading file: $TESTCASE_ROOT/one.ny
  
   ￫ info[I0001]
   ￮ axiom A assumed
  
   ￫ info[I0004]
   ￮ file loaded: $TESTCASE_ROOT/one.ny (source)
  
   ￫ info[I0001]
   ￮ axiom a0 assumed
  
   ￫ error[E0300]
   ￭ command-line exec string
   1 | axiom a1 : A
     ^ unbound variable: A
  
  [1]

  $ narya -source-only -v one.ny -e 'axiom a1 : A'
   ￫ info[I0001]
   ￮ axiom A assumed
  
   ￫ info[I0001]
   ￮ axiom a1 assumed
  

Unless we explicitly export them:

  $ cat >etwo.ny <<EOF
  > export "one"
  > axiom a0 : A
  > EOF

  $ narya -source-only -v etwo.ny -e 'axiom a1 : A'
   ￫ info[I0003]
   ￮ loading file: $TESTCASE_ROOT/one.ny
  
   ￫ info[I0001]
   ￮ axiom A assumed
  
   ￫ info[I0004]
   ￮ file loaded: $TESTCASE_ROOT/one.ny (source)
  
   ￫ info[I0001]
   ￮ axiom a0 assumed
  
   ￫ info[I0001]
   ￮ axiom a1 assumed
  


Requiring a file multiple times

  $ cat >three.ny <<EOF
  > import "one"
  > axiom a1 : A
  > EOF

  $ cat >twothree.ny <<EOF
  > import "two"
  > import "three"
  > axiom a2 : Id A a0 a1

  $ narya -source-only -v twothree.ny
   ￫ info[I0003]
   ￮ loading file: $TESTCASE_ROOT/two.ny
  
   ￫ info[I0003]
   ￮ loading file: $TESTCASE_ROOT/one.ny
  
   ￫ info[I0001]
   ￮ axiom A assumed
  
   ￫ info[I0004]
   ￮ file loaded: $TESTCASE_ROOT/one.ny (source)
  
   ￫ info[I0001]
   ￮ axiom a0 assumed
  
   ￫ info[I0004]
   ￮ file loaded: $TESTCASE_ROOT/two.ny (source)
  
   ￫ info[I0003]
   ￮ loading file: $TESTCASE_ROOT/three.ny
  
   ￫ info[I0001]
   ￮ axiom a1 assumed
  
   ￫ info[I0004]
   ￮ file loaded: $TESTCASE_ROOT/three.ny (source)
  
   ￫ error[E0300]
   ￭ $TESTCASE_ROOT/twothree.ny
   3 | axiom a2 : Id A a0 a1
     ^ unbound variable: A
  
  [1]

  $ cat >four.ny <<EOF
  > import "one"
  > import "two"
  > import "three"
  > axiom a2 : Id A a0 a1

  $ narya -source-only -v four.ny
   ￫ info[I0003]
   ￮ loading file: $TESTCASE_ROOT/one.ny
  
   ￫ info[I0001]
   ￮ axiom A assumed
  
   ￫ info[I0004]
   ￮ file loaded: $TESTCASE_ROOT/one.ny (source)
  
   ￫ info[I0003]
   ￮ loading file: $TESTCASE_ROOT/two.ny
  
   ￫ info[I0001]
   ￮ axiom a0 assumed
  
   ￫ info[I0004]
   ￮ file loaded: $TESTCASE_ROOT/two.ny (source)
  
   ￫ info[I0003]
   ￮ loading file: $TESTCASE_ROOT/three.ny
  
   ￫ info[I0001]
   ￮ axiom a1 assumed
  
   ￫ info[I0004]
   ￮ file loaded: $TESTCASE_ROOT/three.ny (source)
  
   ￫ info[I0001]
   ￮ axiom a2 assumed
  

Circular dependency

  $ cat >foo.ny <<EOF
  > import "bar"
  > EOF

  $ cat >bar.ny <<EOF
  > import "foo"
  > EOF

  $ narya -source-only foo.ny
   ￫ error[E2300]
   ￮ circular imports:
     $TESTCASE_ROOT/foo.ny
       imports $TESTCASE_ROOT/bar.ny
       imports $TESTCASE_ROOT/foo.ny
  
  [1]

Import is relative to the file's directory

  $ mkdir subdir

  $ cat >subdir/one.ny <<EOF
  > axiom A:Type
  > EOF

  $ cat >subdir/two.ny <<EOF
  > import "one"
  > axiom a : A
  > EOF

  $ narya -source-only -v -e 'import "subdir/two"'
   ￫ info[I0003]
   ￮ loading file: $TESTCASE_ROOT/subdir/two.ny
  
   ￫ info[I0003]
   ￮ loading file: $TESTCASE_ROOT/subdir/one.ny
  
   ￫ info[I0001]
   ￮ axiom A assumed
  
   ￫ info[I0004]
   ￮ file loaded: $TESTCASE_ROOT/subdir/one.ny (source)
  
   ￫ info[I0001]
   ￮ axiom a assumed
  
   ￫ info[I0004]
   ￮ file loaded: $TESTCASE_ROOT/subdir/two.ny (source)
  

A file isn't loaded twice even if referred to in different ways

  $ narya -source-only -v subdir/one.ny -e 'import "subdir/two"'
   ￫ info[I0001]
   ￮ axiom A assumed
  
   ￫ info[I0003]
   ￮ loading file: $TESTCASE_ROOT/subdir/two.ny
  
   ￫ info[I0001]
   ￮ axiom a assumed
  
   ￫ info[I0004]
   ￮ file loaded: $TESTCASE_ROOT/subdir/two.ny (source)
  

Notations are used from explicitly imported files, but not transitively.

  $ cat >n1.ny <<EOF
  > axiom A:Type
  > axiom f : A -> A -> A
  > axiom a:A
  > EOF

  $ cat >n2.ny <<EOF
  > import "n1"
  > notation 0 f : x "&" y := f x y
  > EOF

  $ cat >n3.ny <<EOF
  > import "n1"
  > import "n2"
  > notation 0 f2 : x "%" y := f x y
  > EOF

  $ narya -source-only n1.ny n3.ny -e 'echo a % a'
   ￫ warning[E2209]
   ￮ replacing printing notation for f (previous notation will still be parseable)
  
  a % a
    : A
  

  $ narya -source-only n1.ny n3.ny -e 'echo a & a'
   ￫ warning[E2209]
   ￮ replacing printing notation for f (previous notation will still be parseable)
  
  a
    : A
  
   ￫ error[E0200]
   ￭ command-line exec string
   1 | echo a & a
     ^ parse error
  
  [1]

  $ cat >n4.ny <<EOF
  > import "n1"
  > import "n3"
  > echo a % a
  > EOF

  $ narya -source-only n4.ny
   ￫ warning[E2209]
   ￮ replacing printing notation for f (previous notation will still be parseable)
  
  a % a
    : A
  

Quitting in imports quits only that file

  $ cat >qone.ny <<EOF
  > axiom A : Type
  > quit
  > axiom B : Type
  > EOF

  $ cat >qtwo.ny <<EOF
  > import "qone"
  > axiom a0 : A
  > EOF

  $ narya -source-only -v qtwo.ny
   ￫ info[I0003]
   ￮ loading file: $TESTCASE_ROOT/qone.ny
  
   ￫ info[I0001]
   ￮ axiom A assumed
  
   ￫ info[I0200]
   ￮ execution of $TESTCASE_ROOT/qone.ny terminated by quit
  
   ￫ info[I0004]
   ￮ file loaded: $TESTCASE_ROOT/qone.ny (source)
  
   ￫ info[I0001]
   ￮ axiom a0 assumed
  

Definitions are linked

  $ cat >lone.ny <<EOF
  > def Nat : Type := data [ zero. | suc. (_:Nat) ]
  > EOF

  $ cat >ltwo.ny <<EOF
  > import "lone"
  > def foo (n : Nat) : Type := match n [ zero. ↦ Nat | suc. n ↦ Nat ]
  > EOF

  $ narya -v lone.ny
   ￫ info[I0000]
   ￮ constant Nat defined
  

  $ narya -v ltwo.ny
   ￫ info[I0004]
   ￮ file loaded: $TESTCASE_ROOT/lone.ny (compiled)
  
   ￫ info[I0000]
   ￮ constant foo defined
  

Undoing and redoing an import

  $ cat >undoimport.ny <<EOF
  > import "one"
  > undo 1
  > import "one"
  > axiom a:A
  > EOF

  $ narya -fake-interact undoimport.ny
   ￫ info[I0004]
   ￮ file loaded: $TESTCASE_ROOT/one.ny (compiled)
  
   ￫ info[I0006]
   ￮ 1 command undone
  
   ￫ info[I0001]
   ￮ axiom a assumed
  
Importing after creating a hole

  $ rm one.nyo

  $ cat >importhole.ny <<EOF
  > def Z : Type := ?
  > import "one"
  > def W : Type := Z
  > EOF

  $ narya -v importhole.ny
   ￫ info[I0000]
   ￮ constant Z defined, containing 1 hole
  
   ￫ info[I3003]
   ￮ hole ?0:
     
     ----------------------------------------------------------------------
     Type
  
   ￫ info[I0003]
   ￮ loading file: $TESTCASE_ROOT/one.ny
  
   ￫ info[I0001]
   ￮ axiom A assumed
  
   ￫ info[I0004]
   ￮ file loaded: $TESTCASE_ROOT/one.ny (source)
  
   ￫ info[I0000]
   ￮ constant W defined
  
   ￫ error[E3002]
   ￮ file importhole.ny contains open holes
  
  [1]
