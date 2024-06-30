Undo single command

  $ cat >undo.ny <<EOF
  > axiom A:Type
  > axiom a:A
  > echo a
  > undo 1
  > echo a
  > EOF

  $ narya -v -fake-interact undo.ny
   ￫ info[I0001]
   ￮ axiom A assumed
  
   ￫ info[I0001]
   ￮ axiom a assumed
  
  a
    : A
  
   ￫ info[I0006]
   ￮ 1 command undone
  
   ￫ error[E0300]
   ￭ undo.ny
   5 | echo a
     ^ unbound variable: a
  

Undo multiple commands

  $ cat >undo2.ny <<EOF
  > axiom A:Type
  > axiom a:A
  > axiom b:A
  > echo a
  > undo 2
  > echo a
  > EOF

  $ narya -v -fake-interact undo2.ny
   ￫ info[I0001]
   ￮ axiom A assumed
  
   ￫ info[I0001]
   ￮ axiom a assumed
  
   ￫ info[I0001]
   ￮ axiom b assumed
  
  a
    : A
  
   ￫ info[I0006]
   ￮ 2 commands undone
  
   ￫ error[E0300]
   ￭ undo2.ny
   6 | echo a
     ^ unbound variable: a
  

Undo nothing

  $ cat >no-undo.ny <<EOF
  > undo 1
  > EOF

  $ narya -v -fake-interact no-undo.ny
   ￫ error[E2500]
   ￮ not enough commands to undo
  

Undo notations

  $ cat >undo-notn.ny <<EOF
  > axiom A:Type
  > axiom a:A
  > axiom f : A -> A -> A
  > notation 1 f : x "+" y := f x y
  > echo a + a
  > undo 1
  > echo a + a
  > EOF

  $ narya -v -fake-interact undo-notn.ny
   ￫ info[I0001]
   ￮ axiom A assumed
  
   ￫ info[I0001]
   ￮ axiom a assumed
  
   ￫ info[I0001]
   ￮ axiom f assumed
  
   ￫ info[I0002]
   ￮ notation f defined
  
  a + a
    : A
  
   ￫ info[I0006]
   ￮ 1 command undone
  
  a
    : A
  
   ￫ error[E0200]
   ￭ undo-notn.ny
   7 | echo a + a
     ^ parse error
  
