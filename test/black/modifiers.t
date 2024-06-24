  $ cat >nat.ny <<EOF
  > def Nat : Type := data [ zero. | suc. (_:Nat) ]
  > def myzero : Nat := zero.
  > def myone : Nat := suc. zero.
  > def nums.two : Nat := suc. (suc. zero.)
  > def nums.three : Nat := suc. (suc. (suc. zero.))
  > def plus (x y : Nat) : Nat := match y [ zero. ↦ x | suc. y ↦ suc. (plus x y) ]
  > def times (x y : Nat) : Nat := match y [ zero. ↦ zero. | suc. y ↦ plus (times x y) x ]
  > def minus (x y : Nat) : Nat := match y, x [ zero., x ↦ x | suc. y, suc. x ↦ minus x y | suc. _, zero. ↦ y ]
  > notation 5 plus : x "+" y ≔ plus x y
  > notation 6 times : x "*" y ≔ times x y
  > notation 5 minus : x "-" y ≔ minus x y
  > EOF

Renaming individual imports

  $ narya -e 'import "nat" | renaming myone yourone echo yourone'
  1
    : Nat
  

Renaming a whole subtree, clobbering the rest

  $ narya -e 'import "nat" | renaming nums . echo two'
  2
    : _UNNAMED_CONSTANT
  
Renaming a subtree while preserving the rest

  $ narya -e 'import "nat" | union (id, renaming nums .) echo two'
  2
    : Nat
  
Excluding a subtree

  $ narya -e 'import "nat" | except nums echo myone echo two'
  1
    : Nat
  
   ￫ error[E0300]
   ￭ command-line exec string
   1 | import "nat" | except nums echo myone echo two
     ^ unbound variable: two
  
  [1]

Renaming everything (i.e. import qualified)

  $ narya -e 'import "nat" | renaming . nat echo nat.myzero echo nat.nums.three'
  0
    : nat.Nat
  
  3
    : nat.Nat
  
We get notations if we keep the main subtree

  $ narya -e 'import "nat" | renaming myone yourone echo 1 + 1'
  2
    : Nat
  
We can get only the notations by keeping only that subtree

  $ narya -e 'import "nat" | only notations echo 1 + 1'
  2
    : _UNNAMED_CONSTANT
  

Or exclude the notations but get everything else

  $ narya -e 'import "nat" | except notations echo myzero echo 1 + 1'
  0
    : Nat
  
   ￫ error[E0400]
   ￮ non-synthesizing term in synthesizing position (argument of echo)
  
  [1]

Or import some of the notations but not others

  $ narya -e 'import "nat" | in notations union (only plus, only times) echo 1+1 echo 1*1 echo (1-1 : Nat)'
  2
    : Nat
  
  1
    : Nat
  
   ￫ error[E0200]
   ￭ command-line exec string
   1 | import "nat" | in notations union (only plus, only times) echo 1+1 echo 1*1 echo (1-1 : Nat)
     ^ parse error
  
  [1]

We can also import from a namespace rather than a file.

  $ narya -e 'axiom a.b : Type axiom a.c : Type import a echo b'
  a.b
    : Type
  

  $ narya -e 'axiom a.b : Type axiom a.c : Type import a | renaming b d echo d'
  a.b
    : Type
  

But this doesn't affect the export namespace:

  $ cat >importns.ny <<EOF
  > axiom a.b : Type
  > axiom a.c : Type
  > import a
  > echo b
  > EOF

  $ narya importns.ny -e 'echo a.b echo b'
  a.b
    : Type
  
  a.b
    : Type
  
   ￫ error[E0300]
   ￭ command-line exec string
   1 | echo a.b echo b
     ^ unbound variable: b
  
  [1]

Unless we tell it to:

  $ cat >exportns.ny <<EOF
  > axiom a.b : Type
  > axiom a.c : Type
  > export a
  > echo b
  > EOF

  $ narya exportns.ny -e 'echo a.b echo b'
  a.b
    : Type
  
  a.b
    : Type
  
  a.b
    : Type
  
