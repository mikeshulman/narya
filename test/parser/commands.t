Testing parsing of commands, on the command line:

  $ narya -e 'axiom A : Type'

  $ narya -e 'axiom A : Type axiom a : A'

  $ narya -e 'def A : Type := Type'

  $ narya -e 'axiom A : Type' -e 'axiom a : A'

  $ narya -e 'axiom A : Type' -e 'def B : Type := A'

  $ narya -e 'axiom A : Type' -e 'echo A'
  A
    : Type
  

And in files:

  $ cat >test.ny <<EOF
  > axiom A:Type
  > axiom a:A
  > def B : Type := A
  > echo B
  > EOF

Now we run it:

  $ narya test.ny
  A
    : Type
  

Can we parse empty things?

  $ narya -e ''

  $ cat >test.ny <<EOF
  > EOF
  $ narya test.ny

Redefining commands

  $ narya -e 'axiom A:Type' -e 'axiom A:Type'
   ￫ warning[E2100]
   ￮ redefining constant: A
  
