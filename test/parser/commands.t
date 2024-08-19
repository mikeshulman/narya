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

Redefining commands.

If the two strings are *identical*, then I think OCaml represents them
as the same object in memory, causing Asai to think they are the same
input source, producing a confusing message.  I think this is unlikely
to ever arise in practice, so it's not worth trying to fix; for our
test we just add some spaces to one of them to make them different.

  $ narya -e 'axiom A:Type' -e 'axiom A : Type'
   ￫ error[E2100]
   ￭ command-line exec string
   1 | axiom A : Type
     ^ name already defined: A
   ￭ command-line exec string
   1 | axiom A:Type
     ^ previous definition
  
  [1]
