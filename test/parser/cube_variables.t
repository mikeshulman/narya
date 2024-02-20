Testing parsing and printing of cube variables

  $ cat >cube_vars.ny <<EOF
  > axiom A:Type
  > axiom B:Type
  > axiom b:B
  > def f : A -> B := x |-> b
  > def g (x:A) : B := b
  > def fg : Id (A -> B) f g := x0 x1 x2 |-> refl b
  > echo fg
  > echo refl fg
  > def fg' : Id (A -> B) f g := x |=> refl b
  > echo fg'
  > echo refl fg'
  > axiom a0:A
  > axiom a1:A
  > axiom a2:Id A a0 a1
  > echo refl f a0 a1 a2  

  $ narya cube_vars.ny
  x0 x1 x2 ↦ refl b
  
  x2 ⤇ b⁽⁰⁰⁾
  
  x ⤇ refl b
  
  x ⤇ b⁽⁰⁰⁾
  
  refl b
  
