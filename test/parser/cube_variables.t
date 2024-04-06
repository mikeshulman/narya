Testing parsing and printing of cube variables

  $ cat >cube_vars.ny <<EOF
  > axiom A:Type
  > axiom B:Type
  > axiom b:B
  > def f : A -> B := x |-> b
  > def g (x:A) : B := b
  > def fg : Id (A -> B) f g := x0 x1 x2 |-> refl b
  > echo (x0 x1 x2 |-> fg x0 x1 x2) : Id (A -> B) f g
  > echo (x00 x01 x02 x10 x11 x12 x20 x21 x22 |-> refl fg x00 x01 x02 x10 x11 x12 x20 x21 x22) : Id (Id (A -> B) f g) fg fg
  > echo (x |=> fg x.0 x.1 x.2) : Id (A -> B) f g
  > echo ((x |=> refl fg x.00 x.01 x.02 x.10 x.11 x.12 x.20 x.21 x.22) : Id (Id (A -> B) f g) fg fg)
  > axiom h (x:A) : Id B b b
  > def fgh : Id (A -> B) f g := x0 x1 x2 |-> h x0
  > echo (x0 x1 x2 |-> fgh x0 x1 x2) : Id (A -> B) f g
  > echo (x |=> fgh x.0 x.1 x.2) : Id (A -> B) f g
  > echo ((x |=> refl fgh x.00 x.01 x.02 x.10 x.11 x.12 x.20 x.21 x.22) : Id (Id (A -> B) f g) fgh fgh)
  > echo ((x |=> refl h x.00 x.01 x.02) : Id (Id (A -> B) f g) fgh fgh)
  > axiom a0:A
  > axiom a1:A
  > axiom a2:Id A a0 a1
  > echo refl f a0 a1 a2  

  $ narya cube_vars.ny
  x0 x1 x2 ↦ refl b
  
  x00 x01 x02 x10 x11 x12 x20 x21 x22 ↦ b⁽ᵉᵉ⁾
  
  x ⤇ refl b
  
  x ⤇ b⁽ᵉᵉ⁾
  
  x0 x1 x2 ↦ h x0
  
  x ⤇ h x.0
  
  x ⤇ refl h x.00 x.01 x.02
  
  x ⤇ refl h x.00 x.01 x.02
  
  refl b
  
