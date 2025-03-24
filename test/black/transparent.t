Transparency and translucency

  $ narya - <<EOF
  > axiom A : Type
  > axiom a : A
  > axiom B : Type
  > axiom b : B
  > def prod1 : Type ≔ sig ( fst : A, snd : B)
  > axiom x1 : prod1
  > echo x1
  > def y1 : prod1 ≔ (a,b)
  > echo y1
  > def prod2a : Type ≔ sig #(transparent) ( fst : A, snd : B)
  > axiom x2a : prod2a
  > echo x2a
  > def y2a : prod2a ≔ (a,b)
  > echo y2a
  > def prod2b : Type ≔ sig #(transparent positional) ( fst : A, snd : B)
  > axiom x2b : prod2b
  > echo x2b
  > def y2b : prod2b ≔ (a,b)
  > echo y2b
  > def prod3a : Type ≔ sig #(translucent) ( fst : A, snd : B)
  > axiom x3a : prod3a
  > echo x3a
  > def y3a : prod3a ≔ (a,b)
  > echo y3a
  > def prod3b : Type ≔ sig #(translucent positional) ( fst : A, snd : B)
  > axiom x3b : prod3b
  > echo x3b
  > def y3b : prod3b ≔ (a,b)
  > echo y3b
  x1
    : prod1
  
  y1
    : prod1
  
  (fst ≔ x2a .fst, snd ≔ x2a .snd)
    : prod2a
  
  (fst ≔ a, snd ≔ b)
    : prod2a
  
  (x2b .fst, x2b .snd)
    : prod2b
  
  (a, b)
    : prod2b
  
  x3a
    : prod3a
  
  (fst ≔ a, snd ≔ b)
    : prod3a
  
  x3b
    : prod3b
  
  (a, b)
    : prod3b
  
