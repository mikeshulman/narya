  $ narya -e 'def Stream (A:Type) : Type := codata [ _ .head : A | _ .tail : Stream A ]' -e 'def f : Stream Nat := [  | .head |-> 0 | .tail |-> f ]' -e 'echo f'
  f
  

