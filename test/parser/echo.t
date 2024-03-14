  $ narya -e 'def f : Stream Nat := [  | .head |-> 0 | .tail |-> f ]' -e 'echo f'
  f
  

