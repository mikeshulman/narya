  $ cat >nat.ny <<EOF
  > def ℕ : Type := data [ zero. | suc. (_ : ℕ) ]
  > def O : ℕ := zero.
  > def S : ℕ → ℕ := n ↦ suc. n
  > def plus : ℕ → ℕ → ℕ := m n ↦ match n [ | zero. ↦ m | suc. n ↦ suc. (plus m n) ]
  > def times : ℕ → ℕ → ℕ := m n ↦ match n [ | zero. ↦ zero. | suc. n ↦ plus (times m n) m ]
  > notation 0 plus : m "+" n … ≔ plus m n
  > notation 1 times : m "*" n … ≔ times m n
  > echo (S O) + (S (S O)) + (S (S (S O)))
  > echo S (S O) * S (S O) + S (S O)
  > echo S (S O) * (S (S O) + S (S O))
  > def six : ℕ := 6
  > axiom m : ℕ
  > axiom n : ℕ
  > echo m+n
  > echo m+n*n
  > echo m*(m+n*n)
  > echo m + suc. n
  > echo (m+n)*(m+n)
  > echo n + n + n + n + n + n + n + n + n + n + n + n + n + n + n + n + n + n + n + n + n + n + n + n + n + n + n + n + n + n + n + n + n + n + n + n
  > echo n + n * n + n * n * n + n * n * n * n + n + n * n * n * n * n * n * n + n * n + n * n * n + n * n * n * n + n + n * n * n * n * n * n * n


  $ narya -v nat.ny
   ￫ info[I0000]
   ￮ Constant ℕ defined
  
   ￫ info[I0000]
   ￮ Constant O defined
  
   ￫ info[I0000]
   ￮ Constant S defined
  
   ￫ info[I0000]
   ￮ Constant plus defined
  
   ￫ info[I0000]
   ￮ Constant times defined
  
   ￫ info[I0002]
   ￮ Notation plus defined
  
   ￫ info[I0002]
   ￮ Notation times defined
  
  6
    : ℕ
  
  6
    : ℕ
  
  8
    : ℕ
  
   ￫ info[I0000]
   ￮ Constant six defined
  
   ￫ info[I0001]
   ￮ Axiom m assumed
  
   ￫ info[I0001]
   ￮ Axiom n assumed
  
  m + n
    : ℕ
  
  m + n * n
    : ℕ
  
  m * (m + n * n)
    : ℕ
  
  suc. (m + n)
    : ℕ
  
  (m + n) * (m + n)
    : ℕ
  
  n
  + n
  + n
  + n
  + n
  + n
  + n
  + n
  + n
  + n
  + n
  + n
  + n
  + n
  + n
  + n
  + n
  + n
  + n
  + n
  + n
  + n
  + n
  + n
  + n
  + n
  + n
  + n
  + n
  + n
  + n
  + n
  + n
  + n
  + n
  + n
  
    : ℕ
  
  n
  + n * n
  + n * n * n 
  + n * n * n * n 
  + n
  + n * n * n * n * n * n * n 
  + n * n
  + n * n * n 
  + n * n * n * n 
  + n
  + n * n * n * n * n * n * n 
  
    : ℕ
  
