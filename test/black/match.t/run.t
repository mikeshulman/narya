  $ narya -v matchterm.ny
   ￫ info[I0000]
   ￮ Constant ℕ defined
  
   ￫ info[I0000]
   ￮ Constant plus defined
  
   ￫ info[I0000]
   ￮ Constant bool defined
  
   ￫ info[I0000]
   ￮ Constant plus_is_1 defined
  
  true.
    : bool
  
  false.
    : bool
  
  true.
    : bool
  
  false.
    : bool
  
  false.
    : bool
  
   ￫ info[I0000]
   ￮ Constant ⊥ defined
  
   ￫ info[I0000]
   ￮ Constant contra defined
  
   ￫ hint[E1101]
   ￭ matchterm.ny
   12 | def doublematch (n : ℕ) : bool ≔ match n [ zero. ↦ false. | suc. k ↦ match n [ zero. ↦ true. | suc. _ ↦ false. ]]
      ^ match will not refine the goal or context (discriminee is let-bound): n
  
   ￫ info[I0000]
   ￮ Constant doublematch defined
  
   ￫ info[I0000]
   ￮ Constant doublematch' defined
  
   ￫ info[I0000]
   ￮ Constant ⊤ defined
  
   ￫ info[I0000]
   ￮ Constant zero_or_suc defined
  
   ￫ info[I0000]
   ￮ Constant plus_zero_or_suc defined
  
   ￫ info[I0000]
   ￮ Constant Vec defined
  
   ￫ info[I0000]
   ￮ Constant idvec defined
  
   ￫ info[I0000]
   ￮ Constant nil_or_cons defined
  
   ￫ info[I0000]
   ￮ Constant idvec_nil_or_cons defined
  
