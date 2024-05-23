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
      ^ matching on let-bound variable n doesn't refine the type
  
   ￫ info[I0000]
   ￮ Constant doublematch defined
  
