  $ narya -v even_odd_rec.ny
   ￫ info[I0000]
   ￮ constant ℕ defined
  
   ￫ info[I0000]
   ￮ constant ⊤ defined
  
   ￫ info[I0000]
   ￮ constant ⊥ defined
  
   ￫ info[I0000]
   ￮ constant even_odd_type defined
  
   ￫ info[I0000]
   ￮ constant even_odd defined
  
  ⊤
    : Type
  
  ⊥
    : Type
  

  $ narya -v even_odd_sig.ny
   ￫ info[I0000]
   ￮ constant ℕ defined
  
   ￫ info[I0000]
   ￮ constant even_odd_type defined
  
   ￫ info[I0000]
   ￮ constant even_odd defined
  
   ￫ info[I0000]
   ￮ constant even defined
  
   ￫ info[I0000]
   ￮ constant odd defined
  
   ￫ info[I0000]
   ￮ constant sum defined
  
   ￫ info[I0000]
   ￮ constant even_or_odd_suc defined
  
   ￫ info[I0000]
   ￮ constant all_even_or_odd defined
  

  $ narya -v even_odd_rec_canonical.ny
   ￫ info[I0000]
   ￮ constant ℕ defined
  
   ￫ info[I0000]
   ￮ constant even_odd_type defined
  
   ￫ info[I0000]
   ￮ constant even_odd defined
  
  even_odd .even 8
    : Type
  
  even_odd .odd 8
    : Type
  


  $ narya -v ctx_ty_sig.ny
   ￫ info[I0000]
   ￮ constant ctx_ty_type defined
  
   ￫ info[I0000]
   ￮ constant ctx_ty defined
  
   ￫ info[I0000]
   ￮ constant ctx_ty_tm_type defined
  
   ￫ info[I0000]
   ￮ constant ctx_ty_tm defined
  

  $ narya -v univ_sig.ny
   ￫ info[I0000]
   ￮ constant bool defined
  
   ￫ info[I0000]
   ￮ constant uu_el_type defined
  
   ￫ info[I0000]
   ￮ constant uu_el defined
  

  $ narya -v even_odd_and.ny
   ￫ info[I0000]
   ￮ constant ℕ defined
  
   ￫ info[I0000]
   ￮ constants defined mutually:
       even
       odd
  
   ￫ info[I0000]
   ￮ constant sum defined
  
   ￫ info[I0000]
   ￮ constant even_or_odd_suc defined
  
   ￫ info[I0000]
   ￮ constant all_even_or_odd defined
  

  $ narya -v ctx_el_and.ny
   ￫ info[I0000]
   ￮ constants defined mutually:
       ctx
       ty
  
   ￫ warning[E2100]
   ￮ name already defined: ctx
  
   ￫ warning[E2100]
   ￮ name already defined: ty
  
   ￫ info[I0000]
   ￮ constants defined mutually:
       ctx
       ty
       tm
  

  $ narya -v univ_and.ny
   ￫ info[I0000]
   ￮ constant bool defined
  
   ￫ info[I0000]
   ￮ constants defined mutually:
       uu
       el
  

