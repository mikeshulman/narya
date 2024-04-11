  $ narya -v even_odd_rec.ny
   ￫ info[I0000]
   ￮ Constant ℕ defined
  
   ￫ info[I0000]
   ￮ Constant ⊤ defined
  
   ￫ info[I0000]
   ￮ Constant ⊥ defined
  
   ￫ info[I0000]
   ￮ Constant even_odd_type defined
  
   ￫ info[I0000]
   ￮ Constant even_odd defined
  
  ⊤
  
  ⊥
  

  $ narya -v even_odd_sig.ny
   ￫ info[I0000]
   ￮ Constant ℕ defined
  
   ￫ info[I0000]
   ￮ Constant even_odd_type defined
  
   ￫ info[I0000]
   ￮ Constant even_odd defined
  
   ￫ info[I0000]
   ￮ Constant even defined
  
   ￫ info[I0000]
   ￮ Constant odd defined
  
   ￫ info[I0000]
   ￮ Constant sum defined
  
   ￫ info[I0000]
   ￮ Constant even_or_odd_suc defined
  
   ￫ info[I0000]
   ￮ Constant all_even_or_odd defined
  

  $ narya -v even_odd_rec_canonical.ny
   ￫ info[I0000]
   ￮ Constant ℕ defined
  
   ￫ info[I0000]
   ￮ Constant even_odd_type defined
  
   ￫ info[I0000]
   ￮ Constant even_odd defined
  
  even_odd .even 8
  
  even_odd .odd 8
  


  $ narya -v ctx_ty_sig.ny
   ￫ info[I0000]
   ￮ Constant ctx_ty_type defined
  
   ￫ info[I0000]
   ￮ Constant ctx_ty defined
  
   ￫ info[I0000]
   ￮ Constant ctx_ty_tm_type defined
  
   ￫ info[I0000]
   ￮ Constant ctx_ty_tm defined
  

  $ narya -v univ_sig.ny
   ￫ info[I0000]
   ￮ Constant bool defined
  
   ￫ info[I0000]
   ￮ Constant uu_el_type defined
  
   ￫ info[I0000]
   ￮ Constant uu_el defined
  

  $ narya -v even_odd_and.ny
   ￫ info[I0000]
   ￮ Constant ℕ defined
  
   ￫ info[I0000]
   ￮ Constants defined mutually:
       even
       odd
  
   ￫ info[I0000]
   ￮ Constant sum defined
  
   ￫ info[I0000]
   ￮ Constant even_or_odd_suc defined
  
   ￫ info[I0000]
   ￮ Constant all_even_or_odd defined
  

  $ narya -v ctx_el_and.ny
   ￫ info[I0000]
   ￮ Constants defined mutually:
       ctx
       ty
  
   ￫ warning[E2100]
   ￮ redefining constant: ctx
  
   ￫ warning[E2100]
   ￮ redefining constant: ty
  
   ￫ info[I0000]
   ￮ Constants defined mutually:
       ctx
       ty
       tm
  

  $ narya -v univ_and.ny
   ￫ info[I0000]
   ￮ Constant bool defined
  
   ￫ info[I0000]
   ￮ Constants defined mutually:
       uu
       el
  

