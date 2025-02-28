  $ cat - >display.ny <<EOF
  > echo Type -> Type
  > display chars ≔ ascii
  > echo Type -> Type
  > display chars ≔ unicode
  > echo Type -> Type
  > EOF

  $ narya -fake-interact=display.ny
  Type → Type
    : Type
  
   ￫ info[I0101]
   ￮ display set chars to ASCII
  
  Type -> Type
    : Type
  
   ￫ info[I0101]
   ￮ display set chars to unicode
  
  Type → Type
    : Type
  
