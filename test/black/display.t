  $ cat - >display.ny <<EOF
  > echo Type -> Type
  > display ascii
  > echo Type -> Type
  > display unicode
  > echo Type -> Type
  > EOF

  $ narya -fake-interact=display.ny
  Type → Type
    : Type
  
   ￫ info[I0100]
   ￮ display set: ASCII
  
  Type -> Type
    : Type
  
   ￫ info[I0100]
   ￮ display set: unicode
  
  Type → Type
    : Type
  
