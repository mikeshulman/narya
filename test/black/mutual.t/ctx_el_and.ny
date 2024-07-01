{` A version of ctx_el_sig that uses mutual definition syntax. `}

def ctx : Type ≔ data [
| empty.
| ext. (Γ : ctx) (A : ty Γ)
]

and ty (Γ : ctx) : Type ≔ data [
| base.
| pi. (A : ty Γ) (B : ty (ext. Γ A))
]
