{` A version of ctx_el_sig that uses mutual definition syntax. `}

def ctx : Type ≔ data [
| empty.
| ext. (Γ : ctx) (A : ty Γ)
]

and ty (Γ : ctx) : Type ≔ data [
| base.
| pi. (A : ty Γ) (B : ty (ext. Γ A))
]

def ctx : Type ≔ data [
| empty.
| ext. (Γ : ctx) (A : ty Γ)
]

and ty (Γ : ctx) : Type ≔ data [
| base.
| pi. (A : ty Γ) (B : ty (ext. Γ A))
| uu.
| el. (X : tm Γ uu.)
| sub. (A : ty Γ) (B : ty (ext. Γ A)) (a : tm Γ A)
]

and tm (Γ : ctx) : ty Γ → Type ≔ data [
| codebase. : tm Γ uu.
| lam. (A : ty Γ) (B : ty (ext. Γ A)) (b : tm (ext. Γ A) B) : tm Γ (pi. A B)
| app. (A : ty Γ) (B : ty (ext. Γ A)) (f : tm Γ (pi. A B)) (a : tm Γ A) : tm Γ (sub. A B a)
]
