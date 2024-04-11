def bool : Type ≔ data [ true. | false. ]

{` A version of univ_sig that uses mutual syntax. `}

def uu : Type ≔ data [
| bool.
| pi. (A : uu) (B : el A → uu)
]

and el : uu → Type ≔ [
| bool. ↦ bool
| pi. A B ↦ (x : el A) → el (B x)
]
