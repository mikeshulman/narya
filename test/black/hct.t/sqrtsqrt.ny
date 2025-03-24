axiom A:Type

{` There are two ways of defining a double square root: directly with a 2-dimensional field, or by iterating ordinary square roots.  Here we prove that those are equivalent. `}

def √A : Type ≔ codata [
| x .r.e : A
]

def √√A : Type ≔ codata [
| x .rr.ee : A
]

def √_√A : Type ≔ codata [
| x .r_r.e : √A
]

def f (x : √√A) : √_√A ≔ [
| .r_r.e ↦ [
  | .r.e ↦ x.22 .rr.12
  ]
]

def g (x : √_√A) : √√A ≔ [
| .rr.ee ↦ x.22 .r_r.1 .r.1
]

{` This depends on the characterization of the identity types of higher coinductive types as other higher coinductive types. `}

def fg (x : √_√A) : Id √_√A (f (g x)) x ≔ [
| .r_r.1 ↦ refl x .r_r.1
| .r_r.e ↦ [
  | .r.1 ↦ refl x.2 .r_r.1 .r.1
  | .r.e ↦ refl (x.22 .r_r.1 .r.1)
  ]
]

def gf (x : √√A) : Id √√A (g (f x)) x ≔ [
| .rr.1e ↦ refl x.2 .rr.12
| .rr.e1 ↦ refl x.2 .rr.21
| .rr.ee ↦ refl (x.22 .rr.12)
]
