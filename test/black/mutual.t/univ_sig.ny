def bool : Type ≔ data [ true. | false. ]

` We can define an inductive-recursive universe as well.  Here is the type of it and its recursive eliminator.
def uu_el_type : Type ≔ sig (
  uu : Type,
  el : uu → Type,
)

` And now here are their definitions.
def uu_el : uu_el_type ≔ (
  uu ≔ data [
  | bool.
  | pi. (A : uu_el .uu) (B : uu_el .el A → uu_el .uu)
  ],
  el ≔ [
  | bool. ↦ bool
  | pi. A B ↦ (x : uu_el .el A) → uu_el .el (B x)
  ],
)
