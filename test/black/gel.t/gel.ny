def Gel (A B : Type) (R : A → B → Type) : Id Type A B ≔ sig a b ↦ ( ungel : R a b )

axiom A:Type
axiom B:Type
axiom R: A → B → Type
axiom a₀:A
axiom a₁:A
axiom a₂ : Id A a₀ a₁ 
axiom b₀ : B
axiom b₁ : B
axiom b₂ : Id B b₀ b₁
axiom r₀ : R a₀ b₀
axiom r₁ : R a₁ b₁

{` An intrinsic symmetry of a higher-dimensional Gel is no longer a record type `}
axiom M : (Gel A B R)⁽ᵉ¹⁾ a₀ b₀ (r₀,) a₁ b₁ (r₁,) a₂ b₂
echo sym M
{` But its terms can be symmetrized to end up in a record type `}
echo sym M .ungel

{` And it satisfies an eta-rule inherited from that record type `}
def eta : Id ((Gel A B R)⁽ᵉ¹⁾ a₀ b₀ (r₀,) a₁ b₁ (r₁,) a₂ b₂)
  M (sym (ungel ≔ sym M .ungel)) ≔ refl M
