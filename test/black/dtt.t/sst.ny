{` Unary Gel-types `}
def Gel (A : Type) (A' : A → Type) : Type⁽ᵈ⁾ A ≔ sig x ↦ (ungel : A' x)

{` The definition of semi-simplicial types `}
def SST : Type ≔ codata [
| X .z : Type
| X .s : (X .z) → SST⁽ᵈ⁾ X
]

` Extracting some low-dimensional simplices
def 0s (X : SST) : Type ≔ X .z

def 1s (X : SST) (x₀ x₁ : 0s X) : Type ≔ X .s x₀ .z x₁

def 2s (X : SST) (x₀ x₁ : 0s X) (x₀₁ : 1s X x₀ x₁) (x₂ : 0s X) (x₀₂ : 1s X x₀ x₂) (x₁₂ : 1s X x₁ x₂) : Type
  ≔ X .s x₀ .s x₁ x₀₁ .z x₂ x₀₂ x₁₂

def 3s (X : SST) (x₀ x₁ : 0s X) (x₀₁ : 1s X x₀ x₁) (x₂ : 0s X) (x₀₂ : 1s X x₀ x₂) (x₁₂ : 1s X x₁ x₂) (x₀₁₂ : 2s X x₀ x₁ x₀₁ x₂ x₀₂ x₁₂)
  (x₃ : 0s X) (x₀₃ : 1s X x₀ x₃) (x₁₃ : 1s X x₁ x₃) (x₀₁₃ : 2s X x₀ x₁ x₀₁ x₃ x₀₃ x₁₃)
  (x₂₃ : 1s X x₂ x₃) (x₀₂₃ : 2s X x₀ x₂ x₀₂ x₃ x₀₃ x₂₃) (x₁₂₃ : 2s X x₁ x₂ x₁₂ x₃ x₁₃ x₂₃)
  : Type
  ≔ X .s x₀ .s x₁ x₀₁ .s x₂ x₀₂ x₁₂ x₀₁₂ .z x₃ x₀₃ x₁₃ x₀₁₃ x₂₃ x₀₂₃ x₁₂₃

{` Singular SSTs, based on the Martin-Lof jdentity type for now. `}
def eq (A:Type) (x:A) : A → Type ≔ data [ rfl. : eq A x x ]

def Sing (A : Type) : SST ≔ [
| .z ↦ A
| .s ↦ x ↦ Sing⁽ᵈ⁾ A (Gel A (y ↦ eq A x y))
]

{` We normalize some low-dimensional simplex types of singular SSTs. `}
axiom A : Type
echo 0s (Sing A)

axiom a₀ : 0s (Sing A)
axiom a₁ : 0s (Sing A)
echo 1s (Sing A) a₀ a₁

axiom a₀₁ : 1s (Sing A) a₀ a₁
axiom a₂ : 0s (Sing A)
axiom a₀₂ : 1s (Sing A) a₀ a₂
axiom a₁₂ : 1s (Sing A) a₁ a₂
echo 2s (Sing A) a₀ a₁ a₀₁ a₂ a₀₂ a₁₂

axiom a₀₁₂ : 2s (Sing A) a₀ a₁ a₀₁ a₂ a₀₂ a₁₂
axiom a₃ : 0s (Sing A)
axiom a₀₃ : 1s (Sing A) a₀ a₃
axiom a₁₃ : 1s (Sing A) a₁ a₃
axiom a₀₁₃ : 2s (Sing A) a₀ a₁ a₀₁ a₃ a₀₃ a₁₃
axiom a₂₃ : 1s (Sing A) a₂ a₃
axiom a₀₂₃ : 2s (Sing A) a₀ a₂ a₀₂ a₃ a₀₃ a₂₃
axiom a₁₂₃ : 2s (Sing A) a₁ a₂ a₁₂ a₃ a₁₃ a₂₃
echo 3s (Sing A) a₀ a₁ a₀₁ a₂ a₀₂ a₁₂ a₀₁₂ a₃ a₀₃ a₁₃ a₀₁₃ a₂₃ a₀₂₃ a₁₂₃

{` The empty SST `}
def sst.∅ : SST ≔ [
| .z ↦ data [ ]
| .s ↦ [ ]
]

{` The unit SST `}
def sst.𝟙 : SST ≔ [
| .z ↦ sig ()
| .s ↦ _ ↦ sst.𝟙⁽ᵈ⁾
]

{` Binary products of SSTs `}
def sst.prod (X Y : SST) : SST ≔ [
| .z ↦ sig ( fst : X .z, snd : Y .z )
| .s ↦ xy ↦ sst.prod⁽ᵈ⁾ X (X .s (xy .fst)) Y (Y .s (xy .snd))
]

{` Dependent Σ-SSTs require symmetry! `}
def sst.Σ (X : SST) (Y : SST⁽ᵈ⁾ X) : SST ≔ [
| .z ↦ sig ( fst : X .z, snd : Y .z fst )
| .s ↦ xy ↦ sst.Σ⁽ᵈ⁾ X (X .s (xy .fst)) Y (sym (Y .s (xy .fst) (xy .snd)))
]

{`
We can check this by hand too:

sst.Σ⁽ᵈ⁾ : (X : SST) (X' : SST⁽ᵈ⁾ X) (Y : SST⁽ᵈ⁾ X) (Y' : SST⁽ᵈᵈ⁾ X X' Y) : SST⁽ᵈ⁾ (sst.Σ X Y)
sst.Σ⁽ᵈ⁾ X (X .s (xy .fst)) Y : SST⁽ᵈᵈ⁾ X (X .s (xy .fst)) Y → SST⁽ᵈ⁾ (sst.Σ X Y)
X : SST
xy .fst : X .z
X .s (xy .fst) : SST⁽ᵈ⁾ X
Y : SST⁽ᵈ⁾ X
xy .snd : Y .z (xy .fst)
− .s : (X : SST) → X .z → SST⁽ᵈ⁾ X
− .s⁽ᵈ⁾ : {X : SST} (X' : SST⁽ᵈ⁾ X) (x : X .z) (x' : X' .z x) → SST⁽ᵈᵈ⁾ X X' (X .s x)
Y .s⁽ᵈ⁾ (xy .fst) (xy .snd) : SST⁽ᵈᵈ⁾ X Y (X .s (xy .fst))

So the type of "Y .s⁽ᵈ⁾ (xy .fst) (xy .snd)" is indeed symmetrized from what "sst.Σ⁽ᵈ⁾ X (X .s (xy .fst)) Y" expects for its argument.  (Note that ".s⁽ᵈ⁾" is not Narya syntax; the field projection has the same syntax at every dimension, I just wrote this for clarity in the by-hand version.)
`}

{` Constant displayed SSTs also require symmetry, as noted in the paper. `}
def sst.const (X Y : SST) : SST⁽ᵈ⁾ X ≔ [
| .z ↦ sig _ ↦ ( ungel : Y .z )
| .s ↦ x y ↦ sym (sst.const⁽ᵈ⁾ X (X .s x) Y (Y .s (y .ungel)))
]

{` Using constant displayed SSTs, we can define binary sum SSTs. `}
def sst.sum (X Y : SST) : SST ≔ [
| .z ↦ data [ inl. (_ : X .z) | inr. (_ : Y .z) ]
| .s ↦ [
  | inl. x ↦ sst.sum⁽ᵈ⁾ X (X .s x) Y (sst.const Y sst.∅)
  | inr. y ↦ sst.sum⁽ᵈ⁾ X (sst.const X sst.∅) Y (Y .s y)
  ]
]

{` Augmented SSTs are another displayed coinductive. `}
def ASST : Type ≔ codata [
| X .z : Type
| X .s : ASST⁽ᵈ⁾ X
]

{` As is pointedness of an SST. `}
def sst.pt (X : SST) : Type ≔ codata [
| p .z : X .z
| p .s : sst.pt⁽ᵈ⁾ X (X .s (p .z)) p
]

{` And maps of SSTs. `}
def sst.hom (X Y : SST) : Type ≔ codata [
| f .z : X .z → Y .z
| f .s : (x : X .z) → sst.hom⁽ᵈ⁾ X (X .s x) Y (Y .s (f .z x)) f
]

{` Identities and composition for maps `}
def sst.id (X : SST) : sst.hom X X ≔ [
| .z ↦ x ↦ x
| .s ↦ x ↦ sst.id⁽ᵈ⁾ X (X .s x)
]

def sst.comp (X Y Z : SST) (g : sst.hom Y Z) (f : sst.hom X Y) : sst.hom X Z ≔ [
| .z ↦ x ↦ g .z (f .z x)
| .s ↦ x ↦ sst.comp⁽ᵈ⁾ X (X .s x) Y (Y .s (f .z x)) Z (Z .s (g .z (f .z x))) g (g .s (f .z x)) f (f .s x)
]

{` Universal maps `}
def sst.abort (X : SST) : sst.hom sst.∅ X ≔ [
| .z ↦ [ ]
| .s ↦ [ ]
]

def sst.uniq (X : SST) : sst.hom X sst.𝟙 ≔ [
| .z ↦ _ ↦ ()
| .s ↦ x ↦ sst.uniq⁽ᵈ⁾ X (X .s x)
]

def sst.pair (X Y Z : SST) (f : sst.hom X Y) (g : sst.hom X Z) : sst.hom X (sst.prod Y Z) ≔ [
| .z ↦ x ↦ (f .z x, g .z x)
| .s ↦ x ↦ sst.pair⁽ᵈ⁾ X (X .s x) Y (Y .s (f .z x)) Z (Z .s (g .z x)) f (f .s x) g (g .s x)
]

{` Copairing requires a displayed version of abort.  And for that, we can't match directly against (x' .ungel) since it isn't a variable, so we have to define a helper function first. `}
def sst.abortz (X : Type) : sst.∅ .z → X ≔ [ ]

def sst.const_abort (X Y : SST) (Y' : SST⁽ᵈ⁾ Y) (f : sst.hom X Y) : sst.hom⁽ᵈ⁾ X (sst.const X sst.∅) Y Y' f ≔ [
| .z ↦ x x' ↦ sst.abortz (Y' .z (f .z x)) (x' .ungel)
| .s ↦ x x' ↦ sst.abortz
  {` Ideally, this big long argument should be obtainable by unification. `}
	(sst.hom⁽ᵈᵈ⁾
    X (sst.const X sst.∅) (X .s x) (sym (sst.const⁽ᵈ⁾ X (X .s x) sst.∅ (sst.∅ .s (x' .ungel))))
    Y Y' (Y .s (f .z x)) (Y' .s (f .z x) (sst.abortz (Y' .z (f .z x)) (x' .ungel)))
    f (sst.const_abort X Y Y' f) (f .s x))
  (x' .ungel)
]

def sst.copair (X Y Z : SST) (f : sst.hom X Z) (g : sst.hom Y Z) : sst.hom (sst.sum X Y) Z ≔ [
| .z ↦ [ inl. x ↦ f .z x | inr. y ↦ g .z y ]
| .s ↦ [
  | inl. x ↦ sst.copair⁽ᵈ⁾ X (X .s x) Y (sst.const Y sst.∅) Z (Z .s (f .z x))
                f (f .s x) g (sst.const_abort Y Z (Z .s (f .z x)) g)
  | inr. y ↦ sst.copair⁽ᵈ⁾ X (sst.const X sst.∅) Y (Y .s y) Z (Z .s (g .z y))
                f (sst.const_abort X Z (Z .s (g .z y)) f) g (g .s y)
  ]
]
