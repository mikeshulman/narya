axiom A : Type

axiom B : Type

echo B

def id : Type → Type ≔ X ↦ X

axiom b : B

axiom g : (A → B) → A → B

def f : A → B ≔ g ?

axiom a_very_long_variable : A

axiom a_very_long_function : A → A → A → A → A → A → A → B

def f' : A → B ≔ ?

def ℕ : Type ≔ data [
| zero. : ℕ
| suc. : ℕ → ℕ
]

def plus (m n : ℕ) : ℕ ≔ match n [
| zero. ↦ ?
| suc. n ↦ ?
]

axiom P : ℕ → Type

def anop : ℕ → ℕ → (x : ℕ) → P x ≔ n n0 n ↦ ?

{` The user's "n0" should not be shadowed by an auto-generated one `}
def anop' : ℕ → ℕ → (x : ℕ) → P x ≔ n0 n n ↦ ?

def anop'' : ℕ → ℕ → (x : ℕ) → P x ≔ n _ n ↦ ?

{` Nor the user's H be shadowed by an auto-generated one `}
def anop''' : ℕ → ℕ → (x : ℕ) → P x ≔ H _ n ↦ ?

def Σ (A:Type) (B : A → Type) : Type ≔ sig (
  fst : A,
  snd : B fst,
)

{` Here the type of the second hole is not the first hole but "pp .fst", since the first hole is potential and causes its case tree to be just stuck. `}
def pp : Σ Type (X ↦ X) ≔ ( ? , ? )

{` But if we break the case tree, then the type of the second hole is the first hole. `}
def pp' : Σ Type (X ↦ X) ≔ ( id ? , ? )

{` The out-of-scope variable "H" that appears here is because record types are stored internally like codatatypes with all fields depending on a single variable, so we have to introduce that variable during typechecking. `}
def foo : Type ≔ sig (
  bar : ℕ,
  {` It's important for ? to be its own token, so that it can be followed immediately by a comma. `}
  baz : ?,
)

def foo' : Type ≔ sig (
  bar : Type,
  baz : (x:bar) → ?,
)

def gel0 (A B : Type) : Id Type A B ≔ sig x y ↦ (
  one : ?,
)

def gel1 (A B : Type) : Id Type A B ≔ sig x y ↦ (
  one : Type,
  two : ?
)

def gel2 (A B : Type) : Id Type A B ≔ sig x y ↦ (
  one : ?,
  two : ?
)

def gel3 (A B : Type) : Id Type A B ≔ codata [
| x .one : ?
| x .two : ?
]

axiom C : A → Type

def AC : Type ≔ sig (
  a : ℕ → A,
  c : C (a zero.),
)

def ac : AC ≔ (
  a ≔ ?,
  c ≔ ?
)

def ida : A → A ≔ x ↦ x

def ideqid : Id (A -> A) ida ida := ((x |-> x) : Id (A -> A ) ida ida -> Id (A -> A) ida ida) (u u u |-> u)

echo ideqid

{` TODO: Ideally, the user's "u0" should not be shadowed by an auto-generated one (although this matters a bit less than the one for contexts, since the user won't be using it to enter terms).  (This isn't about holes.) `}
def ideqid' : Id (A -> A) ida ida := ((x |-> x) : Id (A -> A ) ida ida -> Id (A -> A) ida ida) (u u u0 |-> u0)

echo ideqid'

def ideqid'' : Id (A -> A) ida ida := ((x |-> x) : Id (A -> A ) ida ida -> Id (A -> A) ida ida) (u u u |-> ?)

{` A kinetic hole `}
def afam : Type → Type ≔ X ↦ id ?

{` This requires comparing a metavariable to equal itself when evaluated in equal environments. `}
def idafam (X:Type) : afam X → afam X ≔ x ↦ x
