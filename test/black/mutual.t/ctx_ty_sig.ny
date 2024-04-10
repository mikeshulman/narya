` We can also define a notion of "contexts" and "types" by mutual induction-induction.  First we define a record-type in which the pair of the type "ctx" and a type family "ty" over it lives.
def ctx_ty_type : Type ≔ sig (
  ctx : Type,
  ty : ctx → Type,
)

` Then we can define the pair of them by mutual induction-induction.
def ctx_ty : ctx_ty_type ≔ (
  ` A context is either empty or an extension of a context by a type in that context.
  ctx ≔ data [
  | empty.
  | ext. (Γ : ctx_ty .ctx) (A : ctx_ty .ty Γ) ],
  ` As generating types, we include a single "base type" along with Π-types.  Note that the context Γ is a non-uniform parameter, not an index.
  ty ≔ Γ ↦ data [
  | base.
  | pi. (A : ctx_ty .ty Γ) (B : ctx_ty .ty (ext. Γ A)) ]
)

` We can also include a family of "terms" indexed by types and contexts.  As before, here is the record-type in which the triple lives.
def ctx_ty_tm_type : Type ≔ sig (
  ctx : Type,
  ty : ctx → Type,
  tm : (Γ:ctx) → ty Γ → Type,
)

` And now we can define all three mutually.
def ctx_ty_tm : ctx_ty_tm_type ≔ (
  ctx ≔ data [
  | empty.
  | ext. (Γ : ctx_ty_tm .ctx) (A : ctx_ty_tm .ty Γ) ],
  ` This time we include also a single universe type, a Tarski coercion from terms in the universe to types, and substitution of terms into types.
  ty ≔ Γ ↦ data [
  | base.
  | pi. (A : ctx_ty_tm .ty Γ) (B : ctx_ty_tm .ty (ext. Γ A))
  | uu.
  | el. (X : ctx_ty_tm .tm Γ uu.)
  | sub. (A : ctx_ty_tm .ty Γ) (B : ctx_ty_tm .ty (ext. Γ A)) (a : ctx_ty_tm .tm Γ A)
  ],
  ` As generating terms, we have a code in the universe for the base type, and lambda-abstractions and applications for the Π-types.  Note that the typing of application requires substitution.  Also, the context is again a non-uniform parameter, but the *type* is a true index.
  tm ≔ Γ ↦ data [
  | codebase. : ctx_ty_tm .tm Γ uu.
  | lam. (A : ctx_ty_tm .ty Γ) (B : ctx_ty_tm .ty (ext. Γ A)) (b : ctx_ty_tm .tm (ext. Γ A) B) : ctx_ty_tm .tm Γ (pi. A B)
  | app. (A : ctx_ty_tm .ty Γ) (B : ctx_ty_tm .ty (ext. Γ A)) (f : ctx_ty_tm .tm Γ (pi. A B)) (a : ctx_ty_tm .tm Γ A) : ctx_ty_tm .tm Γ (sub. A B a)
  ],
)
