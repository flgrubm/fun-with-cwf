-- | The syntax of type theory as a quotient inductive-inductive type, following
-- Altenkirch–Kaposi, "Type theory in type theory using quotient inductive
-- types" (POPL 2016): substitutions are built from `ε` and `_,_` and taken
-- apart with `π₁`/`π₂`.  The Pitts-style CwF structure is in
-- `ACwF.Instances.Syntax.CwF`, initiality in `ACwF.Instances.Syntax.Initial`.
--
-- Agda checks each data definition as a whole, so constructors of distinct
-- sorts cannot refer to each other cyclically; yet the signature does
-- (`[][]Ty` uses `_∘_`, `_,_` uses `_[_]Ty`, `,∘` uses `_[_]Tm`).
-- Substitutions, types and terms are therefore one family `Syn` indexed by a
-- `Sort`, whose constructors may mention each other freely.
module ACwF.Instances.Syntax.Base where

open import Cubical.Foundations.Prelude hiding (Sub)

data Con  : Type
data Sort : Con → Type
data Syn  : (Γ : Con) → Sort Γ → Type

data Sort where
  ty  : {Γ : Con} → Sort Γ
  sub : {Δ : Con} (Γ : Con) → Sort Δ
  tm  : {Γ : Con} → Syn Γ ty → Sort Γ

Ty : Con → Type
Ty Γ = Syn Γ ty

Sub : Con → Con → Type
Sub Δ Γ = Syn Δ (sub Γ)

Tm : (Γ : Con) → Ty Γ → Type
Tm Γ A = Syn Γ (tm A)

data Con where
  ◇   : Con
  _▹_ : (Γ : Con) → Ty Γ → Con

infixr 4  _,_
infixl 30 _▹_
infix  40 _[_]Ty _[_]Tm
infixr 50 _∘_

private variable
  Θ Δ Γ Ξ : Con

data Syn where
  -- | Category of substitutions
  id     : Sub Γ Γ
  _∘_    : Sub Δ Γ → Sub Θ Δ → Sub Θ Γ
  idr    : (σ : Sub Δ Γ) → σ ∘ id ≡ σ
  idl    : (σ : Sub Δ Γ) → id ∘ σ ≡ σ
  assoc  : (ν : Sub Ξ Θ) (δ : Sub Θ Δ) (σ : Sub Δ Γ)
         → σ ∘ (δ ∘ ν) ≡ (σ ∘ δ) ∘ ν

  -- | Types
  _[_]Ty : Ty Γ → Sub Δ Γ → Ty Δ
  [id]Ty : (A : Ty Γ) → A [ id ]Ty ≡ A
  [][]Ty : (A : Ty Γ) (σ' : Sub Θ Δ) (σ : Sub Δ Γ)
         → A [ σ ∘ σ' ]Ty ≡ A [ σ ]Ty [ σ' ]Ty

  -- | Terms
  _[_]Tm : {A : Ty Γ} → Tm Γ A → (σ : Sub Δ Γ) → Tm Δ (A [ σ ]Ty)
  [id]Tm : {A : Ty Γ} (a : Tm Γ A)
         → PathP (λ i → Tm Γ ([id]Ty A i)) (a [ id ]Tm) a
  [][]Tm : {A : Ty Γ} (a : Tm Γ A) (σ' : Sub Θ Δ) (σ : Sub Δ Γ)
         → PathP (λ i → Tm Θ ([][]Ty A σ' σ i))
                 (a [ σ ∘ σ' ]Tm) (a [ σ ]Tm [ σ' ]Tm)

  -- | Substitutions as lists of terms
  ε      : Sub Γ ◇
  εη     : (σ : Sub Γ ◇) → ε ≡ σ
  _,_    : {A : Ty Γ} (σ : Sub Δ Γ) → Tm Δ (A [ σ ]Ty) → Sub Δ (Γ ▹ A)
  π₁     : {A : Ty Γ} → Sub Δ (Γ ▹ A) → Sub Δ Γ
  π₂     : {A : Ty Γ} (σ : Sub Δ (Γ ▹ A)) → Tm Δ (A [ π₁ σ ]Ty)
  π₁β    : {A : Ty Γ} (σ : Sub Δ Γ) (t : Tm Δ (A [ σ ]Ty)) → π₁ (σ , t) ≡ σ
  π₂β    : {A : Ty Γ} (σ : Sub Δ Γ) (t : Tm Δ (A [ σ ]Ty))
         → PathP (λ i → Tm Δ (A [ π₁β σ t i ]Ty)) (π₂ (σ , t)) t
  πη     : {A : Ty Γ} (σ : Sub Δ (Γ ▹ A)) → (π₁ σ , π₂ σ) ≡ σ
  -- AK's `,∘` has `subst⁻ (Tm Θ) ([][]Ty A ν σ) (t [ ν ]Tm)` in place of `t'`,
  -- but a transport along a family built from `Syn` is not strictly positive.
  -- Abstracting the transported term over its defining path is equivalent
  -- (singletons are contractible) and transport-free.
  ,∘     : {A : Ty Γ} (σ : Sub Δ Γ) (t : Tm Δ (A [ σ ]Ty)) (ν : Sub Θ Δ)
           (t' : Tm Θ (A [ σ ∘ ν ]Ty))
         → PathP (λ i → Tm Θ ([][]Ty A ν σ i)) t' (t [ ν ]Tm)
         → (σ , t) ∘ ν ≡ (σ ∘ ν , t')

  -- | Set-truncation, for all three sorts at once
  trunc  : {s : Sort Γ} → isSet (Syn Γ s)
