module ACwF.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Isomorphism

open import Cubical.Functions.FunExtEquiv

open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Limits.Terminal

module Algebraic {ℓOb ℓHom : Level} (C : Category ℓOb ℓHom) where

  open Category C hiding (_⋆_)

  Ctx = Category.ob C

  -- potentially rename
  _⟶_ : (Δ Γ : Ctx) → Type ℓHom
  Δ ⟶ Γ = C [ Δ , Γ ]

  infix 20 _⟶_

  private variable
    Θ Δ Γ : Ctx

  -- Unfolded definition of CwF à la Pitts
  record CwF (ℓTy ℓTm : Level) :
             Type (ℓ-suc (ℓ-max ℓOb (ℓ-max ℓHom (ℓ-max ℓTy  ℓTm)))) where
    field
      -- Empty context
      ⟨⟩ : Terminal C

      -- | Types

      Ty : (Γ : Ctx) → Type ℓTy

      isSetTy : (Γ : Ctx) → isSet (Ty Γ)

      _[_]Ty : (A : Ty Γ) (σ : Δ ⟶ Γ)
             → ----------------------
               Ty Δ

      [id]Ty : (A : Ty Γ)
             → ----------------
               A [ id ]Ty ≡ A

      [][]Ty : (A : Ty Γ) (σ' : Θ ⟶ Δ) (σ : Δ ⟶ Γ)
             → -------------------------------------------
               A [ σ ∘ σ' ]Ty ≡ (A [ σ ]Ty ) [ σ' ]Ty

      -- | Terms

      Tm : (Γ : Ctx) (A : Ty Γ) → Type ℓTm

      isSetTm : (Γ : Ctx) (A : Ty Γ) → isSet (Tm Γ A)

      _[_]Tm : {A : Ty Γ} (a : Tm Γ A) (σ : Δ ⟶ Γ)
             → -----------------------------------
               Tm Δ (A [ σ ]Ty)

      [id]Tm : {A : Ty Γ} (a : Tm Γ A)
             → ------------------------------------------------
               PathP (λ i → Tm Γ ([id]Ty A i)) (a [ id ]Tm) a

      [][]Tm : {A : Ty Γ} (a : Tm Γ A) (σ' : Θ ⟶ Δ) (σ : Δ ⟶ Γ)
             → ------------------------------------------------
                PathP (λ i → Tm Θ ([][]Ty A σ' σ i))
                      (a [ σ ∘ σ' ]Tm)
                      (a [ σ ]Tm [ σ' ]Tm)

      -- | Comprehension objects

      _⋆_ : (Γ : Ctx) (A : Ty Γ) → Ctx

      p : {A : Ty Γ} → (Γ ⋆ A) ⟶ Γ

      q : {A : Ty Γ} → Tm (Γ ⋆ A) (A [ p ]Ty)

    infix  40 _[_]Ty
    infix  40 _[_]Tm
    infixl 30 _⋆_

    field
      _⁺ : {A : Ty Γ} (σ : Δ ⟶ Γ) →  (Δ ⋆ A [ σ ]Ty) ⟶ (Γ ⋆ A)

      ⟨_⟩ : {A : Ty Γ} (a : Tm Γ A) → (Γ ⟶ (Γ ⋆ A)) -- ⟨ id , a ⟩
    -- ⟨⟩-∘ : (a : Tm Γ A) (γ : Sub Δ Γ) → ⟨ a ⟩ ∘ γ ≡ γ ⁺ ∘ ⟨ a [ γ ]ᵗ ⟩
    -- ▹-η : id {Γ ▹ A} ≡ p ⁺ ∘ ⟨ q ⟩

    -- ⁺-∘ :
    --     (γ : Sub Δ Γ) (δ : Sub Θ Δ) →
    --     PathP (λ i → Sub (Θ ▹ []ᵀ-∘ A γ δ i) (Γ ▹ A)) ((γ ∘ δ) ⁺) (γ ⁺ ∘ δ ⁺)
    -- ⁺-id : PathP (λ i → Sub (Γ ▹ []ᵀ-id A i) (Γ ▹ A)) (id ⁺) id

    -- p-⁺ : (γ : Sub Δ Γ) → p {A = A} ∘ γ ⁺ ≡ γ ∘ p
    -- []ᵀ-p-⁺ :
    --     (B : Ty Γ) (γ : Sub Δ Γ) → B [ p {A = A} ]ᵀ [ γ ⁺ ]ᵀ ≡ B [ γ ]ᵀ [ p ]ᵀ
    -- q-⁺ :
    --     (γ : Sub Δ Γ) →
    --     PathP (λ i → Tm (Δ ▹ A [ γ ]ᵀ) ([]ᵀ-p-⁺ A γ i)) (q [ γ ⁺ ]ᵗ) q

    -- p-⟨⟩ : (a : Tm Γ A) → p ∘ ⟨ a ⟩ ≡ id
    -- []ᵀ-p-⟨⟩ : (B : Ty Γ) (a : Tm Γ A) → B [ p ]ᵀ [ ⟨ a ⟩ ]ᵀ ≡ B
    -- q-⟨⟩ : (a : Tm Γ A) → PathP (λ i → Tm Γ ([]ᵀ-p-⟨⟩ A a i)) (q [ ⟨ a ⟩ ]ᵗ) a

