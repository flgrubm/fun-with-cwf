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

      -- | Context extension

      _⋆_ : (Γ : Ctx) (A : Ty Γ) → Ctx

      p : {A : Ty Γ} → Γ ⋆ A ⟶ Γ

      q : {A : Ty Γ} → Tm (Γ ⋆ A) (A [ p ]Ty)

    infix  40 _[_]Ty
    infix  40 _[_]Tm
    infixl 30 _⋆_

    field
      _⁺ : {A : Ty Γ} (σ : Δ ⟶ Γ)
         → ----------------------
           Δ ⋆ A [ σ ]Ty ⟶ Γ ⋆ A

      ⟨_⟩ : {A : Ty Γ} (a : Tm Γ A)
          → -----------------------
            Γ ⟶ (Γ ⋆ A)

      ⟨⟩∘ : {A : Ty Γ} (a : Tm Γ A) (σ : Δ ⟶ Γ)
          → -----------------------------------
            ⟨ a ⟩ ∘ σ ≡ σ ⁺ ∘ ⟨ a [ σ ]Tm ⟩

      p⁺∘⟨q⟩≡id : {A : Ty Γ}
                → ------------------------
                  p ⁺ ∘ ⟨ q ⟩ ≡ id {Γ ⋆ A}

      ∘⁺ : {A : Ty Γ} (σ' : Θ ⟶ Δ) (σ : Δ ⟶ Γ)
         → -------------------------------------------------------------------
           PathP (λ i → Θ ⋆ [][]Ty A σ' σ i ⟶ Γ ⋆ A) ((σ ∘ σ') ⁺) (σ ⁺ ∘ σ' ⁺)

      id⁺ : {A : Ty Γ}
          → ----------------------------------------------
            PathP (λ i → Γ ⋆ [id]Ty A i ⟶ Γ ⋆ A) (id ⁺) id

      p∘⁺ : {A : Ty Γ} (σ : Δ ⟶ Γ)
          → -----------------------
            p {A = A} ∘ σ ⁺ ≡ σ ∘ p

      [p][⁺]Ty : {A : Ty Γ} (B : Ty Γ) (σ : Δ ⟶ Γ)
               → -----------------------------------------------
                 B [ p {A = A} ]Ty [ σ ⁺ ]Ty ≡ B [ σ ]Ty [ p ]Ty

      q[⁺]Tm : {A : Ty Γ} (σ : Δ ⟶ Γ)
             → -----------------------------------------------------------------
               PathP (λ i → Tm (Δ ⋆ A [ σ ]Ty) ([p][⁺]Ty A σ i)) (q [ σ ⁺ ]Tm) q

      p∘⟨⟩≡id : {A : Ty Γ} (a : Tm Γ A)
              → -----------------------
                p ∘ ⟨ a ⟩ ≡ id

      [p][⟨⟩]Ty : {A : Ty Γ} (B : Ty Γ) (a : Tm Γ A)
                → ----------------------------------
                  B [ p ]Ty [ ⟨ a ⟩ ]Ty ≡ B

      q[⟨⟩]Tm : {A : Ty Γ} (a : Tm Γ A)
              → ------------------------------------------------------
                PathP (λ i → Tm Γ ([p][⟨⟩]Ty A a i)) (q [ ⟨ a ⟩ ]Tm) a

