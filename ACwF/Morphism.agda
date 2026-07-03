module ACwF.Morphism where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Presheaf.Morphism
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Elements
open import Cubical.Categories.Instances.Elements.Properties
open import ACwF.Base

open Category
open Functor
open NatTrans
open Algebraic
open Algebraic.CwF

module _ {ℓOb ℓHom ℓOb' ℓHom'} (C : Category ℓOb ℓHom) (D : Category ℓOb' ℓHom') where
  record CwFMorphism {ℓTy ℓTm ℓTy' ℓTm'} (X : CwF C ℓTy ℓTm) (Y : CwF D ℓTy' ℓTm') : Type (ℓ-max ℓOb (ℓ-max ℓHom (ℓ-max ℓOb' (ℓ-max ℓHom' (ℓ-max ℓTy (ℓ-max ℓTm (ℓ-max ℓTy' ℓTm'))))))) where
    field
      ctxMorph : Functor C D
      tyMorph : {Γ : C .ob} → X .Ty Γ → Y .Ty (ctxMorph .F-ob Γ)
      tmMorph : {Γ : C .ob} {A : X .Ty Γ} → X .Tm Γ A → Y .Tm (ctxMorph .F-ob Γ) (tyMorph A)

      preserves⟨⟩ : ctxMorph .F-ob (X .⟨⟩ .fst) ≡ Y .⟨⟩ .fst

      preserves[]Ty : ∀ {Γ} {Δ} {A : X .Ty Γ} (σ : C [ Δ , Γ ])
        → tyMorph (X ._[_]Ty A σ) ≡ Y ._[_]Ty (tyMorph A) (ctxMorph .F-hom σ)

      preserves[]Tm : ∀ {Γ} {Δ} {A : X .Ty Γ} {x : X .Tm Γ A} (σ : C [ Δ , Γ ])
        → PathP (λ i → Y .Tm (ctxMorph .F-ob Δ) (preserves[]Ty {A = A} σ i))
          (tmMorph (X ._[_]Tm x σ))
          (Y ._[_]Tm (tmMorph x) (ctxMorph .F-hom σ))

    field
      preserves▹ : ∀ Γ A → ctxMorph .F-ob (X ._▹_ Γ A) ≡ Y ._▹_ (ctxMorph .F-ob Γ) (tyMorph A)

      preservesp : ∀ {Γ} {A : X .Ty Γ}
        → PathP (λ i → D [ preserves▹ Γ A i , ctxMorph .F-ob Γ ])
            (ctxMorph .F-hom (X .p))
            (Y .p)

      preservesq : ∀ {Γ} {A : X .Ty Γ}
        → PathP (λ i → Y .Tm (preserves▹ Γ A i) ((preserves[]Ty (X .p) ◁ (λ j → Y ._[_]Ty (tyMorph A) (preservesp j))) i))
            (tmMorph (X .q))
            (Y .q)

    -- these should be proved in the future
    -- preserves⟨_⟩ : ∀ {Γ} {A : X .Ty Γ} (a : X .Tm Γ A)
    --   → PathP (λ i → D [ ctxMorph .F-ob Γ , preserves▹ Γ A i ])
    --       (ctxMorph .F-hom (X .⟨_⟩ a))
    --       (Y .⟨_⟩ (tmMorph a))
    -- preserves⟨_⟩ {Γ} {A} a = {!!}

    -- preserves⁺ : ∀ {Γ Δ} {A : X .Ty Γ} (σ : C [ Δ , Γ ])
    --   → PathP (λ i → D
    --         [ (preserves▹ Δ (X ._[_]Ty A σ) ∙ cong (Y ._▹_ (ctxMorph .F-ob Δ)) (preserves[]Ty σ)) i
    --         , preserves▹ Γ A i
    --         ])
    --       (ctxMorph .F-hom (X ._⁺ σ))
    --       (Y ._⁺ (ctxMorph .F-hom σ))
    -- preserves⁺ {Γ} {Δ} {A} σ = {!!}
