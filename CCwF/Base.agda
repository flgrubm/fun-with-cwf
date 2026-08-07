module CCwF.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties

open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Limits.Terminal

open import Cubical.Categories.Presheaf
open import Cubical.Categories.Functor
import Cubical.Categories.Instances.Elements as Els
open Els.Contravariant

module Categorical {ℓOb ℓHom : Level} (C : Category ℓOb ℓHom) where

  open Category C hiding (_⋆_)
  open Functor

  Ctx = Category.ob C

  _⟶_ : (Δ Γ : Ctx) → Type ℓHom
  Δ ⟶ Γ = C [ Δ , Γ ]

  infix 20 _⟶_

  private variable
    Θ Δ Γ : Ctx

  record CwF (ℓTy ℓTm : Level) :
             Type (ℓ-suc (ℓ-max ℓOb (ℓ-max ℓHom (ℓ-max ℓTy  ℓTm)))) where
    field
      emptyContext : Terminal C

      Ty : Presheaf C ℓTy

      Tm : Presheaf (∫ Ty) ℓTm

    -- Some nice notations
    Ty[_] : (Γ : Ctx) → Type ℓTy
    Ty[ Γ ] = Ty .F-ob Γ .fst

    _[_]Ty : (A : Ty[ Γ ]) (σ : Δ ⟶ Γ) → Ty[ Δ ]
    A [ σ ]Ty = Ty .F-hom σ A

    Tm[_,_] : (Γ : Ctx) (A : Ty[ Γ ]) → Type ℓTm
    Tm[ Γ , A ] = Tm .F-ob (Γ , A) .fst

    _[_]Tm : {A : Ty[ Γ ]} (a : Tm[ Γ , A ]) (σ : Δ ⟶ Γ) → Tm[ Δ , A [ σ ]Ty ]
    a [ σ ]Tm = Tm .F-hom (σ , refl) a

    infix  40 _[_]Ty
    infix  40 _[_]Tm

    field
      _▹_ : (Γ : Ctx) (A : Ty[ Γ ]) → Ctx
      p   : {Γ : Ctx} {A : Ty[ Γ ]} → Γ ▹ A ⟶ Γ
      q   : {Γ : Ctx} {A : Ty[ Γ ]} → Tm[ Γ ▹ A , A [ p ]Ty ]

    infixl 30 _▹_

    ⟨p,q⟩ : {Γ Δ : Ctx} (A : Ty[ Γ ])
          → (Δ ⟶ Γ ▹ A) → Σ[ σ ∈ Δ ⟶ Γ ] Tm[ Δ , A [ σ ]Ty ]
    ⟨p,q⟩ {Δ = Δ} A τ =
      p ∘ τ , subst (λ T → Tm[ Δ , T ]) (sym (funExt⁻ (Ty .F-seq p τ) A)) (q [ τ ]Tm)

    field
      ctxExtRepr : {Γ Δ : Ctx} (A : Ty[ Γ ]) → isEquiv (⟨p,q⟩ {Γ} {Δ} A)

  open CwF

  module _ {ℓTy ℓTm : Level} (Cw Cw' : CwF ℓTy ℓTm)
    (emptyContext≡ : Cw .emptyContext .fst ≡ Cw' .emptyContext .fst)
    (Ty≡ : Cw .Ty ≡ Cw' .Ty)
    (Tm≡ : PathP (λ i → Presheaf (∫ (Ty≡ i)) ℓTm) (Cw .Tm) (Cw' .Tm))
    where
      private
        TyAt : ∀ i Γ → Type ℓTy
        TyAt i Γ = Ty≡ i .F-ob Γ .fst
        TmAt : ∀ i Γ A → Type ℓTm
        TmAt i Γ A = Tm≡ i .F-ob (Γ , A) .fst
      module _
        (▹≡ : PathP (λ i → (Γ : Ctx) → TyAt i Γ → Ctx) (Cw ._▹_) (Cw' ._▹_))
        (p≡ : PathP (λ i → {Γ : Ctx} {A : TyAt i Γ} → ▹≡ i Γ A ⟶ Γ) (Cw .p) (Cw' .p))
        (q≡ : PathP (λ i → {Γ : Ctx} {A : TyAt i Γ} → TmAt i (▹≡ i Γ A) (Ty≡ i .F-hom (p≡ i) A)) (Cw .q) (Cw' .q))
        where

        private
          ⟨p,q⟩At : ∀ i → {Γ Δ : Ctx} (A : TyAt i Γ)
            → (Δ ⟶ ▹≡ i Γ A) → Σ[ σ ∈ Δ ⟶ Γ ] TmAt i Δ (Ty≡ i .F-hom σ A)
          ⟨p,q⟩At i {Γ} {Δ} A τ =
            (p≡ i ∘ τ) ,
            subst (TmAt i Δ) (sym (funExt⁻ (Ty≡ i .F-seq (p≡ i) τ) A)) (Tm≡ i .F-hom (τ , refl) (q≡ i))
          ctxExtRepr≡ :
            PathP (λ i → ∀ {Γ} {Δ} (A : TyAt i Γ) → isEquiv (⟨p,q⟩At i {Γ} {Δ} A))
              (λ A → Cw .ctxExtRepr A)
              (λ A → Cw' .ctxExtRepr A)
          ctxExtRepr≡ = isProp→PathP (λ i → isPropImplicitΠ2 λ Γ Δ → isPropΠ λ A → isPropIsEquiv _) _ _

        makeCCwFPath : Cw ≡ Cw'
        makeCCwFPath i .emptyContext =
          Σ≡Prop (isPropIsTerminal C) {u = Cw .emptyContext} {v = Cw' .emptyContext}
            emptyContext≡
            i
        makeCCwFPath i .Ty = Ty≡ i
        makeCCwFPath i .Tm = Tm≡ i
        makeCCwFPath i ._▹_ = ▹≡ i
        makeCCwFPath i .p = p≡ i
        makeCCwFPath i .q = q≡ i
        makeCCwFPath i .ctxExtRepr A = ctxExtRepr≡ i A
