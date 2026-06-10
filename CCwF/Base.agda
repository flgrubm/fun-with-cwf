module CCwF.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism

open import Cubical.Categories.Category
open import Cubical.Categories.Limits.Terminal

open import Cubical.Categories.Presheaf
open import Cubical.Categories.Functor
import Cubical.Categories.Instances.Elements as Els
open Els.Contravariant

module Categorical {ℓOb ℓHom : Level} (C : Category ℓOb ℓHom) where

  open Category C hiding (_⋆_)
  open Functor
  open Iso

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

      ctxExt : Functor (∫ Ty) C

    -- Some nice notations
    Ty[_] : (Γ : Ctx) → Type ℓTy
    Ty[ Γ ] = Ty .F-ob Γ .fst

    _[_]Ty : (A : Ty[ Γ ]) (σ : Δ ⟶ Γ) → Ty[ Δ ]
    A [ σ ]Ty = Ty .F-hom σ A

    Tm[_,_] : (Γ : Ctx) (A : Ty[ Γ ]) → Type ℓTm
    Tm[ Γ , A ] = Tm .F-ob (Γ , A) .fst

    _[_]Tm : {A : Ty[ Γ ]} (a : Tm[ Γ , A ]) (σ : Δ ⟶ Γ) → Tm[ Δ , A [ σ ]Ty ]
    a [ σ ]Tm = Tm .F-hom (σ , refl) a

    _⋆_ : (Γ : Ctx) (A : Ty[ Γ ]) → Ctx
    Γ ⋆ A = ctxExt .F-ob (Γ , A)

    infix  40 _[_]Ty
    infix  40 _[_]Tm
    infixl 30 _⋆_

    field
      ctxExtIso : (A : Ty[ Γ ])
                → Iso (Δ ⟶ Γ ⋆ A) (Σ[ σ ∈ Δ ⟶ Γ ] Tm[ Δ , A [ σ ]Ty ])

    -- TODO: what is a good name for this?
    drop : (A : Ty[ Γ ]) (τ : Δ ⟶ Γ ⋆ A) → Δ ⟶ Γ
    drop A τ = ctxExtIso A .fun τ .fst


    -- TODO: settle for the minimal set of fields below which are equivalent to ACwF and makes the proof as easy as possible
    field
      -- This is redundant and doesn't seem to make instantiation easier...
      coerceFun : (A : Ty[ Γ ]) (σ : Δ ⟶ Γ ⋆ A) (τ : Θ ⟶ Δ)
                → A [ drop A σ ]Ty [ τ ]Ty ≡ A [ drop A σ ∘ τ ]Ty

      ctxExtIsoFunNat : (A : Ty[ Γ ]) (σ : Δ ⟶ Γ ⋆ A) (τ : Θ ⟶ Δ)
                      → ctxExtIso A .fun (σ ∘ τ)
                      ≡ ( drop A σ ∘ τ
                        , Tm .F-hom (τ , coerceFun A σ τ) (ctxExtIso A .fun σ .snd))

      -- We can also do it this way...
      ctxExtIsoFunNatWithoutCoerceFun :
                         (A : Ty[ Γ ]) (σ : Δ ⟶ Γ ⋆ A) (τ : Θ ⟶ Δ)
                      →  ctxExtIso A .fun (σ ∘ τ)
                      ≡ ( drop A σ ∘ τ
                        , Tm .F-hom (τ , sym (funExt⁻ (Ty .F-seq (drop A σ) τ) A)) (ctxExtIso A .fun σ .snd))

      -- Stating naturality for the inverse is closer to the algebraic version, so we do it as well even though it is redundant...
      coerceInv : (A : Ty[ Γ ]) (σ : Δ ⟶ Γ) (τ : Θ ⟶ Δ)
                → A [ σ ]Ty [ τ ]Ty ≡ A [ σ ∘ τ ]Ty

      ctxExtIsoInvNat : (A : Ty[ Γ ]) (σ : Δ ⟶ Γ) (a : Tm[ Δ , A [ σ ]Ty ]) (τ : Θ ⟶ Δ)
                      → ctxExtIso A .inv (σ , a) ∘ τ
                      ≡ ctxExtIso A .inv (σ ∘ τ , Tm .F-hom (τ , coerceInv A σ τ) a)

      ctxExtIsoInvNatWithoutCoerceInv :
                        (A : Ty[ Γ ]) (σ : Δ ⟶ Γ) (a : Tm[ Δ , A [ σ ]Ty ]) (τ : Θ ⟶ Δ)
                      → ctxExtIso A .inv (σ , a) ∘ τ
                      ≡ ctxExtIso A .inv (σ ∘ τ , Tm .F-hom (τ , sym (funExt⁻ (Ty .F-seq σ τ) A)) a)
