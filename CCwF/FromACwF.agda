module CCwF.FromACwF where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Transport

open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Limits.Terminal

open import Cubical.Categories.Presheaf
open import Cubical.Categories.Functor
import Cubical.Categories.Instances.Elements as Els
open Els.Contravariant

open import ACwF.Base
open import CCwF.Base

module _ {ℓOb ℓHom ℓTy ℓTm : Level} (C : Category ℓOb ℓHom) (X : Algebraic.CwF C ℓTy ℓTm) where

  open Category C

  open Algebraic.CwF X
  open Categorical.CwF hiding (_[_]Ty ; _[_]Tm ; _⋆_)
  open Functor
  open Iso

  ACwF→CCwF : Categorical.CwF C ℓTy ℓTm
  ACwF→CCwF .emptyContext = ⟨⟩
  ACwF→CCwF .Ty .F-ob Γ .fst = X .Ty Γ
  ACwF→CCwF .Ty .F-ob Γ .snd = isSetTy Γ
  ACwF→CCwF .Ty .F-hom σ A = A [ σ ]Ty
  ACwF→CCwF .Ty .F-id = funExt [id]Ty
  ACwF→CCwF .Ty .F-seq f g = funExt (λ A → [][]Ty A g f)
  ACwF→CCwF .Tm .F-ob (Γ , A) .fst = X .Tm Γ A
  ACwF→CCwF .Tm .F-ob (Γ , A) .snd = isSetTm Γ A
  ACwF→CCwF .Tm .F-hom {Γ , A} {Δ , B} (σ , prf) t = subst (X .Tm Δ) prf (t [ σ ]Tm)
  ACwF→CCwF .Tm .F-id = funExt (λ t → fromPathP ([id]Tm t))
  ACwF→CCwF .Tm .F-seq (f , pf) (g , pg) = funExt (λ t → {!X .[][]Tm t g f!})
  ACwF→CCwF .ctxExt .F-ob (Γ , A) = X ._⋆_ Γ A
  ACwF→CCwF .ctxExt .F-hom {Γ , A} {Δ , B} (f , pf) = subst (λ x → Hom[ X ._⋆_ Γ x , _ ]) pf (f ⁺)
  ACwF→CCwF .ctxExt .F-id {Γ , A} = fromPathP (id⁺ {A = A})
  ACwF→CCwF .ctxExt .F-seq f g = {!!}
  ACwF→CCwF .ctxExtIso A .fun σ .fst = p ∘ σ
  ACwF→CCwF .ctxExtIso {Γ} {Δ} A .fun σ .snd = subst⁻ (X .Tm Δ) ([][]Ty A σ p) (q [ σ ]Tm)
  ACwF→CCwF .ctxExtIso A .inv (σ , t) = (σ ⁺) ∘ ⟨ t ⟩
  ACwF→CCwF .ctxExtIso A .sec (σ , t) i .fst =
    let goal : p ∘ ((σ ⁺) ∘ ⟨ t ⟩) ≡ σ
        goal = p ∘ ((σ ⁺) ∘ ⟨ t ⟩) ≡⟨ ⋆Assoc _ _ _ ⟩
               (p ∘ (σ ⁺)) ∘ ⟨ t ⟩ ≡⟨ cong (_∘ ⟨ t ⟩) (p∘⁺ σ) ⟩
               (σ ∘ p) ∘ ⟨ t ⟩     ≡⟨  sym (⋆Assoc _ _ _) ⟩
               σ ∘ (p ∘ ⟨ t ⟩)     ≡⟨ cong (σ ∘_) (p∘⟨⟩≡id t) ⟩
               σ ∘ id              ≡⟨ ⋆IdL σ ⟩
               σ ∎
    in goal i
  ACwF→CCwF .ctxExtIso A .sec (σ , t) i .snd = {!!}
  ACwF→CCwF .ctxExtIso A .ret = {!!}
  ACwF→CCwF .coerceFun = {!!}
  ACwF→CCwF .ctxExtIsoFunNat = {!!}
  ACwF→CCwF .ctxExtIsoFunNatWithoutCoerceFun = {!!}
  ACwF→CCwF .coerceInv = {!!}
  ACwF→CCwF .ctxExtIsoInvNat = {!!}
  ACwF→CCwF .ctxExtIsoInvNatWithoutCoerceInv = {!!}
