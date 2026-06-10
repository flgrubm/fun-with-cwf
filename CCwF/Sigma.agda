module CCwF.Sigma where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Isomorphism

open import Cubical.Functions.FunExtEquiv

open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Limits.Terminal

open import Cubical.Categories.Presheaf
open import Cubical.Categories.Functor
import Cubical.Categories.Instances.Elements as Els
open Els.Contravariant
open Category hiding (_⋆_)
open Functor
open Iso

open import CCwF.Base

module _ {ℓOb ℓHom : Level} (C : Category ℓOb ℓHom) where
  open Categorical C

  variable
    Γ Δ : Ctx

  record Σ-Structure-CwF {ℓTy ℓTm : Level} (cwf : CwF ℓTy ℓTm) :
         Type (ℓ-suc (ℓ-max ℓOb (ℓ-max ℓHom (ℓ-max ℓTm ℓTy)))) where

    open CwF cwf

    field
      ΣTy : (A : Ty[ Γ ]) (B : Ty[ Γ ⋆ A ]) → Ty[ Γ ]

      ΣTyNat : (A : Ty[ Γ ]) (B : Ty[ Γ ⋆ A ]) (σ : Δ ⟶ Γ)
             → (ΣTy A B) [ σ ]Ty ≡ ΣTy (A [ σ ]Ty) (B [ ctxExt .F-hom (σ , refl) ]Ty)

      ΣTmIso : (A : Ty[ Γ ]) (B : Ty[ Γ ⋆ A ])
             → Iso (Tm[ Γ , ΣTy A B ])
                   (Σ[ a ∈ Tm[ Γ , A ] ] Tm[ Γ , B [ ctxExtIso A .inv (id C , (a [ id C ]Tm)) ]Ty ])

      coerceFun : (A : Ty[ Γ ])
                  (B : Ty[ Γ ⋆ A ])
                  (a : Tm[ Γ , ΣTy A B ])
                  (σ : Δ ⟶ Γ)
                → (B [ ctxExtIso A .inv (id C , ΣTmIso A B .fun a .fst [ id C ]Tm) ]Ty) [ σ ]Ty
                ≡ (B [ ctxExt .F-hom (σ , refl) ]Ty) [ ctxExtIso (A [ σ ]Ty) .inv (id C , (ΣTmIso A B .fun a .fst [ σ ]Tm) [ id C ]Tm) ]Ty

      ΣTmIsoFunNat : (A : Ty[ Γ ])
                     (B : Ty[ Γ ⋆ A ])
                     (a : Tm[ Γ , ΣTy A B ])
                     (σ : Δ ⟶ Γ)
                   → ( (ΣTmIso A B .fun a .fst) [ σ ]Tm
                     , subst (λ x → Tm[ Δ , x ]) (coerceFun A B a σ) ((ΣTmIso A B .fun a .snd) [ σ ]Tm)  )
                   ≡ ΣTmIso (A [ σ ]Ty) (B [ ctxExt .F-hom (σ , refl) ]Ty) .fun
                            (subst (λ x → Tm[ Δ , x ]) (ΣTyNat A B σ) (a [ σ ]Tm))

      -- The inverse could be nicer? Fording could help even more...

      coerceInv : (A : Ty[ Γ ])
                  (B : Ty[ Γ ⋆ A ])
                  (a : Tm[ Γ , A ])
                  (σ : Δ ⟶ Γ)
                → (B [ inv (ctxExtIso A) (id C , a [ id C ]Tm) ]Ty) [ σ ]Ty
                ≡ (B [ ctxExt .F-hom (σ , refl) ]Ty) [ inv (ctxExtIso (A [ σ ]Ty)) (id C , (a [ σ ]Tm) [ id C ]Tm) ]Ty

      ΣTmIsoInvNat : (A : Ty[ Γ ])
                     (B : Ty[ Γ ⋆ A ])
                     (a : Tm[ Γ , A ])
                     (b : Tm[ Γ , B [ ctxExtIso A .inv (id C , (a [ id C ]Tm)) ]Ty ])
                     (σ : Δ ⟶ Γ)
                   → PathP (λ i → Tm[ Δ , ΣTyNat A B σ i ])
                           (ΣTmIso A B .inv (a , b) [ σ ]Tm)
                           (ΣTmIso (A [ σ ]Ty) (B [ ctxExt .F-hom (σ , refl) ]Ty) .inv
                             (a [ σ ]Tm , subst (λ x → Tm[ Δ , x ]) (coerceInv A B a σ) (b [ σ ]Tm)))
