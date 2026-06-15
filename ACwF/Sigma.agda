module ACwF.Sigma where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism

open import Cubical.Categories.Category

open import ACwF.Base

module _ {ℓOb ℓHom ℓTy ℓTm : Level} (C : Category ℓOb ℓHom) (cwf : Algebraic.CwF C ℓTy ℓTm) where

  open Algebraic C
  open CwF cwf

  private variable
    Θ Δ Γ : Ctx

  record Σ-Structure : Type (ℓ-suc (ℓ-max ℓOb (ℓ-max ℓHom (ℓ-max ℓTy  ℓTm)))) where

    field
      ΣTy : (A : Ty Γ) (B : Ty (Γ ✦ A)) → Ty Γ

      ΣTyNat : (A : Ty Γ) (B : Ty (Γ ✦ A)) (σ : Δ ⟶ Γ)
             → (ΣTy A B) [ σ ]Ty ≡ ΣTy (A [ σ ]Ty) (B [ σ ⁺ ]Ty)

      ΣTmIso : (A : Ty Γ) (B : Ty (Γ ✦ A))
             → Iso (Tm Γ (ΣTy A B)) (Σ[ a ∈ Tm Γ A ] Tm Γ (B [ ⟨ a ⟩ ]Ty))

      coerce : (A : Ty Γ) (B : Ty (Γ ✦ A)) (a : Tm Γ A) (σ : Δ ⟶ Γ)
             → (B [ ⟨ a ⟩ ]Ty) [ σ ]Ty ≡ (B [ σ ⁺ ]Ty) [ ⟨ a [ σ ]Tm ⟩ ]Ty

      ΣTmIsoInvNat : (A : Ty Γ)
                     (B : Ty (Γ ✦ A))
                     (a : Tm Γ A)
                     (b : Tm Γ (B [ ⟨ a ⟩ ]Ty))
                     (σ : Δ ⟶ Γ)
                   → PathP (λ i → Tm Δ (ΣTyNat A B σ i))
                           (ΣTmIso A B .Iso.inv (a , b) [ σ ]Tm)
                           (ΣTmIso (A [ σ ]Ty) (B [ σ ⁺ ]Ty) .Iso.inv
                                   (a [ σ ]Tm , subst (Tm Δ) (coerce A B a σ) (b [ σ ]Tm)))
