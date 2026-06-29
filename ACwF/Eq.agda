module ACwF.Eq where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Categories.Category
open import ACwF.Base

module _ {ℓTy ℓTm ℓOb ℓHom : Level} {C : Category ℓOb ℓHom} (cwf : Algebraic.CwF C ℓTy ℓTm) where

  open Algebraic C
  open CwF cwf

  private variable
    Θ Δ Γ : Ctx

  record Eq-Structure : Type (ℓ-max ℓOb (ℓ-max ℓHom (ℓ-max ℓTy ℓTm))) where
    field
      EqTy : (A : Ty Γ) → (a b : Tm Γ A) → Ty Γ
      EqTyNat : (A : Ty Γ) (a b : Tm Γ A) (σ : Δ ⟶ Γ)
              → (EqTy A a b) [ σ ]Ty ≡ EqTy (A [ σ ]Ty) (a [ σ ]Tm) (b [ σ ]Tm)
      EqTmIso : (A : Ty Γ) (a b : Tm Γ A)
              → Iso (Tm Γ (EqTy A a b)) (a ≡ b)
      EqTmIsoInvNat : (A : Ty Γ)
                      (a b : Tm Γ A)
                      (p : a ≡ b)
                      (σ : Δ ⟶ Γ)
                    → PathP (λ i → Tm Δ (EqTyNat A a b σ i))
                        (EqTmIso A a b .Iso.inv p [ σ ]Tm)
                        (EqTmIso (A [ σ ]Ty) (a [ σ ]Tm) (b [ σ ]Tm) .Iso.inv (cong (_[ σ ]Tm) p))
