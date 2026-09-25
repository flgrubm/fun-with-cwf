module ACwF.Empty where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Categories.Category
open import Cubical.Data.Empty
open import ACwF.Base

module _ {ℓOb ℓHom ℓTy ℓTm : Level} {C : Category ℓOb ℓHom} (cwf : Algebraic.CwF C ℓTy ℓTm) where

  open Algebraic C
  open CwF cwf

  private variable
    Θ Δ Γ : Ctx

  record ⊥-Structure : Type (ℓ-max ℓOb (ℓ-max ℓHom (ℓ-max ℓTy ℓTm))) where
    field
      ⊥Ty : Ty Γ
      ⊥TyNat : (σ : Δ ⟶ Γ) → ⊥Ty [ σ ]Ty ≡ ⊥Ty
      ⊥TmIso : Iso (Tm Γ ⊥Ty) ⊥
      ⊥TmIsoInvNat : (t : ⊥) (σ : Δ ⟶ Γ)
        → PathP (λ i → Tm Δ (⊥TyNat σ i))
            (⊥TmIso .Iso.inv t [ σ ]Tm)
            (⊥TmIso .Iso.inv t)
