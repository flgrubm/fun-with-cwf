module ACwF.Unit where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Categories.Category
open import Cubical.Data.Unit
open import ACwF.Base

module _ {ℓOb ℓHom ℓTy ℓTm : Level} {C : Category ℓOb ℓHom} (cwf : Algebraic.CwF C ℓTy ℓTm) where

  open Algebraic C
  open CwF cwf

  private variable
    Θ Δ Γ : Ctx

  record Unit-Structure : Type (ℓ-max ℓOb (ℓ-max ℓHom (ℓ-max ℓTy ℓTm))) where
    field
      UnitTy : Ty Γ
      UnitTyNat : (σ : Δ ⟶ Γ) → UnitTy [ σ ]Ty ≡ UnitTy
      UnitTmIso : Iso (Tm Γ UnitTy) Unit
      UnitTmIsoInvNat : (t : Unit) (σ : Δ ⟶ Γ)
        → PathP (λ i → Tm Δ (UnitTyNat σ i))
            (UnitTmIso .Iso.inv t [ σ ]Tm)
            (UnitTmIso .Iso.inv t)
