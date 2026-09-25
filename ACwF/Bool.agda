module ACwF.Bool where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Categories.Category
open import Cubical.Data.Bool
open import ACwF.Base

module _ {ℓOb ℓHom ℓTy ℓTm : Level} {C : Category ℓOb ℓHom} (cwf : Algebraic.CwF C ℓTy ℓTm) where

  open Algebraic C
  open CwF cwf

  private variable
    Θ Δ Γ : Ctx

  record Unit-Structure : Type (ℓ-max ℓOb (ℓ-max ℓHom (ℓ-max ℓTy ℓTm))) where
    field
      BoolTy : Ty Γ
      BoolTyNat : (σ : Δ ⟶ Γ) → BoolTy [ σ ]Ty ≡ BoolTy
      BoolTmIso : Iso (Tm Γ BoolTy) Bool
      BoolTmIsoInvNat : (b : Bool) (σ : Δ ⟶ Γ)
        → PathP (λ i → Tm Δ (BoolTyNat σ i))
            (BoolTmIso .Iso.inv b [ σ ]Tm)
            (BoolTmIso .Iso.inv b)
