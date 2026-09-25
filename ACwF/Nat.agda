module ACwF.Nat where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Categories.Category
open import Cubical.Data.Nat
open import ACwF.Base

module _ {ℓOb ℓHom ℓTy ℓTm : Level} {C : Category ℓOb ℓHom} (cwf : Algebraic.CwF C ℓTy ℓTm) where

  open Algebraic C
  open CwF cwf

  private variable
    Θ Δ Γ : Ctx

  record ℕ-Structure : Type (ℓ-max ℓOb (ℓ-max ℓHom (ℓ-max ℓTy ℓTm))) where
    field
      ℕTy : Ty Γ
      ℕTyNat : (σ : Δ ⟶ Γ) → ℕTy [ σ ]Ty ≡ ℕTy
      ℕTmIso : Iso (Tm Γ ℕTy) ℕ
      ℕTmIsoInvNat : (n : ℕ) (σ : Δ ⟶ Γ)
        → PathP (λ i → Tm Δ (ℕTyNat σ i))
            (ℕTmIso .Iso.inv n [ σ ]Tm)
            (ℕTmIso .Iso.inv n)
