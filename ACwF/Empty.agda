module ACwF.Empty where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Isomorphism
open import Cubical.Categories.Category
open import Cubical.Data.Empty
open import ACwF.Base
open import ACwF.Eq

module _ {ℓOb ℓHom ℓTy ℓTm : Level} {C : Category ℓOb ℓHom} (cwf : Algebraic.CwF C ℓTy ℓTm) where

  open Algebraic C
  open CwF cwf

  private variable
    Θ Δ Γ : Ctx

  private level = ℓ-max ℓOb (ℓ-max ℓHom (ℓ-max ℓTy ℓTm))

  record ⊥-Structure : Type level where
    field
      ⊥Ty : Ty Γ
      ⊥TyNat : (σ : Δ ⟶ Γ) → ⊥Ty [ σ ]Ty ≡ ⊥Ty
      ⊥-elim : ∀ A → Tm (Γ ▹ ⊥Ty) A
    _↑ : (σ : Δ ⟶ Γ) → Δ ▹ ⊥Ty ⟶ Γ ▹ ⊥Ty
    σ ↑ = subst (λ X → _ ▹ X ⟶ _ ▹ ⊥Ty) (⊥TyNat σ) (σ ⁺)
    field
      ⊥-elimNat : ∀ A (σ : Δ ⟶ Γ) → ⊥-elim (A [ σ ↑ ]Ty) ≡ ⊥-elim A [ σ ↑ ]Tm

  record ⊥-Strong (⊥ : ⊥-Structure) : Type level where
    open ⊥-Structure ⊥
    field
      ⊥-elimη : ∀ A → (x : Tm (Γ ▹ ⊥Ty) A) → x ≡ ⊥-elim A

  ⊥-Eq+Weak→Strong : Eq-Structure cwf → (⊥ : ⊥-Structure) → ⊥-Strong ⊥
  ⊥-Eq+Weak→Strong E ⊥ .⊥-Strong.⊥-elimη A x =
    EqTmIso A x (⊥-elim A) .Iso.fun
      (⊥-elim (EqTy A x (⊥-elim A)))
    where
      open Eq-Structure E
      open ⊥-Structure ⊥
