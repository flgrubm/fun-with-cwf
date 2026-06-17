module ACwF.Pi where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism

open import Cubical.Categories.Category

open import ACwF.Base

open Iso

module _ {ℓOb ℓHom ℓTy ℓTm : Level} (C : Category ℓOb ℓHom) (cwf : Algebraic.CwF C ℓTy ℓTm) where

  open Algebraic C
  open CwF cwf

  private variable
    Θ Δ Γ : Ctx

  record Π-Structure : Type (ℓ-suc (ℓ-max ℓOb (ℓ-max ℓHom (ℓ-max ℓTy  ℓTm)))) where

    field
      ΠTy : (A : Ty Γ) (B : Ty (Γ ▹ A)) → Ty Γ

      ΠTyNat : (A : Ty Γ) (B : Ty (Γ ▹ A)) (σ : Δ ⟶ Γ)
             → (ΠTy A B) [ σ ]Ty ≡ ΠTy (A [ σ ]Ty) (B [ σ ⁺ ]Ty)

      ΠTmIso : (A : Ty Γ) (B : Ty (Γ ▹ A))
             → Iso (Tm Γ (ΠTy A B)) (Tm (Γ ▹ A) B)

      -- ΠTmIsoNat : (A : Ty Γ)
      --             (B : Ty (Γ ⋆ A))
      --             (F : Tm Γ (ΠTy A B))
      --             (σ : Δ ⟶ Γ)
      --           → {!ΠTmIso A B .fun F [ σ ⁺ ]Tm!}
                     
      ΠTmIsoInvNat : (A : Ty Γ)
                  (B : Ty (Γ ▹ A))
                  (f : Tm (Γ ▹ A) B)
                  (σ : Δ ⟶ Γ)
                → PathP (λ i → Tm Δ (ΠTyNat A B σ i))
                        (ΠTmIso A B .inv f [ σ ]Tm)
                        (ΠTmIso (A [ σ ]Ty) (B [ σ ⁺ ]Ty) .inv (f [ σ ⁺ ]Tm))
