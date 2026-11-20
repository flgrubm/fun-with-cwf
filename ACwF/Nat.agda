module ACwF.Nat where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category
open import ACwF.Base

module _ {ℓOb ℓHom ℓTy ℓTm : Level} {C : Category ℓOb ℓHom} (cwf : Algebraic.CwF C ℓTy ℓTm) where

  open Category C hiding (_⋆_)
  open Algebraic C
  open CwF cwf

  private variable
    Θ Δ Γ : Ctx

  record ℕ-Ops : Type (ℓ-max ℓOb (ℓ-max ℓHom (ℓ-max ℓTy ℓTm))) where
    field
      ℕTy : Ty Γ
      ℕzero : Tm Γ ℕTy
      -- an internal definition of suc. morally "suc n" is `ℕsuc [ ⟨ n ⟩ ]`.
      ℕsuc : Tm (Γ ▹ ℕTy) (ℕTy [ p ]Ty)

      ℕTyNat : (σ : Δ ⟶ Γ) → ℕTy [ σ ]Ty ≡ ℕTy

    _↑ : (σ : Δ ⟶ Γ) → Δ ▹ ℕTy ⟶ Γ ▹ ℕTy
    σ ↑ = subst (λ X → _ ▹ X ⟶ _ ▹ ℕTy) (ℕTyNat σ) (σ ⁺)
    -- the substitution (γ, n) ↦ (γ, suc n)
    suc⁺ : Γ ▹ ℕTy ⟶ Γ ▹ ℕTy
    suc⁺ =  p ⁺ ∘ ⟨ ℕsuc ⟩
    -- to go from `A n` to `A (suc n)`
    sucσ : ∀ {A} → Γ ▹ ℕTy ▹ A ⟶ Γ ▹ ℕTy
    sucσ = suc⁺ ∘ p

  module _ (ℕ-Ops-field : ℕ-Ops) where
    open ℕ-Ops ℕ-Ops-field

    ℕ-ElimTy : Type (ℓ-max ℓOb (ℓ-max ℓTy ℓTm))
    ℕ-ElimTy = ∀ {Γ} A
      → (Az : Tm Γ (A [ ⟨ ℕzero ⟩ ]Ty))
      → (As : Tm (Γ ▹ ℕTy ▹ A) (A [ sucσ ]Ty))
      → Tm (Γ ▹ ℕTy) A

    -- naturality of `elim` along `σ ↑`, the reindexed arguments being related
    -- to the new ones over the type paths `P` and `Q`
    ℕ-ElimNatOver : (elim : ℕ-ElimTy) (A : Ty (Γ ▹ ℕTy)) (σ : Δ ⟶ Γ)
      (Az : Tm Γ (A [ ⟨ ℕzero ⟩ ]Ty)) (As : Tm (Γ ▹ ℕTy ▹ A) (A [ sucσ ]Ty))
      → A [ ⟨ ℕzero ⟩ ]Ty [ σ ]Ty ≡ A [ σ ↑ ]Ty [ ⟨ ℕzero ⟩ ]Ty
      → A [ sucσ {A = A} ]Ty [ σ ↑ ⁺ ]Ty ≡ A [ σ ↑ ]Ty [ sucσ {A = A [ σ ↑ ]Ty} ]Ty
      → Type ℓTm
    ℕ-ElimNatOver elim A σ Az As P Q = ∀ Az' As'
      → PathP (λ i → Tm _ (P i)) (Az [ σ ]Tm) Az'
      → PathP (λ i → Tm _ (Q i)) (As [ σ ↑ ⁺ ]Tm) As'
      → elim A Az As [ σ ↑ ]Tm ≡ elim (A [ σ ↑ ]Ty) Az' As'

    -- types form a set, so `ℕ-ElimNatOver` may be proved over any type paths
    mkElimNatOver : ∀ {elim : ℕ-ElimTy} {A} {σ : Δ ⟶ Γ} {Az As P Q P' Q'}
      → ℕ-ElimNatOver elim A σ Az As P Q → ℕ-ElimNatOver elim A σ Az As P' Q'
    mkElimNatOver h Az' As' pz ps = h Az' As' (reindex pz) (reindex ps)

  record ℕ-Structure : Type (ℓ-max ℓOb (ℓ-max ℓHom (ℓ-max ℓTy ℓTm))) where
    field
      ℕ-Ops-field : ℕ-Ops
    open ℕ-Ops ℕ-Ops-field public
    field
      -- this is equivalent to `ℕzero [ σ ] ≡ ℕzero` (over naturality of ℕTy)
      ℕzeroNat : (σ : Δ ⟶ Γ) → ⟨ ℕzero ⟩ ∘ σ ≡ σ ↑ ∘ ⟨ ℕzero ⟩
      -- same, but along `σ ↑`
      ℕsucNat  : (σ : Δ ⟶ Γ) → suc⁺ ∘ σ ↑ ≡ σ ↑ ∘ suc⁺

    -- `sucσ ∘ ⟨ a ⟩` forgets `a`, leaving `suc⁺`
    [sucσ][⟨⟩]Ty : (A : Ty (Γ ▹ ℕTy)) (a : Tm (Γ ▹ ℕTy) A)
                 → A [ sucσ ]Ty [ ⟨ a ⟩ ]Ty ≡ A [ suc⁺ ]Ty
    [sucσ][⟨⟩]Ty A a = sym ([][]Ty A ⟨ a ⟩ sucσ)
      ∙ cong (A [_]Ty) (sym (⋆Assoc ⟨ a ⟩ p suc⁺) ∙ cong (suc⁺ ∘_) (p∘⟨⟩≡id a) ∙ ⋆IdL suc⁺)

    [⟨ℕzero⟩][]Ty : (A : Ty (Γ ▹ ℕTy)) (σ : Δ ⟶ Γ)
                  → A [ ⟨ ℕzero ⟩ ]Ty [ σ ]Ty ≡ A [ σ ↑ ]Ty [ ⟨ ℕzero ⟩ ]Ty
    [⟨ℕzero⟩][]Ty A σ = sym ([][]Ty A σ ⟨ ℕzero ⟩) ∙ cong (A [_]Ty) (ℕzeroNat σ) ∙ [][]Ty A ⟨ ℕzero ⟩ (σ ↑)

    -- `sucσ` commutes with lifting `σ`, by `ℕsucNat`
    [sucσ][↑⁺]Ty : (A : Ty (Γ ▹ ℕTy)) (σ : Δ ⟶ Γ)
                 → A [ sucσ {A = A} ]Ty [ σ ↑ ⁺ ]Ty ≡ A [ σ ↑ ]Ty [ sucσ {A = A [ σ ↑ ]Ty} ]Ty
    [sucσ][↑⁺]Ty A σ = sym ([][]Ty A (σ ↑ ⁺) sucσ)
      ∙ cong (A [_]Ty) ( sym (⋆Assoc (σ ↑ ⁺) p suc⁺)
                       ∙ cong (suc⁺ ∘_) (p∘⁺ (σ ↑))
                       ∙ ⋆Assoc p (σ ↑) suc⁺
                       ∙ cong (_∘ p {A = A [ σ ↑ ]Ty}) (ℕsucNat σ)
                       ∙ sym (⋆Assoc p suc⁺ (σ ↑)))
      ∙ [][]Ty A sucσ (σ ↑)

    field
      ℕ-elim : ℕ-ElimTy ℕ-Ops-field
      ℕ-elimβ-z : ∀ A Az As →
        ℕ-elim {Γ} A Az As [ ⟨ ℕzero ⟩ ]Tm ≡ Az
      ℕ-elimβ-s : ∀ A Az As →
        let elim = ℕ-elim {Γ} A Az As in
        PathP (λ i → Tm (Γ ▹ ℕTy) ([sucσ][⟨⟩]Ty A elim i))
          (As [ ⟨ elim ⟩ ]Tm)
          (elim [ suc⁺ ]Tm)
      -- `mkElimNatOver` lets this be proved over more convenient type paths
      ℕ-elimNat : ∀ A (σ : Δ ⟶ Γ) Az As →
        ℕ-ElimNatOver ℕ-Ops-field ℕ-elim A σ Az As ([⟨ℕzero⟩][]Ty A σ) ([sucσ][↑⁺]Ty A σ)
