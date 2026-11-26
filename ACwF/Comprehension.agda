-- | Comprehension in a Pitts-style CwF, in the style of Altenkirch–Kaposi:
-- pairing `pair σ t : Δ ⟶ Γ ▹ A` with projections `p ∘ τ` and `π₂ τ`, and
-- their β/η laws and naturality, derived from the laws of `ACwF.Base`.
-- This is what interprets the substitution constructors of
-- `ACwF.Instances.Syntax` in an arbitrary CwF.
open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category
open import ACwF.Base

module ACwF.Comprehension {ℓOb ℓHom ℓTy ℓTm : Level} {C : Category ℓOb ℓHom}
  (cwf : Algebraic.CwF C ℓTy ℓTm) where

open import Cubical.Foundations.Transport using (subst⁻)

open Category C
open Algebraic C
open Algebraic.CwF cwf

private variable
  Θ Δ Γ : Ctx

-- Opaque: both contain a transport (via `⟨_⟩` resp. `subst⁻`), which Agda
-- would otherwise unfold when comparing types that mention them.
opaque
  pair : {A : Ty Γ} (σ : Δ ⟶ Γ) → Tm Δ (A [ σ ]Ty) → Δ ⟶ Γ ▹ A
  pair σ t = σ ⁺ ∘ ⟨ t ⟩

  π₂ : {A : Ty Γ} (τ : Δ ⟶ Γ ▹ A) → Tm Δ (A [ p ∘ τ ]Ty)
  π₂ {A = A} τ = subst⁻ (Tm _) ([][]Ty A τ p) (q [ τ ]Tm)

  π₂≡q[] : {A : Ty Γ} (τ : Δ ⟶ Γ ▹ A)
         → PathP (λ i → Tm Δ ([][]Ty A τ p i)) (π₂ τ) (q [ τ ]Tm)
  π₂≡q[] {A = A} τ = coeP ([][]Ty A τ p) (q [ τ ]Tm)

  π₁β : {A : Ty Γ} (σ : Δ ⟶ Γ) (t : Tm Δ (A [ σ ]Ty)) → p ∘ pair σ t ≡ σ
  π₁β σ t = ⋆Assoc ⟨ t ⟩ (σ ⁺) p
          ∙ cong (_∘ ⟨ t ⟩) (p∘⁺ σ)
          ∙ sym (⋆Assoc ⟨ t ⟩ p σ)
          ∙ cong (σ ∘_) (p∘⟨⟩≡id t)
          ∙ ⋆IdL σ

  π₂β : {A : Ty Γ} (σ : Δ ⟶ Γ) (t : Tm Δ (A [ σ ]Ty))
      → PathP (λ i → Tm Δ (A [ π₁β σ t i ]Ty)) (π₂ (pair σ t)) t
  π₂β σ t = reindex
    (   π₂≡q[] (pair σ t)
    ∙Tm [][]Tm q ⟨ t ⟩ (σ ⁺)
    ∙Tm congP (λ _ x → x [ ⟨ t ⟩ ]Tm) (q[⁺]Tm σ)
    ∙Tm q[⟨⟩]Tm t)

  πη : {A : Ty Γ} (τ : Δ ⟶ Γ ▹ A) → pair (p ∘ τ) (π₂ τ) ≡ τ
  πη τ = (λ i → ∘⁺ τ p i ∘ ⟨ π₂≡q[] τ i ⟩)
       ∙ sym (⋆Assoc ⟨ q [ τ ]Tm ⟩ (τ ⁺) (p ⁺))
       ∙ cong (p ⁺ ∘_) (sym (⟨⟩∘ q τ))
       ∙ ⋆Assoc τ ⟨ q ⟩ (p ⁺)
       ∙ cong (_∘ τ) p⁺∘⟨q⟩≡id
       ∙ ⋆IdR τ

  -- AK's `,∘`, with the coerced term abstracted over its defining path, as in
  -- the syntax.
  pair∘ : {A : Ty Γ} (σ : Δ ⟶ Γ) (t : Tm Δ (A [ σ ]Ty)) (ν : Θ ⟶ Δ)
          (t' : Tm Θ (A [ σ ∘ ν ]Ty))
        → PathP (λ i → Tm Θ ([][]Ty A ν σ i)) t' (t [ ν ]Tm)
        → pair σ t ∘ ν ≡ pair (σ ∘ ν) t'
  pair∘ σ t ν t' P = sym (⋆Assoc ν ⟨ t ⟩ (σ ⁺))
                   ∙ cong (σ ⁺ ∘_) (⟨⟩∘ t ν)
                   ∙ ⋆Assoc ⟨ t [ ν ]Tm ⟩ (ν ⁺) (σ ⁺)
                   ∙ sym (λ i → ∘⁺ ν σ i ∘ ⟨ P i ⟩)
