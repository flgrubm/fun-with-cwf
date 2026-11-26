-- | The recursor out of the syntax into an arbitrary CwF `M`, by pattern
-- matching on `Syn`.  The meaning of a sort, `El`, is computed together with
-- the interpretation itself, since the meaning of `tm A` mentions the
-- interpretation of `A`.  The substitution constructors go to the
-- comprehension structure that `ACwF.Comprehension` derives in `M`.
open import Cubical.Foundations.Prelude hiding (Sub)
open import Cubical.Categories.Category
open import ACwF.Base

module ACwF.Instances.Syntax.Rec {ℓOb ℓHom ℓTy ℓTm : Level} {C : Category ℓOb ℓHom}
  (M : Algebraic.CwF C ℓTy ℓTm) where

open import Cubical.Categories.Functor
open import ACwF.Morphism
import ACwF.Comprehension
open import ACwF.Instances.Syntax.Base
open import ACwF.Instances.Syntax.CwF

private variable
  Θ Δ Γ Ξ : Con

module ℂ = Category C
module 𝕄 = Algebraic.CwF M
module ℙ = ACwF.Comprehension M

lvl : Sort Γ → Level
lvl ty      = ℓTy
lvl (sub _) = ℓHom
lvl (tm _)  = ℓTm

⟦_⟧C  : Con → ℂ.ob
El    : (s : Sort Γ) → Type (lvl s)
isSetEl : (s : Sort Γ) → isSet (El s)
⟦_⟧   : {s : Sort Γ} → Syn Γ s → El s

-- `El` first: its clauses only mention `⟦_⟧C`/`⟦_⟧`, while theirs need
-- `El` to compute.
El {Γ = Γ} ty      = 𝕄.Ty ⟦ Γ ⟧C
El {Γ = Γ} (sub Δ) = C [ ⟦ Γ ⟧C , ⟦ Δ ⟧C ]
El {Γ = Γ} (tm A)  = 𝕄.Tm ⟦ Γ ⟧C ⟦ A ⟧

isSetEl ty      = 𝕄.isSetTy _
isSetEl (sub _) = ℂ.isSetHom
isSetEl (tm _)  = 𝕄.isSetTm _ _

⟦ ◇ ⟧C     = 𝕄.⟨⟩ .fst
⟦ Γ ▹ A ⟧C = ⟦ Γ ⟧C 𝕄.▹ ⟦ A ⟧

⟦ id ⟧               = ℂ.id
⟦ σ ∘ δ ⟧            = ⟦ σ ⟧ ℂ.∘ ⟦ δ ⟧
⟦ idr σ i ⟧          = ℂ.⋆IdL ⟦ σ ⟧ i
⟦ idl σ i ⟧          = ℂ.⋆IdR ⟦ σ ⟧ i
⟦ assoc ν δ σ i ⟧    = ℂ.⋆Assoc ⟦ ν ⟧ ⟦ δ ⟧ ⟦ σ ⟧ i
⟦ A [ σ ]Ty ⟧        = ⟦ A ⟧ 𝕄.[ ⟦ σ ⟧ ]Ty
⟦ [id]Ty A i ⟧       = 𝕄.[id]Ty ⟦ A ⟧ i
⟦ [][]Ty A σ' σ i ⟧  = 𝕄.[][]Ty ⟦ A ⟧ ⟦ σ' ⟧ ⟦ σ ⟧ i
⟦ a [ σ ]Tm ⟧        = ⟦ a ⟧ 𝕄.[ ⟦ σ ⟧ ]Tm
⟦ [id]Tm a i ⟧       = 𝕄.[id]Tm ⟦ a ⟧ i
⟦ [][]Tm a σ' σ i ⟧  = 𝕄.[][]Tm ⟦ a ⟧ ⟦ σ' ⟧ ⟦ σ ⟧ i
⟦ ε ⟧                = 𝕄.⟨⟩ .snd _ .fst
⟦ εη σ i ⟧           = 𝕄.⟨⟩ .snd _ .snd ⟦ σ ⟧ i
⟦ σ , t ⟧            = ℙ.pair ⟦ σ ⟧ ⟦ t ⟧
⟦ π₁ τ ⟧             = 𝕄.p ℂ.∘ ⟦ τ ⟧
⟦ π₂ τ ⟧             = ℙ.π₂ ⟦ τ ⟧
⟦ π₁β σ t i ⟧        = ℙ.π₁β ⟦ σ ⟧ ⟦ t ⟧ i
⟦ π₂β σ t i ⟧        = ℙ.π₂β ⟦ σ ⟧ ⟦ t ⟧ i
⟦ πη τ i ⟧           = ℙ.πη ⟦ τ ⟧ i
⟦ ,∘ σ t ν t' P i ⟧  = ℙ.pair∘ ⟦ σ ⟧ ⟦ t ⟧ ⟦ ν ⟧ ⟦ t' ⟧ (λ j → ⟦ P j ⟧) i
⟦ trunc {s = s} x y e e' i j ⟧ =
  isSetEl s ⟦ x ⟧ ⟦ y ⟧ (cong ⟦_⟧ e) (cong ⟦_⟧ e') i j

-- `p = π₁ id` and `q = π₂ id` are interpreted up to `p ∘ id ≡ p`.
⟦p⟧ : {A : Ty Γ} → ⟦ p {A = A} ⟧ ≡ 𝕄.p
⟦p⟧ = ℂ.⋆IdL 𝕄.p

⟦q⟧ : {A : Ty Γ}
    → PathP (λ i → 𝕄.Tm ⟦ Γ ▹ A ⟧C (⟦ A ⟧ 𝕄.[ ⟦p⟧ {A = A} i ]Ty)) ⟦ q {A = A} ⟧ 𝕄.q
⟦q⟧ {Γ = Γ} {A = A} = 𝕄.reindex
  (ℙ.π₂≡q[] (ℂ.id {⟦ Γ ▹ A ⟧C}) 𝕄.∙Tm 𝕄.[id]Tm (𝕄.q {A = ⟦ A ⟧}))

⟦_⟧F : Functor SynConCategory C
⟦_⟧F = record
  { F-ob  = ⟦_⟧C
  ; F-hom = ⟦_⟧
  ; F-id  = refl
  ; F-seq = λ _ _ → refl
  }

rec : CwFMorphism SynConCategory C Syn-CwF M
rec = record
  { ctxMorph      = ⟦_⟧F
  ; tyMorph       = ⟦_⟧
  ; tmMorph       = ⟦_⟧
  ; preserves⟨⟩   = refl
  ; preserves[]Ty = λ _ → refl
  ; preserves[]Tm = λ _ → refl
  ; preserves▹    = λ _ _ → refl
  ; preservesp    = λ {Γ} {A} → ⟦p⟧ {Γ = Γ} {A = A}
  ; preservesq    = λ {Γ} {A} → 𝕄.reindex (⟦q⟧ {Γ = Γ} {A = A})
  }

