{-# OPTIONS --lossy-unification #-}
module ACwF-CCwF where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Transport
open import Cubical.Categories.Category

open import ACwF.Base
open import ACwF.FromCCwF
open import CCwF.Base
open import CCwF.FromACwF

module _ {ℓOb ℓHom : Level} {ℓTy ℓTm : Level} {Ctx : Category ℓOb ℓHom} where

  -- | The round trip `CCwF→ACwF ∘ ACwF→CCwF` gives back the original data up to
  --   the transports that `ACwF→CCwF`'s `ctxExtIso` introduces: the generic
  --   variable comes back as `q [ id ]Tm` re-typed along `p ∘ id ≡ p`,
  --   weakening as `((σ ∘ (p ∘ id)) ⁺) ∘ ⟨ q-ish ⟩`, and a section as
  --   `(id ⁺) ∘ ⟨ a [ id ]-ish ⟩`.  The three lemmas below unwind exactly that.
  private
    module RoundTrip (Cw : Algebraic.CwF Ctx ℓTy ℓTm) where

      open Category Ctx
      open Algebraic.CwF Cw

      module RT = Algebraic.CwF (CCwF→ACwF Ctx (ACwF→CCwF Ctx Cw))

      -- | `RT.q` is `q [ id ]Tm` transported back along `[][]Ty A id p`.
      qPath : {Γ : ob} {A : Ty Γ}
            → PathP (λ i → Tm (Γ ▹ A) (A [ ⋆IdL (p {Γ} {A}) i ]Ty)) RT.q q
      qPath {Γ} {A} = reindex (coeP ([][]Ty A id p) _ ∙Tm [id]Tm q)

      -- | `RT.⟨ a ⟩` is `(id ⁺) ∘ ⟨ a ⟩` with `a` re-typed along `[id]Ty A`;
      --   `id⁺` turns `id ⁺` into `id` while the term travels back.
      extPath : {Γ : ob} {A : Ty Γ} (a : Tm Γ A) → RT.⟨ a ⟩ ≡ ⟨ a ⟩
      extPath {Γ} {A} a =
        (λ i → id⁺ {A = A} i ∘ ⟨ coeP ([id]Ty A) a i ⟩) ∙ ⋆IdR ⟨ a ⟩

      -- | `RT._⁺ σ` is `((σ ∘ (p ∘ id)) ⁺) ∘ ⟨ t ⟩` for a `t` built out of
      --   `q [ id ]Tm`.  Sliding `p ∘ id` to `p` puts it in the shape
      --   `((σ ∘ p) ⁺) ∘ ⟨ q ⟩`, which `∘⁺` splits and `p⁺∘⟨q⟩≡id` collapses.
      wkPath : {Γ Δ : ob} {A : Ty Γ} (σ : Ctx [ Δ , Γ ]) → RT._⁺ {A = A} σ ≡ σ ⁺
      wkPath {Γ} {Δ} {A} σ = slide ∙ split ∙ collapse
        where
        D : ob
        D = Δ ▹ A [ σ ]Ty

        -- `q` re-typed as a term of `A [ σ ∘ p ]Ty`
        qσ : Tm D (A [ σ ∘ p ]Ty)
        qσ = subst⁻ (Tm D) ([][]Ty A p σ) q

        -- the term carried by `RT._⁺ σ` travels to `qσ` over `σ ∘ ⋆IdL p`:
        -- undo the two transports, apply `[id]Tm`, then redo the one in `qσ`.
        tPath : PathP (λ i → Tm D (A [ σ ∘ ⋆IdL p i ]Ty)) _ qσ
        tPath = reindex
          (coeP ([][]Ty A (p ∘ id) σ) _
           ∙Tm coeP ([][]Ty (A [ σ ]Ty) id p) _
           ∙Tm [id]Tm q
           ∙Tm symP (coeP ([][]Ty A p σ) q))

        slide : RT._⁺ {A = A} σ ≡ ((σ ∘ p) ⁺) ∘ ⟨ qσ ⟩
        slide i = ((σ ∘ ⋆IdL p i) ⁺) ∘ ⟨ tPath i ⟩

        split : ((σ ∘ p) ⁺) ∘ ⟨ qσ ⟩ ≡ (σ ⁺ ∘ p ⁺) ∘ ⟨ q ⟩
        split i = (∘⁺ {A = A} p σ i) ∘ ⟨ coeP ([][]Ty A p σ) q i ⟩

        collapse : (σ ⁺ ∘ p ⁺) ∘ ⟨ q ⟩ ≡ σ ⁺
        collapse = sym (⋆Assoc ⟨ q ⟩ (p ⁺) (σ ⁺))
                 ∙ cong (σ ⁺ ∘_) p⁺∘⟨q⟩≡id
                 ∙ ⋆IdL (σ ⁺)

  ACwF-Iso-CCwF : Iso (Algebraic.CwF Ctx ℓTy ℓTm) (Categorical.CwF Ctx ℓTy ℓTm)
  ACwF-Iso-CCwF .Iso.fun = ACwF→CCwF Ctx
  ACwF-Iso-CCwF .Iso.inv = CCwF→ACwF Ctx
  ACwF-Iso-CCwF .Iso.sec = {!!}
  ACwF-Iso-CCwF .Iso.ret Cw =
    Algebraic.makeACwFPath Ctx (CCwF→ACwF Ctx (ACwF→CCwF Ctx Cw)) Cw
    refl
    refl
    refl
    refl
    (λ i x σ → substRefl {B = λ z → z} (Cw .Algebraic.CwF._[_]Tm x σ) i)
    refl
    (λ i {Γ} {A} → Ctx .Category.⋆IdL (Cw .Algebraic.CwF.p {Γ} {A}) i)
    (λ i {Γ} {A} → RoundTrip.qPath Cw {Γ} {A} i)
    (λ i {Γ} {Δ} {A} σ → RoundTrip.wkPath Cw {Γ} {Δ} {A} σ i)
    (λ i {Γ} {A} a → RoundTrip.extPath Cw {Γ} {A} a i)

  ACwF≃CCwF : Algebraic.CwF Ctx ℓTy ℓTm ≃ Categorical.CwF Ctx ℓTy ℓTm
  ACwF≃CCwF = isoToEquiv ACwF-Iso-CCwF
