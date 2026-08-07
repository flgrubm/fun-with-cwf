module CCwF.FromACwF where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Transport

open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Limits.Terminal

open import Cubical.Categories.Presheaf
open import Cubical.Categories.Functor
import Cubical.Categories.Instances.Elements as Els
open Els.Contravariant

open import ACwF.Base
open import CCwF.Base

module _ {ℓOb ℓHom ℓTy ℓTm : Level} (C : Category ℓOb ℓHom) (X : Algebraic.CwF C ℓTy ℓTm) where

  open Category C

  open Algebraic.CwF X
  open Functor
  open Iso

  -- | The universal property of context extension, packaged as an explicit
  -- `Iso`.  It is phrased entirely in `X`'s own vocabulary — nothing here
  -- mentions `ACwF→CCwF` — so the copattern block below may use it without
  -- upsetting the termination checker.  `Categorical.CwF` is deliberately
  -- opened only *after* it: otherwise `_▹_`, `p` and `q` would be ambiguous
  -- between the two presentations.
  private
    ctxExtIsoA : {Γ Δ : ob} (A : Ty Γ)
               → Iso Hom[ Δ , Γ ▹ A ] (Σ[ σ ∈ Hom[ Δ , Γ ] ] Tm Δ (A [ σ ]Ty))
    ctxExtIsoA A .fun σ .fst = p ∘ σ
    ctxExtIsoA {Δ = Δ} A .fun σ .snd = subst⁻ (Tm Δ) ([][]Ty A σ p) (q [ σ ]Tm)
    ctxExtIsoA A .inv (σ , t) = (σ ⁺) ∘ ⟨ t ⟩
    ctxExtIsoA {Γ} {Δ} A .sec (σ , t) = ΣPathP (secFst , secSnd)
      where
      τ : Hom[ Δ , Γ ▹ A ]
      τ = (σ ⁺) ∘ ⟨ t ⟩

      u : Tm Δ (A [ p ∘ τ ]Ty)
      u = subst⁻ (Tm Δ) ([][]Ty A τ p) (q [ τ ]Tm)

      secFst : p ∘ τ ≡ σ
      secFst = p ∘ ((σ ⁺) ∘ ⟨ t ⟩) ≡⟨ ⋆Assoc _ _ _ ⟩
               (p ∘ (σ ⁺)) ∘ ⟨ t ⟩ ≡⟨ cong (_∘ ⟨ t ⟩) (p∘⁺ σ) ⟩
               (σ ∘ p) ∘ ⟨ t ⟩     ≡⟨ sym (⋆Assoc _ _ _) ⟩
               σ ∘ (p ∘ ⟨ t ⟩)     ≡⟨ cong (σ ∘_) (p∘⟨⟩≡id t) ⟩
               σ ∘ id              ≡⟨ ⋆IdL σ ⟩
               σ ∎

      S1 : A [ p ]Ty [ τ ]Ty ≡ A [ p ]Ty [ σ ⁺ ]Ty [ ⟨ t ⟩ ]Ty
      S1 = [][]Ty (A [ p ]Ty) ⟨ t ⟩ (σ ⁺)

      R : A [ p ]Ty [ τ ]Ty ≡ A [ σ ]Ty
      R = S1 ∙ (cong (_[ ⟨ t ⟩ ]Ty) ([p][⁺]Ty A σ) ∙ [p][⟨⟩]Ty (A [ σ ]Ty) t)

      Q1 : PathP (λ i → Tm Δ (S1 i)) (q [ τ ]Tm) (q [ σ ⁺ ]Tm [ ⟨ t ⟩ ]Tm)
      Q1 = [][]Tm q ⟨ t ⟩ (σ ⁺)

      Q2 : PathP (λ i → Tm Δ ([p][⁺]Ty A σ i [ ⟨ t ⟩ ]Ty))
                 (q [ σ ⁺ ]Tm [ ⟨ t ⟩ ]Tm) (q [ ⟨ t ⟩ ]Tm)
      Q2 = congP (λ i z → z [ ⟨ t ⟩ ]Tm) (q[⁺]Tm σ)

      Q3 : PathP (λ i → Tm Δ ([p][⟨⟩]Ty (A [ σ ]Ty) t i)) (q [ ⟨ t ⟩ ]Tm) t
      Q3 = q[⟨⟩]Tm t

      Q : PathP (λ i → Tm Δ (R i)) (q [ τ ]Tm) t
      Q = Q1 ∙Tm Q2 ∙Tm Q3

      secSnd : PathP (λ i → Tm Δ (A [ secFst i ]Ty)) u t
      secSnd = toPathP (
        subst (Tm Δ) (cong (A [_]Ty) secFst) u
          ≡⟨ sym (substComposite (Tm Δ) (sym ([][]Ty A τ p)) (cong (A [_]Ty) secFst) (q [ τ ]Tm)) ⟩
        subst (Tm Δ) (sym ([][]Ty A τ p) ∙ cong (A [_]Ty) secFst) (q [ τ ]Tm)
          ≡⟨ cong (λ z → subst (Tm Δ) z (q [ τ ]Tm))
                  (isSetTy Δ _ _ (sym ([][]Ty A τ p) ∙ cong (A [_]Ty) secFst) R) ⟩
        subst (Tm Δ) R (q [ τ ]Tm)
          ≡⟨ fromPathP Q ⟩
        t ∎)
    ctxExtIsoA {Γ} {Δ} A .ret τ =
      ((p ∘ τ) ⁺) ∘ ⟨ w ⟩
        ≡⟨ firstStep ⟩
      (p ⁺ ∘ τ ⁺) ∘ ⟨ q [ τ ]Tm ⟩
        ≡⟨ sym (⋆Assoc _ _ _) ⟩
      p ⁺ ∘ (τ ⁺ ∘ ⟨ q [ τ ]Tm ⟩)
        ≡⟨ cong (p ⁺ ∘_) (sym (⟨⟩∘ q τ)) ⟩
      p ⁺ ∘ (⟨ q ⟩ ∘ τ)
        ≡⟨ ⋆Assoc _ _ _ ⟩
      (p ⁺ ∘ ⟨ q ⟩) ∘ τ
        ≡⟨ cong (_∘ τ) p⁺∘⟨q⟩≡id ⟩
      id ∘ τ
        ≡⟨ ⋆IdR τ ⟩
      τ ∎
      where
      w : Tm Δ (A [ p ∘ τ ]Ty)
      w = subst⁻ (Tm Δ) ([][]Ty A τ p) (q [ τ ]Tm)

      wPath : PathP (λ i → Tm Δ ([][]Ty A τ p i)) w (q [ τ ]Tm)
      wPath = symP (subst-filler (Tm Δ) (sym ([][]Ty A τ p)) (q [ τ ]Tm))

      firstStep : ((p ∘ τ) ⁺) ∘ ⟨ w ⟩ ≡ (p ⁺ ∘ τ ⁺) ∘ ⟨ q [ τ ]Tm ⟩
      firstStep i = (∘⁺ {A = A} τ p i) ∘ ⟨ wPath i ⟩

    -- | `ctxExtIsoA .fun` is the record's `⟨p,q⟩` up to the `transport refl`
    -- that the CCwF term substitution (`Tm ⟪ τ , refl ⟫`) inserts.
    funPath : {Γ Δ : ob} (A : Ty Γ) (τ : Hom[ Δ , Γ ▹ A ])
            → ctxExtIsoA {Δ = Δ} A .fun τ
            ≡ ( p ∘ τ
              , subst (Tm Δ) (sym ([][]Ty A τ p))
                      (subst (Tm Δ) refl (q [ τ ]Tm)) )
    funPath {Δ = Δ} A τ =
      ΣPathP (refl , cong (subst⁻ (Tm Δ) ([][]Ty A τ p))
                          (sym (substRefl {B = Tm Δ} (q [ τ ]Tm))))

  open Categorical.CwF hiding (_[_]Ty ; _[_]Tm)

  ACwF→CCwF : Categorical.CwF C ℓTy ℓTm
  ACwF→CCwF .emptyContext = ⟨⟩
  ACwF→CCwF .Ty .F-ob Γ .fst = X .Ty Γ
  ACwF→CCwF .Ty .F-ob Γ .snd = isSetTy Γ
  ACwF→CCwF .Ty .F-hom σ A = A [ σ ]Ty
  ACwF→CCwF .Ty .F-id = funExt [id]Ty
  ACwF→CCwF .Ty .F-seq f g = funExt (λ A → [][]Ty A g f)
  ACwF→CCwF .Tm .F-ob (Γ , A) .fst = X .Tm Γ A
  ACwF→CCwF .Tm .F-ob (Γ , A) .snd = isSetTm Γ A
  ACwF→CCwF .Tm .F-hom {Γ , A} {Δ , B} (σ , prf) t = subst (X .Tm Δ) prf (t [ σ ]Tm)
  ACwF→CCwF .Tm .F-id = funExt (λ t → fromPathP ([id]Tm t))
  ACwF→CCwF .Tm .F-seq {Γ , A} {Δ , B} {Θ , E} (f , pf) (g , pg) = funExt λ t →
    let ph' : A [ f ∘ g ]Ty ≡ E
        ph' = [][]Ty A g f ∙ (cong (_[ g ]Ty) pf ∙ pg)
    in
    subst (X .Tm Θ) _ (t [ f ∘ g ]Tm)
      ≡⟨ cong (λ z → subst (X .Tm Θ) z (t [ f ∘ g ]Tm)) (isSetTy Θ _ _ _ ph') ⟩
    subst (X .Tm Θ) ph' (t [ f ∘ g ]Tm)
      ≡⟨ substComposite (X .Tm Θ) ([][]Ty A g f) (cong (_[ g ]Ty) pf ∙ pg) (t [ f ∘ g ]Tm) ⟩
    subst (X .Tm Θ) (cong (_[ g ]Ty) pf ∙ pg) (subst (X .Tm Θ) ([][]Ty A g f) (t [ f ∘ g ]Tm))
      ≡⟨ cong (subst (X .Tm Θ) (cong (_[ g ]Ty) pf ∙ pg)) (fromPathP ([][]Tm t g f)) ⟩
    subst (X .Tm Θ) (cong (_[ g ]Ty) pf ∙ pg) (t [ f ]Tm [ g ]Tm)
      ≡⟨ substComposite (X .Tm Θ) (cong (_[ g ]Ty) pf) pg (t [ f ]Tm [ g ]Tm) ⟩
    subst (X .Tm Θ) pg (subst (X .Tm Θ) (cong (_[ g ]Ty) pf) (t [ f ]Tm [ g ]Tm))
      ≡⟨ cong (subst (X .Tm Θ) pg)
              (substCommSlice (X .Tm Δ) (λ a → X .Tm Θ (a [ g ]Ty)) (λ a s → s [ g ]Tm) pf (t [ f ]Tm)) ⟩
    subst (X .Tm Θ) pg (subst (X .Tm Δ) pf (t [ f ]Tm) [ g ]Tm) ∎
  ACwF→CCwF ._▹_ = X ._▹_
  ACwF→CCwF .p = X .p
  ACwF→CCwF .q = X .q
  ACwF→CCwF .ctxExtRepr A =
    subst isEquiv (funExt (funPath A)) (isoToIsEquiv (ctxExtIsoA A))
