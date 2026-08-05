module CCwF.FromACwF where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
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
  open Categorical.CwF hiding (_[_]Ty ; _[_]Tm ; _⋆_)
  open Functor
  open Iso

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
  ACwF→CCwF .ctxExt .F-ob (Γ , A) = Γ ▹ A
  ACwF→CCwF .ctxExt .F-hom {Γ , A} {Δ , B} (f , pf) = subst (λ x → Hom[ Γ ▹ x , _ ]) pf (f ⁺)
  ACwF→CCwF .ctxExt .F-id {Γ , A} = fromPathP (id⁺ {A = A})
  ACwF→CCwF .ctxExt .F-seq {Γ , A} {Δ , B} {Θ , E} (f , pf) (g , pg) =
    cong (λ z → subst dom z ((g ∘ f) ⁺)) (isSetTy Γ _ _ _ (ph' pg pf)) ∙ lemma pg pf
    where
    dom : X .Ty Γ → Type _
    dom x = Hom[ Γ ▹ x , Θ ▹ E ]

    ph' : ∀ {B' : X .Ty Δ} (pg : E [ g ]Ty ≡ B') {A' : X .Ty Γ} (pf : B' [ f ]Ty ≡ A')
        → E [ g ∘ f ]Ty ≡ A'
    ph' pg pf = [][]Ty E f g ∙ (cong (_[ f ]Ty) pg ∙ pf)

    lemma : ∀ {B' : X .Ty Δ} (pg : E [ g ]Ty ≡ B') {A' : X .Ty Γ} (pf : B' [ f ]Ty ≡ A')
          → subst dom (ph' pg pf) ((g ∘ f) ⁺)
          ≡ subst (λ x → Hom[ Γ ▹ x , Δ ▹ B' ]) pf (f ⁺) ⋆ subst (λ x → Hom[ Δ ▹ x , Θ ▹ E ]) pg (g ⁺)
    lemma = J (λ B' pg → ∀ {A'} (pf : B' [ f ]Ty ≡ A')
                → subst dom (ph' pg pf) ((g ∘ f) ⁺)
                ≡ subst (λ x → Hom[ Γ ▹ x , Δ ▹ B' ]) pf (f ⁺) ⋆ subst (λ x → Hom[ Δ ▹ x , Θ ▹ E ]) pg (g ⁺))
              (J (λ A' pf → subst dom (ph' refl pf) ((g ∘ f) ⁺)
                         ≡ subst (λ x → Hom[ Γ ▹ x , Δ ▹ E [ g ]Ty ]) pf (f ⁺)
                         ⋆ subst (λ x → Hom[ Δ ▹ x , Θ ▹ E ]) refl (g ⁺))
                 base)
      where
      base : subst dom (ph' refl refl) ((g ∘ f) ⁺)
           ≡ subst (λ x → Hom[ Γ ▹ x , Δ ▹ E [ g ]Ty ]) refl (f ⁺)
           ⋆ subst (λ x → Hom[ Δ ▹ x , Θ ▹ E ]) refl (g ⁺)
      base =
        subst dom (ph' refl refl) ((g ∘ f) ⁺)
          ≡⟨ cong (λ z → subst dom z ((g ∘ f) ⁺)) (isSetTy Γ _ _ (ph' refl refl) ([][]Ty E f g)) ⟩
        subst dom ([][]Ty E f g) ((g ∘ f) ⁺)
          ≡⟨ fromPathP (∘⁺ {A = E} f g) ⟩
        g ⁺ ∘ f ⁺
          ≡⟨ sym (cong₂ _⋆_ (transportRefl (f ⁺)) (transportRefl (g ⁺))) ⟩
        subst (λ x → Hom[ Γ ▹ x , Δ ▹ E [ g ]Ty ]) refl (f ⁺)
          ⋆ subst (λ x → Hom[ Δ ▹ x , Θ ▹ E ]) refl (g ⁺) ∎
  ACwF→CCwF .ctxExtIso A .fun σ .fst = p ∘ σ
  ACwF→CCwF .ctxExtIso {Γ} {Δ} A .fun σ .snd = subst⁻ (X .Tm Δ) ([][]Ty A σ p) (q [ σ ]Tm)
  ACwF→CCwF .ctxExtIso A .inv (σ , t) = (σ ⁺) ∘ ⟨ t ⟩
  ACwF→CCwF .ctxExtIso {Γ} {Δ} A .sec (σ , t) = ΣPathP (secFst , secSnd)
    where
    τ : Hom[ Δ , Γ ▹ A ]
    τ = (σ ⁺) ∘ ⟨ t ⟩

    u : X .Tm Δ (A [ p ∘ τ ]Ty)
    u = subst⁻ (X .Tm Δ) ([][]Ty A τ p) (q [ τ ]Tm)

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

    Q1 : PathP (λ i → X .Tm Δ (S1 i)) (q [ τ ]Tm) (q [ σ ⁺ ]Tm [ ⟨ t ⟩ ]Tm)
    Q1 = [][]Tm q ⟨ t ⟩ (σ ⁺)

    Q2 : PathP (λ i → X .Tm Δ ([p][⁺]Ty A σ i [ ⟨ t ⟩ ]Ty))
               (q [ σ ⁺ ]Tm [ ⟨ t ⟩ ]Tm) (q [ ⟨ t ⟩ ]Tm)
    Q2 = congP (λ i z → z [ ⟨ t ⟩ ]Tm) (q[⁺]Tm σ)

    Q3 : PathP (λ i → X .Tm Δ ([p][⟨⟩]Ty (A [ σ ]Ty) t i)) (q [ ⟨ t ⟩ ]Tm) t
    Q3 = q[⟨⟩]Tm t

    Q : PathP (λ i → X .Tm Δ (R i)) (q [ τ ]Tm) t
    Q = compPathP' {B = X .Tm Δ} Q1 (compPathP' {B = X .Tm Δ} Q2 Q3)

    secSnd : PathP (λ i → X .Tm Δ (A [ secFst i ]Ty)) u t
    secSnd = toPathP (
      subst (X .Tm Δ) (cong (A [_]Ty) secFst) u
        ≡⟨ sym (substComposite (X .Tm Δ) (sym ([][]Ty A τ p)) (cong (A [_]Ty) secFst) (q [ τ ]Tm)) ⟩
      subst (X .Tm Δ) (sym ([][]Ty A τ p) ∙ cong (A [_]Ty) secFst) (q [ τ ]Tm)
        ≡⟨ cong (λ z → subst (X .Tm Δ) z (q [ τ ]Tm))
                (isSetTy Δ _ _ (sym ([][]Ty A τ p) ∙ cong (A [_]Ty) secFst) R) ⟩
      subst (X .Tm Δ) R (q [ τ ]Tm)
        ≡⟨ fromPathP Q ⟩
      t ∎)
  ACwF→CCwF .ctxExtIso {Γ} {Δ} A .ret τ =
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
    w : X .Tm Δ (A [ p ∘ τ ]Ty)
    w = subst⁻ (X .Tm Δ) ([][]Ty A τ p) (q [ τ ]Tm)

    wPath : PathP (λ i → X .Tm Δ ([][]Ty A τ p i)) w (q [ τ ]Tm)
    wPath = symP (subst-filler (X .Tm Δ) (sym ([][]Ty A τ p)) (q [ τ ]Tm))

    firstStep : ((p ∘ τ) ⁺) ∘ ⟨ w ⟩ ≡ (p ⁺ ∘ τ ⁺) ∘ ⟨ q [ τ ]Tm ⟩
    firstStep i = (∘⁺ {A = A} τ p i) ∘ ⟨ wPath i ⟩
  ACwF→CCwF .coerceFun A σ τ = sym ([][]Ty A τ (p ∘ σ))
  ACwF→CCwF .coerceInv A σ τ = sym ([][]Ty A τ σ)

  ACwF→CCwF .ctxExtIsoFunNat {Γ} {Δ} {Θ} A σ τ = ΣPathP (fstP , sndP)
    where
    fstP : p ∘ (σ ∘ τ) ≡ (p ∘ σ) ∘ τ
    fstP = ⋆Assoc τ σ p

    PL PR : A [ p ]Ty [ σ ∘ τ ]Ty ≡ A [ (p ∘ σ) ∘ τ ]Ty
    PL = sym ([][]Ty A (σ ∘ τ) p) ∙ cong (A [_]Ty) fstP
    PR = [][]Ty (A [ p ]Ty) τ σ ∙ (cong (_[ τ ]Ty) (sym ([][]Ty A σ p)) ∙ sym ([][]Ty A τ (p ∘ σ)))

    sndP : PathP (λ i → X .Tm Θ (A [ fstP i ]Ty))
                 (subst⁻ (X .Tm Θ) ([][]Ty A (σ ∘ τ) p) (q [ σ ∘ τ ]Tm))
                 (subst (X .Tm Θ) (sym ([][]Ty A τ (p ∘ σ)))
                        (subst⁻ (X .Tm Δ) ([][]Ty A σ p) (q [ σ ]Tm) [ τ ]Tm))
    sndP = toPathP (
      subst (X .Tm Θ) (cong (A [_]Ty) fstP) (subst⁻ (X .Tm Θ) ([][]Ty A (σ ∘ τ) p) (q [ σ ∘ τ ]Tm))
        ≡⟨ sym (substComposite (X .Tm Θ) (sym ([][]Ty A (σ ∘ τ) p)) (cong (A [_]Ty) fstP) (q [ σ ∘ τ ]Tm)) ⟩
      subst (X .Tm Θ) PL (q [ σ ∘ τ ]Tm)
        ≡⟨ cong (λ z → subst (X .Tm Θ) z (q [ σ ∘ τ ]Tm)) (isSetTy Θ _ _ PL PR) ⟩
      subst (X .Tm Θ) PR (q [ σ ∘ τ ]Tm)
        ≡⟨ substComposite (X .Tm Θ) ([][]Ty (A [ p ]Ty) τ σ)
                          (cong (_[ τ ]Ty) (sym ([][]Ty A σ p)) ∙ sym ([][]Ty A τ (p ∘ σ))) (q [ σ ∘ τ ]Tm) ⟩
      subst (X .Tm Θ) (cong (_[ τ ]Ty) (sym ([][]Ty A σ p)) ∙ sym ([][]Ty A τ (p ∘ σ)))
            (subst (X .Tm Θ) ([][]Ty (A [ p ]Ty) τ σ) (q [ σ ∘ τ ]Tm))
        ≡⟨ cong (subst (X .Tm Θ) (cong (_[ τ ]Ty) (sym ([][]Ty A σ p)) ∙ sym ([][]Ty A τ (p ∘ σ))))
                (fromPathP ([][]Tm q τ σ)) ⟩
      subst (X .Tm Θ) (cong (_[ τ ]Ty) (sym ([][]Ty A σ p)) ∙ sym ([][]Ty A τ (p ∘ σ))) (q [ σ ]Tm [ τ ]Tm)
        ≡⟨ substComposite (X .Tm Θ) (cong (_[ τ ]Ty) (sym ([][]Ty A σ p))) (sym ([][]Ty A τ (p ∘ σ))) (q [ σ ]Tm [ τ ]Tm) ⟩
      subst (X .Tm Θ) (sym ([][]Ty A τ (p ∘ σ)))
            (subst (X .Tm Θ) (cong (_[ τ ]Ty) (sym ([][]Ty A σ p))) (q [ σ ]Tm [ τ ]Tm))
        ≡⟨ cong (subst (X .Tm Θ) (sym ([][]Ty A τ (p ∘ σ))))
                (substCommSlice (X .Tm Δ) (λ b → X .Tm Θ (b [ τ ]Ty)) (λ b s → s [ τ ]Tm)
                                (sym ([][]Ty A σ p)) (q [ σ ]Tm)) ⟩
      subst (X .Tm Θ) (sym ([][]Ty A τ (p ∘ σ))) (subst⁻ (X .Tm Δ) ([][]Ty A σ p) (q [ σ ]Tm) [ τ ]Tm) ∎)

  ACwF→CCwF .ctxExtIsoFunNatWithoutCoerceFun A σ τ = ACwF→CCwF .ctxExtIsoFunNat A σ τ

  ACwF→CCwF .ctxExtIsoInvNat {Γ} {Δ} {Θ} A σ a τ =
    ((σ ⁺) ∘ ⟨ a ⟩) ∘ τ
      ≡⟨ sym (⋆Assoc _ _ _) ⟩
    (σ ⁺) ∘ (⟨ a ⟩ ∘ τ)
      ≡⟨ cong ((σ ⁺) ∘_) (⟨⟩∘ a τ) ⟩
    (σ ⁺) ∘ (τ ⁺ ∘ ⟨ a [ τ ]Tm ⟩)
      ≡⟨ ⋆Assoc _ _ _ ⟩
    ((σ ⁺) ∘ τ ⁺) ∘ ⟨ a [ τ ]Tm ⟩
      ≡⟨ sym bridge ⟩
    ((σ ∘ τ) ⁺) ∘ ⟨ a' ⟩ ∎
    where
    a' : X .Tm Θ (A [ σ ∘ τ ]Ty)
    a' = subst (X .Tm Θ) (sym ([][]Ty A τ σ)) (a [ τ ]Tm)

    aPath : PathP (λ i → X .Tm Θ ([][]Ty A τ σ i)) a' (a [ τ ]Tm)
    aPath = symP (subst-filler (X .Tm Θ) (sym ([][]Ty A τ σ)) (a [ τ ]Tm))

    bridge : ((σ ∘ τ) ⁺) ∘ ⟨ a' ⟩ ≡ ((σ ⁺) ∘ τ ⁺) ∘ ⟨ a [ τ ]Tm ⟩
    bridge i = (∘⁺ {A = A} τ σ i) ∘ ⟨ aPath i ⟩

  ACwF→CCwF .ctxExtIsoInvNatWithoutCoerceInv A σ a τ = ACwF→CCwF .ctxExtIsoInvNat A σ a τ
