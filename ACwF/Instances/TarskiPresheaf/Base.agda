module ACwF.Instances.TarskiPresheaf.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Functors.Constant
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Limits.Terminal
open import TarskiUniverse.Base
open import TarskiUniverse.Properties
open import Utils.TarskiPresheaf
open import ACwF.Base

open Category
open Functor
open NatTrans

module _ {ℓob ℓhom ℓU ℓEl : Level} (C : Category ℓob ℓhom) {U : Type ℓU} (Univ : TarskiUniverse ℓEl U) where
  open TarskiUniverse Univ
  open Algebraic (PRESHEAFU C TU)
  private abstract
    -- The empty context
    PSH-TerminalObject : PresheafU C TU
    PSH-TerminalObject .F-ob x = Unit
    PSH-TerminalObject .F-hom _ x = x
    PSH-TerminalObject .F-id = refl
    PSH-TerminalObject .F-seq _ _ = refl

    PSH-Terminal : Terminal (PRESHEAFU C TU)
    PSH-Terminal .fst = PSH-TerminalObject
    PSH-Terminal .snd _ .fst .NatTrans.N-ob _ _ = isContrElUnit .fst
    PSH-Terminal .snd _ .fst .NatTrans.N-hom _ = refl
    PSH-Terminal .snd _ .snd η = makeNatTransPath (funExt λ I → funExt λ x → isContrElUnit .snd (N-ob η I x))

  -- the unit type
  Psh-UnitType : {Γ : PresheafU C TU} → Functor (∫U Γ) (UCat TU)
  Psh-UnitType = Constant _ _ Unit

  -- elements of A (terms) can be seen as natural transformations from the unit type to A
  private module _ (Γ : PresheafU C TU) (A : Functor (∫U Γ) (UCat TU)) where
    Psh-Tm : Type (ℓ-max (ℓ-max ℓob ℓhom) ℓEl)
    Psh-Tm = FUNCTOR (∫U Γ) (UCat TU) [ Psh-UnitType , A ]
    Psh-Tm-isSet : isSet (Psh-Tm)
    Psh-Tm-isSet = isSetNatTrans

  private
    []Tm : ∀ Γ Δ
      → (A : Functor (∫U Γ) (UCat TU))
      → (σ : NatTrans Δ Γ)
      → Psh-Tm Γ A
      → Psh-Tm Δ (A ∘F ∫U-hom σ)
    []Tm Γ Δ A σ M .N-ob x = M .N-ob (∫U-hom σ .F-ob x)
    []Tm Γ Δ A σ M .N-hom f = (M .N-hom) _

  Psh-CwF : CwF (ℓ-max (ℓ-max ℓob ℓhom) (ℓ-max ℓU ℓEl)) (ℓ-max (ℓ-max ℓob ℓhom) ℓEl)
  open CwF Psh-CwF
  Psh-CwF .CwF.⟨⟩ = PSH-Terminal

  Psh-CwF .CwF.Ty Γ = Functor (∫U Γ) (UCat TU)
  Psh-CwF .CwF.isSetTy Γ = isSetFunctor isSetU
  Psh-CwF .CwF._[_]Ty A σ = A ∘F ∫U-hom σ
  Psh-CwF .CwF.[id]Ty {Γ} A =
    Functor≡
      (λ c → refl)
      (λ f → cong (A .F-hom) (ΣPathP (refl , isSetEl (Γ .F-ob _) _ _ _ _)))
  Psh-CwF .CwF.[][]Ty {Γ = Γ} A σ' σ =
    Functor≡ (λ c → refl) λ f → cong (A .F-hom) (ΣPathP (refl , isSetEl (Γ .F-ob _) _ _ _ _))

  Psh-CwF .CwF.Tm Γ A = Psh-Tm Γ A
  Psh-CwF .CwF.isSetTm = Psh-Tm-isSet
  Psh-CwF .CwF._[_]Tm M σ = []Tm _ _ _ σ M
  Psh-CwF .CwF.[id]Tm M = makeNatTransPathP refl ([id]Ty _) refl
  Psh-CwF .CwF.[][]Tm M σ' σ = makeNatTransPathP refl ([][]Ty _ _ _) refl

  Psh-CwF .CwF._▹_ Γ A .F-ob I = Sigma (Γ .F-ob I) (λ x → A .F-ob (I , x))
  Psh-CwF .CwF._▹_ Γ A .F-hom {I} {J} f x = pairSigma (Γ .F-hom f (fstSigma x)) (A .F-hom (f , refl) (sndSigma x))
  Psh-CwF .CwF._▹_ Γ A .F-id {I} = funExt λ x →
    cong₂ pairSigma
      (funExt⁻ (Γ .F-id) (fstSigma x))
      (goal x ▷ funExt⁻ (A .F-id) (sndSigma x))
    ∙ ηSigma x
    where
      Elᴬ : El (Γ .F-ob I) → Type ℓEl
      Elᴬ z = El (A .F-ob (I , z))
      goal : ∀ x →
        PathP (λ i → Elᴬ (Γ .F-id i (fstSigma x)))
          (A .F-hom (id C , refl) (sndSigma x))
          (A .F-hom (∫U Γ .id) (sndSigma x))
      goal x =
        funExt⁻ (F-hom-PathP A (id C , refl) (id C , _) refl (λ i → I , Γ .F-id i (fstSigma x)) refl) (sndSigma x)
  Psh-CwF .CwF._▹_ Γ A .F-seq {I} {J} {K} f g = funExt λ x → cong₂ pairSigma
    (funExt⁻ (Γ .F-seq f g) (fstSigma x) ∙ cong (Γ .F-hom g) (sym (fstPairSigma _ _)))
    (compPathP' {B = Elᴬ}
      (goal x)
      (congP (λ i z → A .F-hom (g , refl) z) (symP (sndPairSigma _ _))))
    where
      Elᴬ : El (Γ .F-ob K) → Type ℓEl
      Elᴬ z = El (A .F-ob (K , z))
      goal' : ∀ x →
        PathP (λ i → Elᴬ (funExt⁻ (Γ .F-seq f g) (fstSigma x) i))
          (A .F-hom (g ⋆⟨ C ⟩ f , refl) (sndSigma x))
          (A .F-hom ((f , refl) ⋆⟨ ∫U Γ ⟩ (g , refl)) (sndSigma x))
      goal' x =
        funExt⁻ (F-hom-PathP A (seq' C g f , refl)
                  (seq' (∫U Γ) (f , refl) (g , refl)) refl (λ i → K , Γ .F-seq f g i (fstSigma x)) refl) (sndSigma x)
      goal : ∀ x →
        PathP (λ i → Elᴬ (funExt⁻ (Γ .F-seq f g) (fstSigma x) i))
          (A .F-hom (g ⋆⟨ C ⟩ f , refl) (sndSigma x))
          (A .F-hom (g , refl) (A .F-hom (f , refl) (sndSigma x)))
      goal x = goal' x ▷ funExt⁻ (A .F-seq (f , refl) (g , refl)) (sndSigma x)

  Psh-CwF .CwF.p .N-ob I x = fstSigma x
  Psh-CwF .CwF.p .N-hom f = funExt (λ _ → fstPairSigma _ _)

  Psh-CwF .CwF.q .N-ob x _ = sndSigma (x .snd)
  Psh-CwF .CwF.q {Γ} {A} .N-hom {x} {y} (f , p) = funExt λ _ →
    sym (fromPathP bigPathP)
    ∙ fromPathP (funExt⁻ (F-hom-PathP A (f , refl)
                  (∫U-hom (Psh-CwF .CwF.p {Γ} {A}) .F-hom (f , p))
                  refl (λ i → y .fst , qbase i) refl) (sndSigma (x .snd)))
    where
      Elᴬ : El (Γ .F-ob (y .fst)) → Type ℓEl
      Elᴬ z = El (A .F-ob (y .fst , z))
      qbase : Γ .F-hom f (fstSigma (x .snd)) ≡ fstSigma (y .snd)
      qbase = sym (fstPairSigma _ _) ∙ cong fstSigma p
      bigPathP : PathP (λ i → Elᴬ (qbase i))
                       (A .F-hom (f , refl) (sndSigma (x .snd))) (sndSigma (y .snd))
      bigPathP = compPathP' {B = Elᴬ}
                   (symP (sndPairSigma _ _)) (cong sndSigma p)

  Psh-CwF .CwF._⁺ σ .N-ob I x = pairSigma (σ .N-ob I (fstSigma x)) (sndSigma x)
  Psh-CwF .CwF._⁺ {Γ} {Δ} {A} σ .N-hom {I} {J} f = funExt λ x → cong₂ pairSigma
    (cong (σ .N-ob J) (fstPairSigma _ _) ∙ funExt⁻ (σ .N-hom f) (fstSigma x) ∙ cong (Γ .F-hom f) (sym (fstPairSigma _ _)))
    (compPathP' {B = Elᴬ}
      (sndPairSigma _ _)
      (compPathP' {B = Elᴬ}
        (snd≡ x)
        (congP (λ i z → A .F-hom (f , refl) z) (symP (sndPairSigma _ _)))))
    where
      Elᴬ : El (Γ .F-ob J) → Type ℓEl
      Elᴬ z = El (A .F-ob (J , z))
      snd≡ : ∀ x → PathP
                    (λ i → Elᴬ (funExt⁻ (σ .N-hom f) (fstSigma x) i))
                    (A .F-hom (f , _) (sndSigma x))
                    (A .F-hom (f , refl) (sndSigma x))
      snd≡ x = funExt⁻ (F-hom-PathP A (f , _) (f , refl) refl (λ i → J , funExt⁻ (σ .N-hom f) (fstSigma x) i) refl) (sndSigma x)

  Psh-CwF .CwF.⟨_⟩ M .N-ob I x = pairSigma x (M .N-ob (I , x) (isContrElUnit .fst))
  Psh-CwF .CwF.⟨_⟩ {Γ} {A} M .N-hom {I} {J} f = funExt λ x → cong₂ pairSigma
    (cong (Γ .F-hom f) (sym (fstPairSigma _ _)))
    ((funExt⁻ (M .N-hom (f , refl)) (isContrElUnit .fst)) ◁ congP (λ i z → A .F-hom (f , refl) z) (symP (sndPairSigma _ _)))

  Psh-CwF .CwF.⟨⟩∘ M σ = makeNatTransPath (funExt λ I → funExt λ x →
    cong₂ pairSigma (cong (σ .N-ob I) (sym (fstPairSigma _ _))) (symP (sndPairSigma _ _)))
  Psh-CwF .CwF.p⁺∘⟨q⟩≡id = makeNatTransPath (funExt λ I → funExt λ x →
    cong₂ pairSigma (cong fstSigma (fstPairSigma _ _)) (sndPairSigma _ _) ∙ ηSigma _)
  Psh-CwF .CwF.∘⁺ {Γ} {Δ} {Θ} {A} σ' σ =
    makeNatTransPathP (cong (Δ ▹_) ([][]Ty A σ' σ)) refl
      (funExt λ I → funExt λ w → cong₂ pairSigma (cong (σ .N-ob I) (sym (fstPairSigma _ _))) (symP (sndPairSigma _ _)))
  Psh-CwF .CwF.id⁺ {Γ} {A} =
    makeNatTransPathP (cong (Γ ▹_) ([id]Ty A)) refl (funExt λ I → funExt λ w → ηSigma _)
  Psh-CwF .CwF.p∘⁺ σ = makeNatTransPath (funExt λ I → funExt λ w → fstPairSigma _ _)
  Psh-CwF .CwF.[p][⁺]Ty {Γ} {Δ} B σ =
    Functor≡ (λ c → cong (B .F-ob) (ΣPathP (refl , fstPairSigma _ _)))
             (λ f → F-hom-PathP B _ _ (ΣPathP (refl , fstPairSigma _ _)) (ΣPathP (refl , fstPairSigma _ _)) refl)
  Psh-CwF .CwF.q[⁺]Tm {A = A} σ = makeNatTransPathP refl ([p][⁺]Ty _ σ)
    (λ i x u → sndPairSigma {B = λ v → A .F-ob (x .fst , v)} (σ .N-ob (x .fst) (fstSigma (x .snd))) (sndSigma (x .snd)) i)
  Psh-CwF .CwF.p∘⟨⟩≡id M = makeNatTransPath (funExt λ I → funExt λ z → fstPairSigma _ _)
  Psh-CwF .CwF.[p][⟨⟩]Ty B a =
    Functor≡ (λ c → cong (B .F-ob) (ΣPathP (refl , fstPairSigma _ _)))
             (λ f → F-hom-PathP B _ _ (ΣPathP (refl , fstPairSigma _ _)) (ΣPathP (refl , fstPairSigma _ _)) refl)
  Psh-CwF .CwF.q[⟨⟩]Tm {A = A} M = makeNatTransPathP refl ([p][⟨⟩]Ty A M)
    (λ i x u → (sndPairSigma {B = λ v → A .F-ob (x .fst , v)} (x .snd) (M .N-ob x (isContrElUnit .fst))
                  ▷ cong (M .N-ob x) (isContrElUnit .snd u)) i)
