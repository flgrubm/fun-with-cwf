{-# OPTIONS --lossy-unification #-}
module ACwF.Instances.TarskiPresheaf where

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

module _ {ℓob ℓhom ℓU ℓEl : Level} (C : Category ℓob ℓhom) (Univ : TarskiUniverse ℓU ℓEl) where
  open TarskiUniverse Univ
  open Algebraic (PRESHEAFU C Univ)
  private abstract
    -- The empty context
    PSH-TerminalObject : PresheafU C Univ
    PSH-TerminalObject .F-ob x = Unit
    PSH-TerminalObject .F-hom _ x = x
    PSH-TerminalObject .F-id = refl
    PSH-TerminalObject .F-seq _ _ = refl

    PSH-Terminal : Terminal (PRESHEAFU C Univ)
    PSH-Terminal .fst = PSH-TerminalObject
    PSH-Terminal .snd _ .fst .NatTrans.N-ob _ _ = isContrElUnit .fst
    PSH-Terminal .snd _ .fst .NatTrans.N-hom _ = refl
    PSH-Terminal .snd _ .snd η = makeNatTransPath (funExt λ I → funExt λ x → isContrElUnit .snd (N-ob η I x))

  -- the unit type
  Psh-UnitType : {Γ : PresheafU C Univ} → Functor (∫U Γ) (UCat Univ)
  Psh-UnitType = Constant _ _ Unit

  -- elements of A (terms) can be seen as natural transformations from the unit type to A
  private module _ (Γ : PresheafU C Univ) (A : Functor (∫U Γ) (UCat Univ)) where
    Psh-Tm : Type (ℓ-max (ℓ-max ℓob ℓhom) ℓEl)
    Psh-Tm = FUNCTOR (∫U Γ) (UCat Univ) [ Psh-UnitType , A ]
    Psh-Tm-isSet : isSet (Psh-Tm)
    Psh-Tm-isSet = isSetNatTrans

  private
    []Tm : ∀ Γ Δ
      → (A : Functor (∫U Γ) (UCat Univ))
      → (σ : NatTrans Δ Γ)
      → Psh-Tm Γ A
      → Psh-Tm Δ (A ∘F ∫U-hom σ)
    []Tm Γ Δ A σ M .N-ob x = M .N-ob (∫U-hom σ .F-ob x)
    []Tm Γ Δ A σ M .N-hom f = (M .N-hom) _

  Psh-CwF : CwF (ℓ-max (ℓ-max ℓob ℓhom) (ℓ-max ℓU ℓEl)) (ℓ-max (ℓ-max ℓob ℓhom) ℓEl)
  open CwF Psh-CwF
  Psh-CwF .CwF.⟨⟩ = PSH-Terminal

  Psh-CwF .CwF.Ty Γ = Functor (∫U Γ) (UCat Univ)
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

  Psh-CwF .CwF._▹_ Γ A .F-ob I = Sig (Γ .F-ob I) (λ x → A .F-ob (I , x))
  Psh-CwF .CwF._▹_ Γ A .F-hom {I} {J} f x = pairSig (Γ .F-hom f (fstSig x)) (A .F-hom (f , refl) (sndSig x))
  Psh-CwF .CwF._▹_ Γ A .F-id {I} = funExt λ x → SigPathP
    (fstPairSig _ _ ∙ funExt⁻ (Γ .F-id) (fstSig x))
    (compPathP' {B = λ z → El (A .F-ob (I , z))}
      (sndPairSig _ _)
      (goal x ▷ funExt⁻ (A .F-id) (sndSig x)))
    where
      goal : ∀ x →
        PathP (λ i → El (A .F-ob (I , (Γ .F-id i (fstSig x)))))
          (A .F-hom (id C , refl) (sndSig x))
          (A .F-hom (∫U Γ .id) (sndSig x))
      goal x =
        funExt⁻ (F-hom-PathP A (id C , refl) (id C , _) refl (λ i → I , Γ .F-id i (fstSig x)) refl) (sndSig x)
  Psh-CwF .CwF._▹_ Γ A .F-seq {I} {J} {K} f g = funExt λ x → SigPathP
    (fstPairSig _ _ ∙ (funExt⁻ (Γ .F-seq _ _ ) (fstSig x) ∙ cong (Γ .F-hom g) (sym (fstPairSig _ _))) ∙ sym (fstPairSig _ _))
    (compPathP' {B = λ z → El (A .F-ob (K , z))}
      (sndPairSig _ _)
      (compPathP' {B = λ z → El (A .F-ob (K , z))}
        (compPathP' {B = λ z → El (A .F-ob (K , z))}
          (goal x)
          (congP (λ i z → A .F-hom (g , refl) z) (symP (sndPairSig _ _))))
        (symP (sndPairSig _ _))))
    where
      goal' : ∀ x →
        PathP (λ i → El (A .F-ob (K , funExt⁻ (Γ .F-seq f g) (fstSig x) i)))
          (A .F-hom (g ⋆⟨ C ⟩ f , refl) (sndSig x))
          (A .F-hom ((f , refl) ⋆⟨ ∫U Γ ⟩ (g , refl)) (sndSig x))
      goal' x =
        funExt⁻ (F-hom-PathP A (seq' C g f , refl)
                  (seq' (∫U Γ) (f , refl) (g , refl)) refl (λ i → K , Γ .F-seq f g i (fstSig x)) refl) (sndSig x)
      goal : ∀ x →
        PathP (λ i → El (A .F-ob (K , funExt⁻ (Γ .F-seq f g) (fstSig x) i)))
          (A .F-hom (g ⋆⟨ C ⟩ f , refl) (sndSig x))
          (A .F-hom (g , refl) (A .F-hom (f , refl) (sndSig x)))
      goal x = goal' x ▷ funExt⁻ (A .F-seq (f , refl) (g , refl)) (sndSig x)

  Psh-CwF .CwF.p .N-ob I x = fstSig x
  Psh-CwF .CwF.p .N-hom f = funExt (λ _ → fstPairSig _ _)

  Psh-CwF .CwF.q .N-ob x _ = sndSig (x .snd)
  Psh-CwF .CwF.q {Γ} {A} .N-hom {x} {y} (f , p) = funExt λ _ →
    sym (fromPathP bigPathP)
    ∙ fromPathP (funExt⁻ (F-hom-PathP A (f , refl)
                  (∫U-hom (Psh-CwF .CwF.p {Γ} {A}) .F-hom (f , p))
                  refl (λ i → y .fst , qbase i) refl) (sndSig (x .snd)))
    where
      qbase : Γ .F-hom f (fstSig (x .snd)) ≡ fstSig (y .snd)
      qbase = sym (fstPairSig _ _) ∙ cong fstSig p
      bigPathP : PathP (λ i → El (A .F-ob (y .fst , qbase i)))
                       (A .F-hom (f , refl) (sndSig (x .snd))) (sndSig (y .snd))
      bigPathP = compPathP' {B = λ z → El (A .F-ob (y .fst , z))}
                   (symP (sndPairSig _ _)) (cong sndSig p)
  Psh-CwF .CwF._⁺ σ .N-ob I x = pairSig (σ .N-ob I (fstSig x)) (sndSig x)
  Psh-CwF .CwF._⁺ {Γ} {Δ} {A} σ .N-hom {I} {J} f = funExt λ x → SigPathP
    (fstPairSig _ _ ∙ ((cong (σ .N-ob J) (fstPairSig _ _) ∙ funExt⁻ (σ .N-hom f) (fstSig x)) ∙ cong (Γ .F-hom f) (sym (fstPairSig _ _))) ∙ sym (fstPairSig _ _))
    (compPathP' {B = λ z → El (A .F-ob (J , z))}
      (sndPairSig _ _)
      (compPathP' {B = λ z → El (A .F-ob (J , z))}
        (compPathP' {B = λ z → El (A .F-ob (J , z))}
          (compPathP' {B = λ z → El (A .F-ob (J , z))}
            (sndPairSig _ _)
            (snd≡ x))
          (congP (λ i z → A .F-hom (f , refl) z) (symP (sndPairSig _ _))))
        (symP (sndPairSig _ _))))
    where
      snd≡ : ∀ x → PathP
                    (λ i → El (A .F-ob (J , funExt⁻ (σ .N-hom f) (fstSig x) i)))
                    (A .F-hom (f , _) (sndSig x))
                    (A .F-hom (f , refl) (sndSig x))
      snd≡ x = funExt⁻ (F-hom-PathP A (f , _) (f , refl) refl (λ i → J , funExt⁻ (σ .N-hom f) (fstSig x) i) refl) (sndSig x)

  Psh-CwF .CwF.⟨_⟩ M .N-ob I x = pairSig x (M .N-ob (I , x) (isContrElUnit .fst))
  Psh-CwF .CwF.⟨_⟩ {Γ} {A} M .N-hom {I} {J} f = funExt λ x → cong₂ pairSig
    (cong (Γ .F-hom f) (sym (fstPairSig _ _)))
    ((funExt⁻ (M .N-hom (f , refl)) (isContrElUnit .fst)) ◁ congP (λ i z → A .F-hom (f , refl) z) (symP (sndPairSig _ _)))
  Psh-CwF .CwF.⟨⟩∘ M σ = makeNatTransPath (funExt λ I → funExt λ x →
    cong₂ pairSig (cong (σ .N-ob I) (sym (fstPairSig _ _))) (symP (sndPairSig _ _)))
  Psh-CwF .CwF.p⁺∘⟨q⟩≡id = makeNatTransPath (funExt λ I → funExt λ x →
    cong₂ pairSig (cong fstSig (fstPairSig _ _)) (sndPairSig _ _) ∙ ηSig _)
  Psh-CwF .CwF.∘⁺ {Γ} {Δ} {Θ} {A} σ' σ =
    makeNatTransPathP (cong (Δ ▹_) ([][]Ty A σ' σ)) refl
      (funExt λ I → funExt λ w → cong₂ pairSig (cong (σ .N-ob I) (sym (fstPairSig _ _))) (symP (sndPairSig _ _)))
  Psh-CwF .CwF.id⁺ {Γ} {A} =
    makeNatTransPathP (cong (Γ ▹_) ([id]Ty A)) refl (funExt λ I → funExt λ w → ηSig _)
  Psh-CwF .CwF.p∘⁺ σ = makeNatTransPath (funExt λ I → funExt λ w → fstPairSig _ _)
  Psh-CwF .CwF.[p][⁺]Ty {Γ} {Δ} B σ =
    Functor≡ (λ c → cong (B .F-ob) (ΣPathP (refl , fstPairSig _ _)))
             (λ f → F-hom-PathP B _ _ (ΣPathP (refl , fstPairSig _ _)) (ΣPathP (refl , fstPairSig _ _)) refl)
  Psh-CwF .CwF.q[⁺]Tm {A = A} σ = makeNatTransPathP refl ([p][⁺]Ty _ σ)
    (λ i x u → sndPairSig {B = λ v → A .F-ob (x .fst , v)} (σ .N-ob (x .fst) (fstSig (x .snd))) (sndSig (x .snd)) i)
  Psh-CwF .CwF.p∘⟨⟩≡id M = makeNatTransPath (funExt λ I → funExt λ z → fstPairSig _ _)
  Psh-CwF .CwF.[p][⟨⟩]Ty B a =
    Functor≡ (λ c → cong (B .F-ob) (ΣPathP (refl , fstPairSig _ _)))
             (λ f → F-hom-PathP B _ _ (ΣPathP (refl , fstPairSig _ _)) (ΣPathP (refl , fstPairSig _ _)) refl)
  Psh-CwF .CwF.q[⟨⟩]Tm {A = A} M = makeNatTransPathP refl ([p][⟨⟩]Ty A M)
    (λ i x u → (sndPairSig {B = λ v → A .F-ob (x .fst , v)} (x .snd) (M .N-ob x (isContrElUnit .fst))
                  ▷ cong (M .N-ob x) (isContrElUnit .snd u)) i)
