{-# OPTIONS --lossy-unification #-}
module ACwF.Instances.IterativePresheaf where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Unit
open import Cubical.Data.Sigma
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Limits.Terminal
open import Cubical.Data.IterativeSets.Base renaming (V⁰ to V ; El⁰ to El)
open import Cubical.Data.IterativeSets.Unit
open import Cubical.Data.IterativeSets.Sigma
open import Utils.IterativePresheaf
open import Utils.VCat
open import ACwF.Base

open Category
open Functor
open NatTrans

module _ {ℓob ℓhom ℓV : Level} (C : Category ℓob ℓhom) where
  open Algebraic (PRESHEAFV C ℓV)
  private
    PSH-TerminalObject : PresheafV C ℓV
    PSH-TerminalObject .F-ob x = unit⁰
    PSH-TerminalObject .F-hom _ x = x
    PSH-TerminalObject .F-id = refl
    PSH-TerminalObject .F-seq _ _ = refl

    PSH-Terminal : Terminal (PRESHEAFV C ℓV)
    PSH-Terminal .fst = PSH-TerminalObject
    PSH-Terminal .snd _ .fst .NatTrans.N-ob _ _ = isContrUnit* .fst
    PSH-Terminal .snd _ .fst .NatTrans.N-hom _ = refl
    PSH-Terminal .snd _ .snd η = makeNatTransPath (funExt (λ I → funExt λ x → isContrUnit* .snd (η .NatTrans.N-ob I x)))

  module _ (Γ : PresheafV C ℓV) (A : Functor (∫V Γ) (VCat ℓV)) where
    preTm : Type (ℓ-max ℓob ℓV)
    preTm = (I : C .Category.ob) (x : El (Γ ⟅ I ⟆)) → El (A ⟅ I , x ⟆)
    isTm : preTm → Type (ℓ-max (ℓ-max ℓob ℓhom) ℓV)
    isTm M = {I J : C .Category.ob} {x : El (Γ ⟅ I ⟆)} {y : El (Γ ⟅ J ⟆)}
        → (u : (∫V Γ) [ (J , y) , (I , x) ])
        → A .F-hom u (M J y) ≡ M I x
    -Tm : Type (ℓ-max (ℓ-max ℓob ℓhom) ℓV)
    -Tm = Σ preTm isTm
    isProp-isTm : (M : preTm) → isProp (isTm M)
    isProp-isTm M p1 p2 i {I} {J} {x} {y} u = isSetEl⁰ (A .F-ob (I , x)) _ _ (p1 u) (p2 u) i
    -isSetTm : isSet -Tm
    -isSetTm = isSetΣSndProp (isSetΠ λ I → isSetΠ λ x → isSetEl⁰ (A .F-ob (I , x))) isProp-isTm

  -- lemma : ∀  {Γ : PresheafV C ℓV} {A : Functor (∫V Γ) (VCat ℓV)} {I} {J} (f : C [ J , I ]) (x x' : El (Γ .F-ob I)) y p
  --   → x ≡ x'
  --   →
  --     (x , A .F-hom {x = I , x} {y = J , F-hom Γ f _} (f , p) y)
  --   ≡
  --     (x' , A .F-hom (f , refl) y)
  -- lemma {Γ} {A} {I} {J} f x x' y p fst≡ = ΣPathP (fst≡ , (cong (λ F → A .F-hom F y) (∫V-Hom≡ Γ (f , p) (f , refl) refl)))

  Psh-CwF : CwF (ℓ-max (ℓ-max ℓob ℓhom) (ℓ-suc ℓV)) (ℓ-max (ℓ-max ℓob ℓhom) ℓV)
  open CwF Psh-CwF
  Psh-CwF .CwF.⟨⟩ = PSH-Terminal
  Psh-CwF .CwF.Ty Γ = Functor (∫V Γ) (VCat ℓV)
  Psh-CwF .CwF.isSetTy Γ = isSetFunctor isSetV⁰
  Psh-CwF .CwF._[_]Ty A σ = A ∘F ∫V-hom σ
  Psh-CwF .CwF.[id]Ty {Γ} A =
    -- I changed to this less nice proof because it makes more things definitional
    Functor≡
      (λ c → refl)
      (λ f → cong (A .F-hom) (ΣPathP (refl , isSetEl⁰ (Γ .F-ob _) _ _ _ _)))
    -- A ∘F ∫V-hom (id (PRESHEAFV C ℓV)) ≡⟨ cong (λ F → A ∘F F) ∫V-id ⟩
    -- A ∘F Id                           ≡⟨ F-lUnit ⟩
    -- A                                 ∎
    -- cong (A ∘F_) ∫V-id ∙ F-lUnit
  Psh-CwF .CwF.[][]Ty {Γ = Γ} A σ' σ =
    Functor≡ (λ c → refl) λ f → cong (A .F-hom) (ΣPathP (refl , isSetEl⁰ (Γ .F-ob _) _ _ _ _))
    -- same as above, I changed to a Functor≡ to get more definitional equalities
    -- cong (λ F → A ∘F F) ∫V-seq ∙ F-assoc
  Psh-CwF .CwF.Tm Γ A = -Tm Γ A
  Psh-CwF .CwF.isSetTm = -isSetTm
  Psh-CwF .CwF._[_]Tm M σ .fst = λ I x → M .fst I (σ .N-ob I x)
  Psh-CwF .CwF._[_]Tm {Γ} {Δ} {A} M σ .snd {I} {J} {x} {y} (f , p) =
    (A ∘F ∫V-hom σ) .F-hom (f , p) (M .fst J (σ .N-ob J y)) ≡⟨ {!!} ⟩
    M .fst I (σ .N-ob I x)                                  ∎
  Psh-CwF .CwF.[id]Tm {Γ} {A} M = {!!}
  Psh-CwF .CwF.[][]Tm = {!!}
  Psh-CwF .CwF._✦_ Γ A .F-ob I = Σ⁰ (Γ .F-ob I) (λ x → A .F-ob (I , x))
  Psh-CwF .CwF._✦_ Γ A .F-hom {I} {J} f (x , y) = (Γ .F-hom f x) , A .F-hom (f , refl) y
  Psh-CwF .CwF._✦_ Γ A .F-id {I} = funExt λ x → ΣPathP (funExt⁻ (Γ .F-id) (x .fst) , (goal x ▷ funExt⁻ (A .F-id) (x .snd)))
    where
      goal : ∀ x →
        PathP (λ i → El (A .F-ob (I , (Γ .F-id i (x .fst)))))
          (A .F-hom (id C , refl) (x .snd))
          (A .F-hom (∫V Γ .id) (x .snd))
      goal x =
        funExt⁻ (F-hom-PathP A (id C , refl) (id C , _) refl (λ i → I , Γ .F-id i (x .fst)) refl) (x .snd)
  Psh-CwF .CwF._✦_ Γ A .F-seq {I} {J} {K} f g = funExt λ x → ΣPathP ((funExt⁻ (Γ .F-seq f g) (x .fst)) , goal x)
    where
      goal : ∀ x →
        PathP (λ i → El (A .F-ob (K , funExt⁻ (Γ .F-seq f g) (x .fst) i)))
          (A .F-hom (g ⋆⟨ C ⟩ f , refl) (x .snd))
          (A .F-hom (g , refl) (A .F-hom (f , refl) (x .snd)))
      goal' : ∀ x →
        PathP (λ i → El (A .F-ob (K , funExt⁻ (Γ .F-seq f g) (x .fst) i)))
          (A .F-hom (g ⋆⟨ C ⟩ f , refl) (x .snd))
          (A .F-hom ((f , refl) ⋆⟨ ∫V Γ ⟩ (g , refl)) (x .snd))
      goal' x =
        funExt⁻ (F-hom-PathP A (seq' C g f , refl)
                  (seq' (∫V Γ) (f , refl) (g , refl)) refl (λ i → K , Γ .F-seq f g i (x .fst)) refl) (x .snd)
      goal x = goal' x ▷ funExt⁻ (A .F-seq (f , refl) (g , refl)) (x .snd)
  Psh-CwF .CwF.p .N-ob I x = x .fst
  Psh-CwF .CwF.p .N-hom f = refl
  Psh-CwF .CwF.q .fst I = snd
  Psh-CwF .CwF.q {Γ} {A} .snd {I} {J} {x} {y} u = {!!}
  Psh-CwF .CwF._⁺ σ .N-ob I x = (σ .N-ob I (x .fst)) , (x .snd)
  Psh-CwF .CwF._⁺ {Γ} {Δ} {A} σ .N-hom {I} {J} f = funExt goal
    where
      fst≡ : ∀ x → N-ob σ J (F-hom Δ f (x .fst)) ≡ F-hom Γ f (N-ob σ I (x .fst))
      fst≡ x = funExt⁻ (σ .N-hom f) (x .fst)
      snd≡ : ∀ x → PathP
                    (λ i → El (A .F-ob (J , fst≡ x i)))
                    (F-hom A (f , _) (x .snd))
                    (A .F-hom (f , refl) (x .snd))
      snd≡ x = funExt⁻ (F-hom-PathP A (f , _) (f , refl) refl (λ i → J , fst≡ x i) refl) (x .snd)
      goal : ∀ x → (N-ob σ J (F-hom Δ f (x .fst)) ,
                     F-hom A (f , _) (x .snd))
                    ≡
                    (F-hom Γ f (N-ob σ I (x .fst)) ,
                     A .F-hom (f , refl) (x .snd))
      goal x = ΣPathP (fst≡ x , snd≡ x)

  Psh-CwF .CwF.⟨_⟩ = {!!}
  Psh-CwF .CwF.⟨⟩∘ = {!!}
  Psh-CwF .CwF.p⁺∘⟨q⟩≡id = {!!}
  Psh-CwF .CwF.∘⁺ {Γ} {Δ} {Θ} {A} σ' σ =
    makeNatTransPathP (cong (Δ ✦_) ([][]Ty A σ' σ)) refl refl
  Psh-CwF .CwF.id⁺ {Γ} {A} =
    makeNatTransPathP (cong (Γ ✦_) ([id]Ty A)) refl refl
  Psh-CwF .CwF.p∘⁺ = {!!}
  Psh-CwF .CwF.[p][⁺]Ty = {!!}
  Psh-CwF .CwF.q[⁺]Tm = {!!}
  Psh-CwF .CwF.p∘⟨⟩≡id = {!!}
  Psh-CwF .CwF.[p][⟨⟩]Ty = {!!}
  Psh-CwF .CwF.q[⟨⟩]Tm = {!!}
