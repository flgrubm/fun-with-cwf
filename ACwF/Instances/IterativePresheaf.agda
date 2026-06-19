{-# OPTIONS --lossy-unification #-}
module ACwF.Instances.IterativePresheaf where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Unit
open import Cubical.Data.Sigma
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Functors.Constant
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Limits.Terminal
open import Cubical.Data.IterativeSets.Base renaming (V⁰ to V ; El⁰ to El)
open import Cubical.Data.IterativeSets.Empty
open import Cubical.Data.IterativeSets.Unit
open import Cubical.Data.IterativeSets.Sigma
open import Utils.IterativePresheaf
open import Utils.VCat
open import ACwF.Base

open Category
open Functor
open NatTrans

ConstComp : ∀ {ℓ ℓ' ℓ'' ℓ'''} {C E : Category ℓ ℓ'} {D : Category ℓ'' ℓ'''}
            (G : Functor C E) (x : D .ob)
          → Constant E D x ∘F G ≡ Constant C D x
ConstComp G x = Functor≡ (λ c → refl) (λ f → refl)

-- this is needed to prevent Agda from reducing to much and getting stuck
opaque
  unit⁰-opaque : ∀ {ℓV} → V {ℓV}
  unit⁰-opaque = unit⁰
  tt-opaque : ∀ {ℓV} → El (unit⁰-opaque {ℓV})
  tt-opaque = tt*

module _ {ℓob ℓhom ℓV : Level} (C : Category ℓob ℓhom) where
  open Algebraic (PRESHEAFV C ℓV)
  private abstract
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
    NullType : Functor (∫V Γ) (VCat ℓV)
    NullType = Constant _ _ unit⁰-opaque
    Tm-categorical : Type (ℓ-max (ℓ-max ℓob ℓhom) ℓV)
    Tm-categorical = FUNCTOR (∫V Γ) (VCat ℓV) [ NullType , A ]
    Tm-categorical-isSet : isSet (Tm-categorical)
    Tm-categorical-isSet = isSetNatTrans

  []Tm :
    ∀ Γ Δ
    → (A : Functor (∫V Γ) (VCat ℓV))
    → (σ : NatTrans Δ Γ)
    → Tm-categorical Γ A
    → Tm-categorical Δ (A ∘F ∫V-hom σ)
  []Tm Γ Δ A σ M .N-ob x = M .N-ob (∫V-hom σ .F-ob x)
  []Tm Γ Δ A σ M .N-hom f = (M .N-hom) _

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
  Psh-CwF .CwF.Tm Γ A = Tm-categorical Γ A
  Psh-CwF .CwF.isSetTm = Tm-categorical-isSet
  Psh-CwF .CwF._[_]Tm M σ = []Tm _ _ _ σ M
  Psh-CwF .CwF.[id]Tm M = makeNatTransPathP refl ([id]Ty _) refl
  Psh-CwF .CwF.[][]Tm M σ' σ = makeNatTransPathP refl ([][]Ty _ _ _) refl
  Psh-CwF .CwF._▹_ Γ A .F-ob I = Σ⁰ (Γ .F-ob I) (λ x → A .F-ob (I , x))
  Psh-CwF .CwF._▹_ Γ A .F-hom {I} {J} f (x , y) = (Γ .F-hom f x) , A .F-hom (f , refl) y
  Psh-CwF .CwF._▹_ Γ A .F-id {I} = funExt λ x → ΣPathP (funExt⁻ (Γ .F-id) (x .fst) , (goal x ▷ funExt⁻ (A .F-id) (x .snd)))
    where
      goal : ∀ x →
        PathP (λ i → El (A .F-ob (I , (Γ .F-id i (x .fst)))))
          (A .F-hom (id C , refl) (x .snd))
          (A .F-hom (∫V Γ .id) (x .snd))
      goal x =
        funExt⁻ (F-hom-PathP A (id C , refl) (id C , _) refl (λ i → I , Γ .F-id i (x .fst)) refl) (x .snd)
  Psh-CwF .CwF._▹_ Γ A .F-seq {I} {J} {K} f g = funExt λ x → ΣPathP ((funExt⁻ (Γ .F-seq f g) (x .fst)) , goal x)
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
  Psh-CwF .CwF.q .N-ob x = {!!}
  Psh-CwF .CwF.q .N-hom = {!!}
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

  Psh-CwF .CwF.⟨_⟩ M .N-ob I x = x , M .N-ob (I , x) tt-opaque
  Psh-CwF .CwF.⟨_⟩ {Γ} {A} M .N-hom {I} {J} f = funExt (λ x → ΣPathP (refl , funExt⁻ (M .N-hom _) tt-opaque))
  Psh-CwF .CwF.⟨⟩∘ = {!!}
  Psh-CwF .CwF.p⁺∘⟨q⟩≡id = {!!}
  Psh-CwF .CwF.∘⁺ {Γ} {Δ} {Θ} {A} σ' σ =
    makeNatTransPathP (cong (Δ ▹_) ([][]Ty A σ' σ)) refl refl
  Psh-CwF .CwF.id⁺ {Γ} {A} =
    makeNatTransPathP (cong (Γ ▹_) ([id]Ty A)) refl refl
  Psh-CwF .CwF.p∘⁺ σ = makeNatTransPath refl
  Psh-CwF .CwF.[p][⁺]Ty {Γ} {Δ} B σ = Functor≡ (λ c → refl) (λ f → cong (B .F-hom) (ΣPathP (refl , isSetEl⁰ (Γ .F-ob _) _ _ _ _)))
  Psh-CwF .CwF.q[⁺]Tm = {!!}
  Psh-CwF .CwF.p∘⟨⟩≡id = {!!}
  Psh-CwF .CwF.[p][⟨⟩]Ty = {!!}
  Psh-CwF .CwF.q[⟨⟩]Tm = {!!}
