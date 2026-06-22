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

-- this is needed to prevent Agda from reducing too much and getting stuck
private opaque
  unit⁰-opaque : ∀ {ℓV} → V {ℓV}
  unit⁰-opaque = unit⁰
  tt-opaque : ∀ {ℓV} → El (unit⁰-opaque {ℓV})
  tt-opaque = tt*
  unit⁰-opaque-contr : ∀ {ℓ} x → x ≡ tt-opaque {ℓ}
  unit⁰-opaque-contr x = isPropUnit* x tt-opaque

module _ {ℓob ℓhom ℓV : Level} (C : Category ℓob ℓhom) where
  open Algebraic (PRESHEAFV C ℓV)
  private abstract
    -- The empty context
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

  -- the unit type
  Psh-UnitType : {Γ : PresheafV C ℓV} → Functor (∫V Γ) (VCat ℓV)
  Psh-UnitType = Constant _ _ unit⁰-opaque

  -- elements of A (terms) can be seen as natural transformations from the unit type to A
  private module _ (Γ : PresheafV C ℓV) (A : Functor (∫V Γ) (VCat ℓV)) where
    Psh-Tm : Type (ℓ-max (ℓ-max ℓob ℓhom) ℓV)
    Psh-Tm = FUNCTOR (∫V Γ) (VCat ℓV) [ Psh-UnitType , A ]
    Psh-Tm-isSet : isSet (Psh-Tm)
    Psh-Tm-isSet = isSetNatTrans

  private
    []Tm : ∀ Γ Δ
      → (A : Functor (∫V Γ) (VCat ℓV))
      → (σ : NatTrans Δ Γ)
      → Psh-Tm Γ A
      → Psh-Tm Δ (A ∘F ∫V-hom σ)
    []Tm Γ Δ A σ M .N-ob x = M .N-ob (∫V-hom σ .F-ob x)
    []Tm Γ Δ A σ M .N-hom f = (M .N-hom) _

  Psh-CwF : CwF (ℓ-max (ℓ-max ℓob ℓhom) (ℓ-suc ℓV)) (ℓ-max (ℓ-max ℓob ℓhom) ℓV)
  open CwF Psh-CwF
  Psh-CwF .CwF.⟨⟩ = PSH-Terminal

  Psh-CwF .CwF.Ty Γ = Functor (∫V Γ) (VCat ℓV)
  Psh-CwF .CwF.isSetTy Γ = isSetFunctor isSetV⁰
  Psh-CwF .CwF._[_]Ty A σ = A ∘F ∫V-hom σ
  Psh-CwF .CwF.[id]Ty {Γ} A =
    Functor≡
      (λ c → refl)
      (λ f → cong (A .F-hom) (ΣPathP (refl , isSetEl⁰ (Γ .F-ob _) _ _ _ _)))
    -- alternative proof, more readable but with less definitional equalities
    -- A ∘F ∫V-hom (id (PRESHEAFV C ℓV)) ≡⟨ cong (λ F → A ∘F F) ∫V-id ⟩
    -- A ∘F Id                           ≡⟨ F-lUnit ⟩
    -- A                                 ∎
  Psh-CwF .CwF.[][]Ty {Γ = Γ} A σ' σ =
    Functor≡ (λ c → refl) λ f → cong (A .F-hom) (ΣPathP (refl , isSetEl⁰ (Γ .F-ob _) _ _ _ _))
    -- alternative proof, more readable but with less definitional equalities
    -- cong (λ F → A ∘F F) ∫V-seq ∙ F-assoc

  Psh-CwF .CwF.Tm Γ A = Psh-Tm Γ A
  Psh-CwF .CwF.isSetTm = Psh-Tm-isSet
  Psh-CwF .CwF._[_]Tm M σ = []Tm _ _ _ σ M
  Psh-CwF .CwF.[id]Tm M = makeNatTransPathP refl ([id]Ty _) refl
  Psh-CwF .CwF.[][]Tm M σ' σ = makeNatTransPathP refl ([][]Ty _ _ _) refl

  Psh-CwF .CwF._▹_ Γ A .F-ob I = Σ⁰ (Γ .F-ob I) (λ x → A .F-ob (I , x))
  Psh-CwF .CwF._▹_ Γ A .F-hom {I} {J} f (x , y) = (Γ .F-hom f x) , A .F-hom (f , refl) y
  -- the proofs of the functoriality of the extended context could perhaps be simplified?
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

  Psh-CwF .CwF.q .N-ob x _ = x .snd .snd
  Psh-CwF .CwF.q {Γ} {A} .N-hom {x} {y} (f , p) = funExt λ _ →
      y .snd .snd                                                                            ≡⟨ sym (fromPathP (λ i → p i .snd)) ⟩
      transport (λ i → El (A .F-ob (y .fst , p i .fst))) (A .F-hom (f , refl) (x .snd .snd)) ≡⟨ fromPathP
                                                                                                  (funExt⁻ (F-hom-PathP A (f , refl) (f , λ i → p i .fst) refl
                                                                                                    (ΣPathP (refl , λ i → p i .fst)) refl) (x .snd .snd)) ⟩
      A .F-hom (f , λ i → p i .fst) (x .snd .snd)                                            ≡⟨ sym (funExt⁻
                                                                                                      (F-hom-PathP A (∫V-hom (Psh-CwF .CwF.p {Γ} {A}) .F-hom (f , p))
                                                                                                        (f , λ i → p i .fst) refl refl refl)
                                                                                                      (x .snd .snd)) ⟩
      A .F-hom (∫V-hom (Psh-CwF .CwF.p {Γ} {A}) .F-hom (f , p)) (x .snd .snd)                ∎
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

  -- finally, all the properties are fairly trivial
  Psh-CwF .CwF.⟨_⟩ M .N-ob I x = x , M .N-ob (I , x) tt-opaque
  Psh-CwF .CwF.⟨_⟩ {Γ} {A} M .N-hom {I} {J} f = funExt (λ x → ΣPathP (refl , funExt⁻ (M .N-hom _) tt-opaque))
  Psh-CwF .CwF.⟨⟩∘ M σ = makeNatTransPath refl
  Psh-CwF .CwF.p⁺∘⟨q⟩≡id = makeNatTransPath refl
  Psh-CwF .CwF.∘⁺ {Γ} {Δ} {Θ} {A} σ' σ =
    makeNatTransPathP (cong (Δ ▹_) ([][]Ty A σ' σ)) refl refl
  Psh-CwF .CwF.id⁺ {Γ} {A} =
    makeNatTransPathP (cong (Γ ▹_) ([id]Ty A)) refl refl
  Psh-CwF .CwF.p∘⁺ σ = makeNatTransPath refl
  Psh-CwF .CwF.[p][⁺]Ty {Γ} {Δ} B σ = Functor≡ (λ c → refl) (λ f → F-hom-PathP B _ _ refl refl refl)
  Psh-CwF .CwF.q[⁺]Tm σ = makeNatTransPathP refl ([p][⁺]Ty _ σ) refl
  Psh-CwF .CwF.p∘⟨⟩≡id M = makeNatTransPath refl
  Psh-CwF .CwF.[p][⟨⟩]Ty B a = Functor≡ (λ c → refl) (λ f → F-hom-PathP B _ _ refl refl refl)
  Psh-CwF .CwF.q[⟨⟩]Tm {A = A} M = makeNatTransPathP refl ([p][⟨⟩]Ty A M) (λ i x u → M .N-ob x (unit⁰-opaque-contr u (~ i)))
