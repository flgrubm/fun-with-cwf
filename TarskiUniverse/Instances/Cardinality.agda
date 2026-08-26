module TarskiUniverse.Instances.Cardinality where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Function
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.HITs.SetTruncation as ∥₂
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.PropositionalTruncation.Monad

open import Cubical.Data.Cardinal.Base
open import Cubical.Axiom.Choice

open import TarskiUniverse.Base

private
  variable
    ℓ ℓ' ℓ'' : Level

-- The (textbook) axiom of choice: every set satisfies the propositional
-- (n = 1) axiom of choice, at every target level. Assumed as a hypothesis
-- (not a `postulate`, since this project is built with --safe) that the
-- whole development below is conditional on.
module _ (ac1 : {ℓa ℓb : Level} {A : Type ℓa} → isSet A → satAC ℓb 1 A) where

  -- Corollary: a set-indexed family that is pointwise merely inhabited has a
  -- (merely-existing) global choice function.
  choiceFn : {X : Type ℓ} (isSetX : isSet X) (B : X → Type ℓ') (P : (x : X) → B x → Type ℓ'')
           → ((x : X) → ∃[ y ∈ B x ] P x y)
           → ∃[ f ∈ ((x : X) → B x) ] ((x : X) → P x (f x))
  choiceFn {ℓ' = ℓ'} {ℓ'' = ℓ''} isSetX B P pointwise =
    invEq (_ , satAC→satAC∃ (ac1 {ℓb = ℓ-max ℓ' ℓ''} isSetX) B P) pointwise

  -- a variant with no extra property: just choosing a witness for each `B x`
  choiceFn1 : {X : Type ℓ} (isSetX : isSet X) (B : X → Type ℓ')
            → ((x : X) → ∥ B x ∥₁) → ∥ ((x : X) → B x) ∥₁
  choiceFn1 {ℓ' = ℓ'} isSetX B pointwise =
    PT.map fst (choiceFn isSetX B (λ _ _ → Unit* {ℓ'}) (λ x → PT.map (λ b → b , tt*) (pointwise x)))

  -- a section of `∣_∣₂ : hSet ℓ → Card` merely exists
  ∃El : ∃[ El' ∈ (Card {ℓ} → hSet ℓ) ] ((c : Card {ℓ}) → ∣ El' c ∣₂ ≡ c)
  ∃El {ℓ} = choiceFn isSetCard (λ _ → hSet ℓ) (λ c X → ∣ X ∣₂ ≡ c) pointwise
    where
    pointwise : (c : Card {ℓ}) → ∃[ X ∈ hSet ℓ ] ∣ X ∣₂ ≡ c
    pointwise = ∥₂.elim (λ _ → isProp→isSet isPropPropTrunc) (λ X → ∣ X , refl ∣₁)

  IsTarski : Type (ℓ-suc (ℓ-suc ℓ))
  IsTarski {ℓ} = Σ[ TU ∈ BareTarskiUniverse ℓ (Card {ℓ}) ] hasUnit TU × hasSigma TU

  module _ {ℓ : Level} (El' : Card {ℓ} → hSet ℓ) (isEl'∈ : (c : Card {ℓ}) → ∣ El' c ∣₂ ≡ c) where

    El : Card {ℓ} → Type ℓ
    El c = El' c .fst

    isSetEl : (c : Card {ℓ}) → isSet (El c)
    isSetEl c = El' c .snd

    TU : BareTarskiUniverse ℓ (Card {ℓ})
    TU = record { isSetU = isSetCard ; El = El ; isSetEl = isSetEl }

    SigmaHSet : (A : Card {ℓ}) (B : El A → Card {ℓ}) → hSet ℓ
    SigmaHSet A B .fst = Σ[ x ∈ El A ] El (B x)
    SigmaHSet A B .snd = isSetΣ (isSetEl A) (λ x → isSetEl (B x))

    Sigma : (A : Card {ℓ}) → (El A → Card {ℓ}) → Card {ℓ}
    Sigma A B = card (SigmaHSet A B)

    SigmaIsoWitness : (p : Σ[ A ∈ Card {ℓ} ] (El A → Card {ℓ}))
                   → ∥ Iso (El (Sigma (p .fst) (p .snd))) (Σ[ x ∈ El (p .fst) ] El (p .snd x)) ∥₁
    SigmaIsoWitness (A , B) = PT.map toIso mereEq
      where
      mereEq : ∥ El' (Sigma A B) ≡ SigmaHSet A B ∥₁
      mereEq = Iso.fun ∥₂.PathIdTrunc₀Iso (isEl'∈ (Sigma A B))

      toIso : El' (Sigma A B) ≡ SigmaHSet A B
            → Iso (El (Sigma A B)) (Σ[ x ∈ El A ] El (B x))
      toIso eq = equivToIso (pathToEquiv (cong fst eq))

    buildTarski : ∥ IsTarski {ℓ} ∥₁
    buildTarski = do
      sigmaIsoAll ← choiceFn1 (isSetΣ isSetCard (λ A → isSetΠ (λ _ → isSetCard)))
                            (λ p → Iso (El (Sigma (p .fst) (p .snd))) (Σ[ x ∈ El (p .fst) ] El (p .snd x)))
                            SigmaIsoWitness

      unitEq ← Iso.fun ∥₂.PathIdTrunc₀Iso (isEl'∈ (card (Unit* , isSetUnit*)))

      let
        hasSigmaStruct : hasSigma TU
        hasSigmaStruct = record { Sigma = Sigma ; SigmaIso = λ A B → sigmaIsoAll (A , B) }

        hasUnitStruct : hasUnit TU
        hasUnitStruct = record
          { Unit = card (Unit* , isSetUnit*)
          ; isContrElUnit = subst isContr (sym (cong fst unitEq)) isContrUnit*
          }

      ∣ TU , hasUnitStruct , hasSigmaStruct ∣₁

  ∃Tarski : ∥ IsTarski {ℓ} ∥₁
  ∃Tarski {ℓ} = do
    (El' , isEl'∈) ← ∃El {ℓ}
    buildTarski El' isEl'∈
