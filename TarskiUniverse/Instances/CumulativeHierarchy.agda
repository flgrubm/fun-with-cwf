{-# OPTIONS --lossy-unification #-}
module TarskiUniverse.Instances.CumulativeHierarchy where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Transport

open import Cubical.Data.Sigma

open import Cubical.Data.IterativeSets.Base
open import Cubical.Data.IterativeSets.IsCumulativeHierarchy
open import Cubical.HITs.CumulativeHierarchy

open import TarskiUniverse.Instances.IterativeSets renaming ( BareTarskiUniverseV to BareTarskiUniverseV⁰
                                                            ; TarskiUniverseV     to TarskiUniverseV⁰
                                                            ; hasPiV              to hasPiV⁰
                                                            ; hasSigmaV           to hasSigmaV⁰
                                                            ; hasUniverseV        to hasUniverseV⁰
                                                            ; hasUniversePiV      to hasUniversePiV⁰
                                                            ; hasUniverseSigmaV   to hasUniverseSigmaV⁰ )
open import TarskiUniverse.Base

-- The Tarski universe instance for the cumulative hierarchy
module _ {ℓ : Level} where

  BareTarskiUniverseV : BareTarskiUniverse ℓ (V ℓ)
  BareTarskiUniverseV = subst⁻ (BareTarskiUniverse ℓ) V≡V⁰ (BareTarskiUniverseV⁰ ℓ)

  TarskiUniverseV : TarskiUniverse ℓ (V ℓ)
  TarskiUniverseV = subst⁻ (TarskiUniverse ℓ) V≡V⁰ (TarskiUniverseV⁰ ℓ)

  -- Transport in a record is componentwise, so this is a definitional
  -- consequence of the two transports above.
  _ : TarskiUniverseV .TarskiUniverse.TU ≡ BareTarskiUniverseV
  _ = refl

-- Extra structure is transported together with the universe it lives on;
-- the first component of the transported pair is again `BareTarskiUniverseV`.
private
  transportStructure : {ℓ : Level} (S : {X : Type (ℓ-suc ℓ)} → BareTarskiUniverse ℓ X → Type (ℓ-suc ℓ))
                     → S (BareTarskiUniverseV⁰ ℓ) → S BareTarskiUniverseV
  transportStructure {ℓ} S s =
    subst⁻ (λ X → Σ[ TU ∈ BareTarskiUniverse ℓ X ] S TU) V≡V⁰ (BareTarskiUniverseV⁰ ℓ , s) .snd

module _ {ℓ : Level} where
  hasPiV : hasPi BareTarskiUniverseV
  hasPiV = transportStructure hasPi (hasPiV⁰ ℓ)

-- The internal universe at a successor level depends on the universe and,
-- through its closure, on Π and Σ: transport all of them together.  The
-- transported Π and Σ are definitionally `hasPiV` and the Σ of
-- `TarskiUniverseV`.  (Without `--lossy-unification` this block exhausts
-- memory, as the V⁰ universe does.)
module _ {ℓ : Level} where
  private
    UnivStructure : {X : Type (ℓ-suc (ℓ-suc ℓ))} → BareTarskiUniverse (ℓ-suc ℓ) X → Type (ℓ-suc (ℓ-suc ℓ))
    UnivStructure TU = Σ[ 𝒰 ∈ hasUniverse TU ] Σ[ P ∈ hasPi TU ] Σ[ S ∈ hasSigma TU ]
                         hasUniversePi TU 𝒰 P × hasUniverseSigma TU 𝒰 S

    univStructureV : UnivStructure BareTarskiUniverseV
    univStructureV = transportStructure UnivStructure
      (hasUniverseV⁰ ℓ , hasPiV⁰ (ℓ-suc ℓ) , hasSigmaV⁰ (ℓ-suc ℓ) , hasUniversePiV⁰ ℓ , hasUniverseSigmaV⁰ ℓ)

  hasUniverseV : hasUniverse (BareTarskiUniverseV {ℓ-suc ℓ})
  hasUniverseV = univStructureV .fst

  hasUniversePiV : hasUniversePi BareTarskiUniverseV hasUniverseV hasPiV
  hasUniversePiV = univStructureV .snd .snd .snd .fst

  hasUniverseSigmaV : hasUniverseSigma BareTarskiUniverseV hasUniverseV (TarskiUniverseV .TarskiUniverse.hasSigmaTU)
  hasUniverseSigmaV = univStructureV .snd .snd .snd .snd
