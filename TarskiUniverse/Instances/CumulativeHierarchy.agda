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
                                                            ; hasWV               to hasWV⁰ )
open import TarskiUniverse.Base

-- The Tarski universe instance for the cumulative hierarchy
module _ {ℓ : Level} where

  BareTarskiUniverseV : BareTarskiUniverse ℓ (V ℓ)
  BareTarskiUniverseV = subst⁻ (BareTarskiUniverse ℓ) V≡V⁰ (BareTarskiUniverseV⁰ ℓ)

  TarskiUniverseV : TarskiUniverse ℓ (V ℓ)
  TarskiUniverseV = subst⁻ (TarskiUniverse ℓ) V≡V⁰ (TarskiUniverseV⁰ ℓ)

  -- TODO: implement hasPiV : hasPi BareTarskiUniverseV, this is a bit more tedious but should be easy using the SIP

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
  hasWV : hasW BareTarskiUniverseV
  hasWV = transportStructure hasW (hasWV⁰ ℓ)
