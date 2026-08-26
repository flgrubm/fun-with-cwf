module TarskiUniverse.Instances.CumulativeHierarchy where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Transport

open import Cubical.Data.IterativeSets.Base
open import Cubical.HITs.CumulativeHierarchy

open import Utils.CumulativeHierarchyEquivIterativeSets

open import TarskiUniverse.Instances.IterativeSets renaming ( BareTarskiUniverseV to BareTarskiUniverseV⁰
                                                            ; TarskiUniverseV     to TarskiUniverseV⁰
                                                            ; hasPiV              to hasPiV⁰ )
open import TarskiUniverse.Base

-- The Tarski universe instance for the cumulative hierarchy
module _ {ℓ : Level} where

  BareTarskiUniverseV : BareTarskiUniverse ℓ (V ℓ)
  BareTarskiUniverseV = subst⁻ (BareTarskiUniverse ℓ) V≡V⁰ (BareTarskiUniverseV⁰ ℓ)
  
  TarskiUniverseV : TarskiUniverse ℓ (V ℓ)
  TarskiUniverseV = subst⁻ (TarskiUniverse ℓ) V≡V⁰ (TarskiUniverseV⁰ ℓ)

  -- TODO: implement hasPiV : hasPi BareTarskiUniverseV, this is a bit more tedious but should be easy using the SIP
