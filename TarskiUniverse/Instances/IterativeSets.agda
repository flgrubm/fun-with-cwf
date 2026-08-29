module TarskiUniverse.Instances.IterativeSets where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Unit

open import Cubical.Data.IterativeSets.Base
open import Cubical.Data.IterativeSets.Sigma
open import Cubical.Data.IterativeSets.Pi
open import Cubical.Data.IterativeSets.Unit
open import Cubical.Data.IterativeSets.Identity

open import TarskiUniverse.Base

module _ (ℓ : Level) where
  BareTarskiUniverseV : BareTarskiUniverse ℓ (V⁰ {ℓ})
  BareTarskiUniverseV .BareTarskiUniverse.isSetU  = isSetV⁰
  BareTarskiUniverseV .BareTarskiUniverse.El      = El⁰
  BareTarskiUniverseV .BareTarskiUniverse.isSetEl = isSetEl⁰

  hasUnitV : hasUnit BareTarskiUniverseV
  hasUnitV .hasUnit.Unit          = unit⁰
  hasUnitV .hasUnit.isContrElUnit = subst isContr (sym El⁰unit⁰IsUnit*) isContrUnit*

  hasSigmaV : hasSigma BareTarskiUniverseV
  hasSigmaV .hasSigma.Sigma        = Σ⁰
  hasSigmaV .hasSigma.SigmaIso _ _ = idIso

  TarskiUniverseV : TarskiUniverse ℓ (V⁰ {ℓ})
  TarskiUniverseV .TarskiUniverse.TU         = BareTarskiUniverseV
  TarskiUniverseV .TarskiUniverse.hasUnitTU  = hasUnitV
  TarskiUniverseV .TarskiUniverse.hasSigmaTU = hasSigmaV

  hasPiV : hasPi BareTarskiUniverseV
  hasPiV .hasPi.Pi        = Π⁰
  hasPiV .hasPi.PiIso _ _ = idIso

  hasEqV : hasEq BareTarskiUniverseV
  hasEqV .hasEq.Eq          = Id⁰
  hasEqV .hasEq.EqIso _ _ _ = idIso
