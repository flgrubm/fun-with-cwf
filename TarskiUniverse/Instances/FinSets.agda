module TarskiUniverse.Instances.FinSets  where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv

open import Cubical.Data.Unit
open import Cubical.Data.SumFin
open import Cubical.Data.Nat

open import TarskiUniverse.Base

open BareTarskiUniverse

module _ where
  BareTarskiUniverseℕ : BareTarskiUniverse ℓ-zero ℕ
  BareTarskiUniverseℕ .isSetU    = isSetℕ
  BareTarskiUniverseℕ .El n      = Fin n
  BareTarskiUniverseℕ .isSetEl n = isSetFin {k = n}

  hasUnitℕ : hasUnit BareTarskiUniverseℕ
  hasUnitℕ .hasUnit.Unit          = 1
  hasUnitℕ .hasUnit.isContrElUnit = isContrSumFin1

  hasSigmaℕ : hasSigma BareTarskiUniverseℕ
  hasSigmaℕ .hasSigma.Sigma _      = totalSum
  hasSigmaℕ .hasSigma.SigmaIso _ _ = equivToIso (invEquiv (SumFinΣ≃ _ _))

  TarskiUniverseℕ : TarskiUniverse ℓ-zero ℕ
  TarskiUniverseℕ .TarskiUniverse.TU = BareTarskiUniverseℕ
  TarskiUniverseℕ .TarskiUniverse.hasUnitTU = hasUnitℕ
  TarskiUniverseℕ .TarskiUniverse.hasSigmaTU = hasSigmaℕ

  hasPiℕ : hasPi BareTarskiUniverseℕ
  hasPiℕ .hasPi.Pi _      = totalProd
  hasPiℕ .hasPi.PiIso _ _ = equivToIso (invEquiv (SumFinΠ≃ _ _))
