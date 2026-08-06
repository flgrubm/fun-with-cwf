module TarskiUniverse.Instances.FinSets  where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv

open import Cubical.Data.Unit
open import Cubical.Data.SumFin
open import Cubical.Data.Nat

open import TarskiUniverse.Base

open TarskiUniverse-Base

module _ where
  ℕ-TarskiUniverse-Base : TarskiUniverse-Base ℓ-zero ℓ-zero
  ℕ-TarskiUniverse-Base .U         = ℕ
  ℕ-TarskiUniverse-Base .isSetU    = isSetℕ
  ℕ-TarskiUniverse-Base .El n      = Fin n
  ℕ-TarskiUniverse-Base .isSetEl n = isSetFin {k = n}

  ℕ-TarskiUniverse-Unit : TarskiUniverse-Unit ℕ-TarskiUniverse-Base
  ℕ-TarskiUniverse-Unit .TarskiUniverse-Unit.Unit          = 1
  ℕ-TarskiUniverse-Unit .TarskiUniverse-Unit.isContrElUnit = isContrSumFin1

  ℕ-TarskiUniverse-Sig : TarskiUniverse-Sig ℕ-TarskiUniverse-Base
  ℕ-TarskiUniverse-Sig .TarskiUniverse-Sig.Sig _      = totalSum
  ℕ-TarskiUniverse-Sig .TarskiUniverse-Sig.SigIso _ _ = equivToIso (invEquiv (SumFinΣ≃ _ _))

  ℕ-TarskiUniverse : TarskiUniverse ℓ-zero ℓ-zero
  ℕ-TarskiUniverse .TarskiUniverse.TU-Base = ℕ-TarskiUniverse-Base
  ℕ-TarskiUniverse .TarskiUniverse.TU-Unit = ℕ-TarskiUniverse-Unit
  ℕ-TarskiUniverse .TarskiUniverse.TU-Sig = ℕ-TarskiUniverse-Sig

  ℕ-TarskiUniverse-Pi : TarskiUniverse-Pi ℕ-TarskiUniverse-Base
  ℕ-TarskiUniverse-Pi .TarskiUniverse-Pi.Pi _ = totalProd
  ℕ-TarskiUniverse-Pi .TarskiUniverse-Pi.PiIso _ _ = equivToIso (invEquiv (SumFinΠ≃ _ _))
