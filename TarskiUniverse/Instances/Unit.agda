module TarskiUniverse.Instances.Unit  where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Unit

open import TarskiUniverse.Base

open BareTarskiUniverse

module _ (ℓ : Level) where
  Unit-TarskiUniverse-Base : BareTarskiUniverse ℓ (Unit* {ℓ})
  Unit-TarskiUniverse-Base .isSetU = isSetUnit*
  Unit-TarskiUniverse-Base .El x = Unit*
  Unit-TarskiUniverse-Base .isSetEl _ = isSetUnit*

  hasSigmaUnit : hasSigma Unit-TarskiUniverse-Base
  hasSigmaUnit .hasSigma.Sigma A x = tt*
  hasSigmaUnit .hasSigma.SigmaIso _ _ .Iso.fun x = tt* , tt*
  hasSigmaUnit .hasSigma.SigmaIso _ _ .Iso.inv x = tt*
  hasSigmaUnit .hasSigma.SigmaIso _ _ .Iso.sec (tt* , tt*) = refl
  hasSigmaUnit .hasSigma.SigmaIso _ _ .Iso.ret tt* = refl

  hasUnitUnit : hasUnit Unit-TarskiUniverse-Base
  hasUnitUnit .hasUnit.Unit = tt*
  hasUnitUnit .hasUnit.isContrElUnit = isContrUnit*

  Unit-TarskiUniverse : TarskiUniverse ℓ Unit*
  Unit-TarskiUniverse .TarskiUniverse.TU = Unit-TarskiUniverse-Base
  Unit-TarskiUniverse .TarskiUniverse.hasUnitTU = hasUnitUnit
  Unit-TarskiUniverse .TarskiUniverse.hasSigmaTU = hasSigmaUnit

  hasPiUnit : hasPi Unit-TarskiUniverse-Base
  hasPiUnit .hasPi.Pi A B = tt*
  hasPiUnit .hasPi.PiIso _ _ .Iso.fun _ _ = tt*
  hasPiUnit .hasPi.PiIso _ _ .Iso.inv _ = tt*
  hasPiUnit .hasPi.PiIso _ _ .Iso.sec _ _ _ = tt*
  hasPiUnit .hasPi.PiIso _ _ .Iso.ret tt* = refl

  -- the universe is again the unit type, and everything decodes to `tt*`
  hasUniverseUnit : hasUniverse Unit-TarskiUniverse-Base
  hasUniverseUnit .hasUniverse.Univ     = tt*
  hasUniverseUnit .hasUniverse.decode _ = tt*

  hasUniversePiUnit : hasUniversePi Unit-TarskiUniverse-Base hasUniverseUnit hasPiUnit
  hasUniversePiUnit .hasUniversePi.piU _ _        = tt*
  hasUniversePiUnit .hasUniversePi.decode-piU _ _ = refl

  hasUniverseSigmaUnit : hasUniverseSigma Unit-TarskiUniverse-Base hasUniverseUnit hasSigmaUnit
  hasUniverseSigmaUnit .hasUniverseSigma.sigU _ _        = tt*
  hasUniverseSigmaUnit .hasUniverseSigma.decode-sigU _ _ = refl
