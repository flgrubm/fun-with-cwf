module TarskiUniverse.Instances.Unit  where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Unit

open import TarskiUniverse.Base

open TarskiUniverse-Base

module _ (ℓ : Level) where
  Unit-TarskiUniverse-Base : TarskiUniverse-Base (ℓ-suc ℓ) ℓ
  Unit-TarskiUniverse-Base .U = Unit*
  Unit-TarskiUniverse-Base .isSetU = isSetUnit*
  Unit-TarskiUniverse-Base .El x = Unit*
  Unit-TarskiUniverse-Base .isSetEl _ = isSetUnit*

  Unit-TarskiUniverse-Sig : TarskiUniverse-Sig Unit-TarskiUniverse-Base
  Unit-TarskiUniverse-Sig .TarskiUniverse-Sig.Sig A x = tt*
  Unit-TarskiUniverse-Sig .TarskiUniverse-Sig.SigIso _ _ .Iso.fun x = tt* , tt*
  Unit-TarskiUniverse-Sig .TarskiUniverse-Sig.SigIso _ _ .Iso.inv x = tt*
  Unit-TarskiUniverse-Sig .TarskiUniverse-Sig.SigIso _ _ .Iso.sec (tt* , tt*) = refl
  Unit-TarskiUniverse-Sig .TarskiUniverse-Sig.SigIso _ _ .Iso.ret tt* = refl

  Unit-TarskiUniverse-Unit : TarskiUniverse-Unit Unit-TarskiUniverse-Base
  Unit-TarskiUniverse-Unit .TarskiUniverse-Unit.Unit          = tt*
  Unit-TarskiUniverse-Unit .TarskiUniverse-Unit.isContrElUnit = isContrUnit*

  Unit-TarskiUniverse : TarskiUniverse (ℓ-suc ℓ) ℓ
  Unit-TarskiUniverse .TarskiUniverse.TU-Base = Unit-TarskiUniverse-Base
  Unit-TarskiUniverse .TarskiUniverse.TU-Unit = Unit-TarskiUniverse-Unit
  Unit-TarskiUniverse .TarskiUniverse.TU-Sig = Unit-TarskiUniverse-Sig

  Unit-TarskiUniverse-Pi : TarskiUniverse-Pi Unit-TarskiUniverse-Base
  Unit-TarskiUniverse-Pi .TarskiUniverse-Pi.Pi A B = tt*
  Unit-TarskiUniverse-Pi .TarskiUniverse-Pi.PiIso _ _ .Iso.fun _ _ = tt*
  Unit-TarskiUniverse-Pi .TarskiUniverse-Pi.PiIso _ _ .Iso.inv _ = tt*
  Unit-TarskiUniverse-Pi .TarskiUniverse-Pi.PiIso _ _ .Iso.sec _ _ _ = tt*
  Unit-TarskiUniverse-Pi .TarskiUniverse-Pi.PiIso _ _ .Iso.ret tt* = refl

