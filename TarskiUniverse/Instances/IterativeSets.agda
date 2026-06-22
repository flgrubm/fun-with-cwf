module TarskiUniverse.Instances.IterativeSets  where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Unit

open import Cubical.Data.IterativeSets.Base
open import Cubical.Data.IterativeSets.Sigma
open import Cubical.Data.IterativeSets.Pi
open import Cubical.Data.IterativeSets.Unit

open import TarskiUniverse.Base

open TarskiUniverse

module _ (ℓ : Level) where
  V-TarskiUniverse : TarskiUniverse (ℓ-suc ℓ) ℓ
  V-TarskiUniverse .U                   = V⁰ {ℓ}
  V-TarskiUniverse .isSetU              = isSetV⁰
  V-TarskiUniverse .El                  = El⁰
  V-TarskiUniverse .isSetEl             = isSetEl⁰
  V-TarskiUniverse .TarskiUniverse.Unit = unit⁰
  V-TarskiUniverse .isContrElUnit       = subst isContr (sym El⁰unit⁰IsUnit*) isContrUnit*
  V-TarskiUniverse .Sig                 = Σ⁰
  V-TarskiUniverse .SigIso _ _          = idIso
  V-TarskiUniverse .Pi                  = Π⁰
  V-TarskiUniverse .PiIso _ _           = idIso
