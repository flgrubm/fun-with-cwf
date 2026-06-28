module TarskiUniverse.Instances.IterativeSets  where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Unit

open import Cubical.Categories.Functor

open import Cubical.Data.IterativeSets.Base
open import Cubical.Data.IterativeSets.Sigma
open import Cubical.Data.IterativeSets.Pi
open import Cubical.Data.IterativeSets.Unit

open import IterativeSets.Limits

open import TarskiUniverse.Base
open import TarskiUniverse.Properties

open TarskiUniverse-Base
open Functor

module _ (ℓ : Level) where
  V-TarskiUniverse-Base : TarskiUniverse-Base (ℓ-suc ℓ) ℓ
  V-TarskiUniverse-Base .U                   = V⁰ {ℓ}
  V-TarskiUniverse-Base .isSetU              = isSetV⁰
  V-TarskiUniverse-Base .El                  = El⁰
  V-TarskiUniverse-Base .isSetEl             = isSetEl⁰

  V-TarskiUniverse-Unit : TarskiUniverse-Unit V-TarskiUniverse-Base
  V-TarskiUniverse-Unit .TarskiUniverse-Unit.Unit          = unit⁰
  V-TarskiUniverse-Unit .TarskiUniverse-Unit.isContrElUnit = subst isContr (sym El⁰unit⁰IsUnit*) isContrUnit*

  V-TarskiUniverse-Sig : TarskiUniverse-Sig V-TarskiUniverse-Base
  V-TarskiUniverse-Sig .TarskiUniverse-Sig.Sig                 = Σ⁰
  V-TarskiUniverse-Sig .TarskiUniverse-Sig.SigIso _ _          = idIso

  V-TarskiUniverse : TarskiUniverse (ℓ-suc ℓ) ℓ
  V-TarskiUniverse .TarskiUniverse.TU-Base = V-TarskiUniverse-Base
  V-TarskiUniverse .TarskiUniverse.TU-Unit = V-TarskiUniverse-Unit
  V-TarskiUniverse .TarskiUniverse.TU-Sig = V-TarskiUniverse-Sig

  V-TarskiUniverse-Pi : TarskiUniverse-Pi V-TarskiUniverse-Base
  V-TarskiUniverse-Pi .TarskiUniverse-Pi.Pi                  = Π⁰
  V-TarskiUniverse-Pi .TarskiUniverse-Pi.PiIso _ _           = idIso

  V-TarskiUniverse-Limit : TarskiUniverse-Limit V-TarskiUniverse-Base
  V-TarskiUniverse-Limit .TarskiUniverse-Limit.Limit {D} J =
    limit⁰ (InternalCategory.Obᵢ D) (InternalCategory.Homᵢ D) (λ d → J ⟅ d ⟆) (J .F-hom)
  V-TarskiUniverse-Limit .TarskiUniverse-Limit.LimitIso {D} J =
    Iso-El⁰-limit⁰-Cone (InternalCategory.Obᵢ D) (InternalCategory.Homᵢ D) (λ d → J ⟅ d ⟆) (J .F-hom)
