{-# OPTIONS --lossy-unification #-}
module TarskiUniverse.Instances.IterativeSets where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Data.Unit

open import Cubical.Data.IterativeSets.Base
open import Cubical.Data.IterativeSets.Sigma
open import Cubical.Data.IterativeSets.Pi
open import Cubical.Data.IterativeSets.Unit
open import Cubical.Data.IterativeSets.Identity
open import Cubical.Data.IterativeSets.Universes
open import Cubical.Data.IterativeSets.Universes.Closures

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

-- | At a successor level, V⁰ has an internal universe: the code `universe⁰`
-- of the ℓ-small iterative sets (`El⁰ universe⁰` *is* `V⁰ {ℓ}`), decoding
-- by raising.  It is closed under Π and Σ because raising commutes with
-- them (`lift-V⁰-Π⁰`, `lift-V⁰-Σ⁰`); a family over a decoded code is
-- precomposed with `liftEl⁰`, which `lowerEl⁰` undoes.
--
-- (`--lossy-unification`: without it, checking the use of `lift-V⁰-Π⁰` in
-- `decode-piU⁰` unfolds the iterativity proofs of both sides and exhausts
-- memory.)
module _ (ℓ : Level) where
  hasUniverseV : hasUniverse (BareTarskiUniverseV (ℓ-suc ℓ))
  hasUniverseV .hasUniverse.Univ   = universe⁰ {ℓ}
  hasUniverseV .hasUniverse.decode = lift-V⁰ (ℓ-suc ℓ)

  -- a family of codes over a raised code is unchanged when its argument is lowered and raised again
  liftFam-lowerEl⁰ : (c : V⁰ {ℓ}) (d : El⁰ (lift-V⁰ (ℓ-suc ℓ) c) → V⁰ {ℓ})
                   → --------------------------------------------------------------------------------
                     (λ x → lift-V⁰ (ℓ-suc ℓ) (d (liftEl⁰ (ℓ-suc ℓ) c (lowerEl⁰ (ℓ-suc ℓ) c x))))
                   ≡ (λ x → lift-V⁰ (ℓ-suc ℓ) (d x))
  liftFam-lowerEl⁰ c d = funExt λ x → cong (lift-V⁰ (ℓ-suc ℓ) ∘ d) (retEq (El⁰-lift-V⁰≃El⁰ (ℓ-suc ℓ) c) x)

  -- the small Π of a code and a family over its raising
  piU⁰ : (c : V⁰ {ℓ}) → (El⁰ (lift-V⁰ (ℓ-suc ℓ) c) → V⁰ {ℓ}) → V⁰ {ℓ}
  piU⁰ c d = Π⁰ c (λ y → d (liftEl⁰ (ℓ-suc ℓ) c y))

  -- raising the small Π gives the large Π of the raisings
  decode-piU⁰ : (c : V⁰ {ℓ}) (d : El⁰ (lift-V⁰ (ℓ-suc ℓ) c) → V⁰ {ℓ})
              → -------------------------------------------------------------------
                lift-V⁰ (ℓ-suc ℓ) (piU⁰ c d) ≡ Π⁰ (lift-V⁰ (ℓ-suc ℓ) c) (λ x → lift-V⁰ (ℓ-suc ℓ) (d x))
  decode-piU⁰ c d =
      lift-V⁰-Π⁰ (ℓ-suc ℓ) c (λ y → d (liftEl⁰ (ℓ-suc ℓ) c y))
    ∙ cong (Π⁰ (lift-V⁰ (ℓ-suc ℓ) c)) (liftFam-lowerEl⁰ c d)

  -- the small Σ of a code and a family over its raising
  sigU⁰ : (c : V⁰ {ℓ}) → (El⁰ (lift-V⁰ (ℓ-suc ℓ) c) → V⁰ {ℓ}) → V⁰ {ℓ}
  sigU⁰ c d = Σ⁰ c (λ y → d (liftEl⁰ (ℓ-suc ℓ) c y))

  -- raising the small Σ gives the large Σ of the raisings
  decode-sigU⁰ : (c : V⁰ {ℓ}) (d : El⁰ (lift-V⁰ (ℓ-suc ℓ) c) → V⁰ {ℓ})
               → -------------------------------------------------------------------
                 lift-V⁰ (ℓ-suc ℓ) (sigU⁰ c d) ≡ Σ⁰ (lift-V⁰ (ℓ-suc ℓ) c) (λ x → lift-V⁰ (ℓ-suc ℓ) (d x))
  decode-sigU⁰ c d =
      lift-V⁰-Σ⁰ (ℓ-suc ℓ) c (λ y → d (liftEl⁰ (ℓ-suc ℓ) c y))
    ∙ cong (Σ⁰ (lift-V⁰ (ℓ-suc ℓ) c)) (liftFam-lowerEl⁰ c d)

  hasUniversePiV : hasUniversePi (BareTarskiUniverseV (ℓ-suc ℓ)) hasUniverseV (hasPiV (ℓ-suc ℓ))
  hasUniversePiV .hasUniversePi.piU        = piU⁰
  hasUniversePiV .hasUniversePi.decode-piU = decode-piU⁰

  hasUniverseSigmaV : hasUniverseSigma (BareTarskiUniverseV (ℓ-suc ℓ)) hasUniverseV (hasSigmaV (ℓ-suc ℓ))
  hasUniverseSigmaV .hasUniverseSigma.sigU        = sigU⁰
  hasUniverseSigmaV .hasUniverseSigma.decode-sigU = decode-sigU⁰
