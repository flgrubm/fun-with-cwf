module TarskiUniverse.Instances.FinSets  where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv

open import Cubical.Data.Unit
open import Cubical.Data.SumFin
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Properties using (+-zero ; ·-identityʳ)

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

  -- | The decidable propositions form an internal universe: codes `Fin 2`,
  -- decoding to the sizes `0` and `1`.  Π and Σ over a proposition are
  -- computed by cases on it: over `0` they are `1` and `0`, over `1` they are
  -- the single fibre.
  decodeProp : Fin 2 → ℕ
  decodeProp fzero        = 0
  decodeProp (fsuc fzero) = 1

  hasUniverseℕ : hasUniverse BareTarskiUniverseℕ
  hasUniverseℕ .hasUniverse.Univ   = 2
  hasUniverseℕ .hasUniverse.decode = decodeProp

  piProp : (c : Fin 2) → (Fin (decodeProp c) → Fin 2) → Fin 2
  piProp fzero        _ = fsuc fzero
  piProp (fsuc fzero) d = d fzero

  -- `piProp` decodes to the product of the decodings
  decode-piProp : (c : Fin 2) (d : Fin (decodeProp c) → Fin 2)
                → -------------------------------------------------------------
                  decodeProp (piProp c d) ≡ totalProd (λ x → decodeProp (d x))
  decode-piProp fzero        _ = refl
  decode-piProp (fsuc fzero) d = sym (·-identityʳ (decodeProp (d fzero)))

  sigProp : (c : Fin 2) → (Fin (decodeProp c) → Fin 2) → Fin 2
  sigProp fzero        _ = fzero
  sigProp (fsuc fzero) d = d fzero

  -- `sigProp` decodes to the sum of the decodings
  decode-sigProp : (c : Fin 2) (d : Fin (decodeProp c) → Fin 2)
                 → -----------------------------------------------------------
                   decodeProp (sigProp c d) ≡ totalSum (λ x → decodeProp (d x))
  decode-sigProp fzero        _ = refl
  decode-sigProp (fsuc fzero) d = sym (+-zero (decodeProp (d fzero)))

  hasUniversePiℕ : hasUniversePi BareTarskiUniverseℕ hasUniverseℕ hasPiℕ
  hasUniversePiℕ .hasUniversePi.piU        = piProp
  hasUniversePiℕ .hasUniversePi.decode-piU = decode-piProp

  hasUniverseSigmaℕ : hasUniverseSigma BareTarskiUniverseℕ hasUniverseℕ hasSigmaℕ
  hasUniverseSigmaℕ .hasUniverseSigma.sigU        = sigProp
  hasUniverseSigmaℕ .hasUniverseSigma.decode-sigU = decode-sigProp
