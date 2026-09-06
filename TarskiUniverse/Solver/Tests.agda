-- Tests for the `solveCode` macro.  The inductive-recursive universe is the
-- right test bed: it is the only instance providing all four structures, and
-- its `El` *computes* to Σ, Π, _≡_ and Unit*, so it also checks that the solver
-- matches the goal unreduced instead of unfolding `El`.
module TarskiUniverse.Solver.Tests where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import TarskiUniverse.Base
open import TarskiUniverse.Properties
open import TarskiUniverse.Solver
open import Utils.InductiveRecursiveUniverse hiding (El; isSetU)
open import TarskiUniverse.Instances.InductiveRecursiveUniverse

private
  variable ℓ : Level

module _ {ℓ : Level} where
  private
    TU = BareTarskiUniverseU {ℓ}
  open BareTarskiUniverse TU

  -- Unit
  _ : TU hasCodeFor Unit
  _ = solveCode hasUnitU

  -- El: must win over unfolding `El (Sig A B)` to a Σ
  _ : (A : U) → TU hasCodeFor (El A)
  _ = λ A → solveCode ε

  _ : (A : U) (B : El A → U) → TU hasCodeFor (El (Sig A B))
  _ = λ A B → solveCode ε

  -- Σ, with the binder path and two `El` leaves
  _ : (A : U) (B : El A → U) → TU hasCodeFor (Σ[ x ∈ El A ] El (B x))
  _ = λ A B → solveCode hasSigmaU

  -- Π
  _ : (A : U) (B : El A → U) → TU hasCodeFor ((x : El A) → El (B x))
  _ = λ A B → solveCode hasPiU

  -- ≡
  _ : (A : U) (a b : El A) → TU hasCodeFor (a ≡ b)
  _ = λ A a b → solveCode hasEqU

  -- Everything at once, three deep
  _ : (A : U) (B : El A → U)
    → TU hasCodeFor (Σ[ x ∈ El A ] ((y : El (B x)) → Σ[ _ ∈ Unit ] (y ≡ y)))
  _ = λ A B → solveCode (hasSigmaU {ℓ} ◂ hasPiU {ℓ} ◂ hasEqU {ℓ} ◂ hasUnitU {ℓ} ◂ ε)

-- Atom hints.  `X` is opaque, so the only way in is the hint `hX`; the Σ case
-- additionally uses it *underneath* a binder, which is what exercises `raise`.
module _ {ℓU ℓEl : Level} {U : Type ℓU} (TU : BareTarskiUniverse ℓEl U)
         (hasSigmaTU : hasSigma TU) (hasEqTU : hasEq TU)
         {ℓX : Level} {X : Type ℓX} (hX : TU hasCodeFor X)
         where

  _ : TU hasCodeFor X
  _ = solveCode hX

  _ : (a b : X) → TU hasCodeFor (a ≡ b)
  _ = λ a b → solveCode (hasEqTU ◂ hX ◂ ε)

  _ : TU hasCodeFor (Σ[ _ ∈ X ] X)
  _ = solveCode (hasSigmaTU ◂ hX ◂ ε)

  _ : TU hasCodeFor (Σ[ a ∈ X ] Σ[ b ∈ X ] (a ≡ b))
  _ = solveCode (hasSigmaTU ◂ hasEqTU ◂ hX ◂ ε)

-- A Π-shaped hint, instantiated against a concrete instance of its conclusion.
module _ {ℓU ℓEl : Level} {U : Type ℓU} (TU : BareTarskiUniverse ℓEl U)
         (hasSigmaTU : hasSigma TU)
         {ℓX : Level} {X : Type ℓX} {P : X → X → Type ℓX}
         (hX : TU hasCodeFor X) (hP : ∀ x y → TU hasCodeFor (P x y))
         where

  _ : (a : X) → TU hasCodeFor (P a a)
  _ = λ a → solveCode (hX ◂ hP ◂ ε)

  _ : TU hasCodeFor (Σ[ a ∈ X ] Σ[ b ∈ X ] P a b)
  _ = solveCode (hasSigmaTU ◂ hX ◂ hP ◂ ε)
