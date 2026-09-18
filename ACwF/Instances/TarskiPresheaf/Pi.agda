{-# OPTIONS --lossy-unification #-}
module ACwF.Instances.TarskiPresheaf.Pi where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Functions.FunExtEquiv
open import Cubical.Data.Sigma
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import TarskiUniverse.Base
open import TarskiUniverse.Properties
open import Utils.TarskiPresheaf
open import ACwF.Base
open import ACwF.Pi
open import TarskiUniverse.Solver
open import Utils.InternalCategory
open import ACwF.Instances.TarskiPresheaf.Base
open import ACwF.Instances.TarskiPresheaf.Pi.Nat

open Category
open Functor
open NatTrans

module _ {ℓob ℓhom ℓU ℓEl : Level} (C : Category ℓob ℓhom) {U : Type ℓU} (Univ : TarskiUniverse ℓEl U) where
  open TarskiUniverse Univ
  open Algebraic (PRESHEAFU C TU)
  open CwF (Psh-CwF C Univ)

  open [_]CodedCategory
  module _ (hasPiTU : hasPi TU) (hasEqTU : hasEq TU) (coded : [ TU ]CodedCategory C) where
    -- Definitions, Restrict and Nat, with this module's parameters applied.
    open PiNat C Univ hasPiTU hasEqTU coded

    Psh-Π-structure : Π-Structure _ (Psh-CwF C Univ)
    -- Restrict.agda builds ΠTy as a functor and Nat.agda proves ΠTyNat clause by
    -- clause: ΠTyNat-ob is exactly Functor≡'s F-ob argument and ΠTyNat-hom exactly
    -- its F-hom argument, so both fields here are pure assembly.
    Psh-Π-structure .Π-Structure.ΠTy = ΠTy
    Psh-Π-structure .Π-Structure.ΠTyNat A B σ =
      Functor≡ (ΠTyNat-ob A B σ) (ΠTyNat-hom A B σ)
    Psh-Π-structure .Π-Structure.ΠTmIso = {!!}
    Psh-Π-structure .Π-Structure.ΠTmIsoInvNat = {!!}
