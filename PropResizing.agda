open import Cubical.Foundations.Prelude
open import Cubical.HITs.Replacement
open import Cubical.HITs.SetQuotients
open import Cubical.Data.Unit
open import Cubical.Data.Bool
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Displayed.Base
open import Cubical.Functions.Image

open import Cubical.Relation.Binary
open BinaryRelation
open isEquivRel

module PropResizing where

is-[_]-small : (ℓ : Level) {ℓ' : Level} → (A : Type ℓ') → Type (ℓ-max (ℓ-suc ℓ) ℓ')
is-[ ℓ ]-small A = Σ[ B ∈ Type ℓ ] (B ≃ A)

is-locally-[_]-small : (ℓ : Level) {ℓ' : Level} → (A : Type ℓ') → Type (ℓ-max (ℓ-suc ℓ) ℓ')
is-locally-[ ℓ ]-small A = (x y : A) → is-[ ℓ ]-small (x ≡ y)

module CheckReplacement
  {ℓA ℓB : Level}
  (A : Type ℓA) (B : Type ℓB)
  (lsB : is-locally-[ ℓA ]-small B)
  (F : A → B)
  where
  UARelF : UARel B ℓA
  UARelF .UARel._≅_ x y = (Σ[ a ∈ A ] lsB (F a) x .fst) ≃ (Σ[ a ∈ A ] lsB (F a) y .fst)
  UARelF .UARel.ua x y = compEquiv {!!} {!!}
  
  Replacement' : is-[ ℓA ]-small (Image F)
  Replacement' .fst = Replacement UARelF F
  Replacement' .snd = replacement≃Image UARelF F


module NiceQuotient {ℓ : Level} (X : Type ℓ-zero) {setX : isSet X}
                                (R : X → X → Type ℓ) {propR : (a b : X) → isProp (R a b)}
                                {eqRelR : isEquivRel R}
  where
  -- TODO: insert proof (already done)
  helper : (a b : X) → (R a ≡ R b) ≃ R a b
  helper = {!!}

  
  
  _/ᴺ_ : Type ℓ-zero
  _/ᴺ_ = Replacement h2 R
    where
      h2 : UARel (X → Type ℓ) ℓ-zero
      h2 .UARel._≅_ = {!!}
      h2 .UARel.ua = {!!}



module _ {ℓ : Level} (X : Type ℓ) (propX : isProp X) where
  R : Bool → Bool → Type ℓ
  R false false = Unit*
  R false true = X
  R true false = X
  R true true = Unit*

  isPropR : (a b : Bool) → isProp (R a b)
  isPropR false false = isPropUnit*
  isPropR false true = propX
  isPropR true false = propX
  isPropR true true = isPropUnit*

  2/R' : Type ℓ
  2/R' = Bool / R

  2/R : Type ℓ-zero
  2/R = {!!}

  propResizing : is-[ ℓ-zero ]-small X
  propResizing = {!!}

