module ACwF.Instances.TarskiPresheaf.Unit where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Functions.FunExtEquiv
open import Cubical.Data.Sigma
open import Cubical.Data.Unit using (tt)
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import TarskiUniverse.Base
open import TarskiUniverse.Properties
open import Utils.TarskiPresheaf
open import ACwF.Base
open import ACwF.Unit
open import ACwF.Instances.TarskiPresheaf.Base

open Category
open Functor
open NatTrans

module _ {ℓob ℓhom ℓU ℓEl : Level} (C : Category ℓob ℓhom) {U : Type ℓU} (Univ : TarskiUniverse ℓEl U) where
  open TarskiUniverse Univ
  open Algebraic (PRESHEAFU C TU)
  open CwF (Psh-CwF C Univ)

  Psh-Unit-structure : Unit-Structure (Psh-CwF C Univ)
  Psh-Unit-structure .Unit-Structure.UnitTy                         = Psh-UnitType C Univ
  Psh-Unit-structure .Unit-Structure.UnitTyNat _                    = Functor≡ (λ _ → refl) (λ _ → refl)
  Psh-Unit-structure .Unit-Structure.UnitTmIso .Iso.fun _           = tt
  Psh-Unit-structure .Unit-Structure.UnitTmIso .Iso.inv _ .N-ob _ _ = isContrElUnit .fst
  Psh-Unit-structure .Unit-Structure.UnitTmIso .Iso.inv _ .N-hom _  = refl
  Psh-Unit-structure .Unit-Structure.UnitTmIso .Iso.sec _           = refl
  Psh-Unit-structure .Unit-Structure.UnitTmIso .Iso.ret a           =
    makeNatTransPath (funExt λ _ → funExt λ x → isContrElUnit .snd (a .N-ob _ x))
  Psh-Unit-structure .Unit-Structure.UnitTmIsoInvNat _ _            = makeNatTransPathP refl _ refl
