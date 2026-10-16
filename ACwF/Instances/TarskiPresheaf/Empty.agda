module ACwF.Instances.TarskiPresheaf.Empty where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Functions.FunExtEquiv
open import Cubical.Data.Sigma
open import Cubical.Data.Empty as ⊥ using (⊥)
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Functors.Constant
open import Cubical.Categories.NaturalTransformation
open import TarskiUniverse.Base
open import TarskiUniverse.Properties
open import Utils.TarskiPresheaf
open import ACwF.Base
open import ACwF.Empty
open import ACwF.Instances.TarskiPresheaf.Base

open Category
open Functor
open NatTrans

module _ {ℓob ℓhom ℓU ℓEl : Level} (C : Category ℓob ℓhom) {U : Type ℓU} (Univ : TarskiUniverse ℓEl U)  where
  open TarskiUniverse Univ
  open Algebraic (PRESHEAFU C TU)
  open CwF (Psh-CwF C Univ)

  module _ (hasEmptyTU : hasEmpty TU) where
    open hasEmpty hasEmptyTU

    Psh-⊥-structure : ⊥-Structure (Psh-CwF C Univ)
    Psh-⊥-structure .⊥-Structure.⊥Ty                       = Constant _ _ Empty
    Psh-⊥-structure .⊥-Structure.⊥TyNat σ                  = Functor≡ (λ _ → refl) (λ _ → refl)
    Psh-⊥-structure .⊥-Structure.⊥-elim _ .N-ob (_ , x) _  = ⊥.rec (EmptyIso .Iso.fun (sndSigma x))
    Psh-⊥-structure .⊥-Structure.⊥-elim _ .N-hom {_ , x} _ = ⊥.rec (EmptyIso .Iso.fun (sndSigma x))
    Psh-⊥-structure .⊥-Structure.⊥-elimNat _ _             =
      makeNatTransPath (funExt λ (_ , x) → ⊥.rec (EmptyIso .Iso.fun (sndSigma x)))
