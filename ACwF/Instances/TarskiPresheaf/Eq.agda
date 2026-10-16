module ACwF.Instances.TarskiPresheaf.Eq where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Functions.FunExtEquiv
open import Cubical.Data.Sigma
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import TarskiUniverse.Base
open import TarskiUniverse.Properties
open import Utils.TarskiPresheaf
open import ACwF.Base
open import ACwF.Eq
open import ACwF.Instances.TarskiPresheaf.Base

open Category
open Functor
open NatTrans

module _ {ℓob ℓhom ℓU ℓEl : Level} (C : Category ℓob ℓhom) {U : Type ℓU} (Univ : TarskiUniverse ℓEl U)  where
  open TarskiUniverse Univ
  open Algebraic (PRESHEAFU C TU)
  open CwF (Psh-CwF C Univ)

  module _ (hasEqTU : hasEq TU) where
    open hasEq hasEqTU
    private
      ttU = isContrElUnit .fst
      isPropElEq : ∀ A a b → isProp (El (Eq A a b))
      isPropElEq A a b = isOfHLevelRetractFromIso 1 (EqIso A a b) (isSetEl A a b)

    Psh-EqTy : {Γ : Ctx} (A : Ty Γ) → Tm Γ A → Tm Γ A → Ty Γ
    Psh-EqTy A a b .F-ob ρ    = Eq (A .F-ob ρ) (a .N-ob ρ ttU) (b .N-ob ρ ttU)
    Psh-EqTy A a b .F-hom f e = eqIntro
      (funExt⁻ (a .N-hom f) ttU
      ∙∙ cong (A .F-hom f) (eqElim e)
      ∙∙ sym (funExt⁻ (b .N-hom f) ttU))
    Psh-EqTy A a b .F-id      = funExt λ _ → isPropElEq _ _ _ _ _
    Psh-EqTy A a b .F-seq _ _ = funExt λ _ → isPropElEq _ _ _ _ _

    Psh-Eq-structure : Eq-Structure (Psh-CwF C Univ)
    Psh-Eq-structure .Eq-Structure.EqTy                               = Psh-EqTy
    Psh-Eq-structure .Eq-Structure.EqTyNat _ _ _ _                    = Functor≡ (λ _ → refl) (λ _ → refl)
    Psh-Eq-structure .Eq-Structure.EqTmIso A a b .Iso.fun M           = makeNatTransPath (funExt λ ρ → funExt λ u →
      cong (a .N-ob ρ) (sym (isContrElUnit .snd u))
      ∙∙ eqElim (M .N-ob ρ ttU)
      ∙∙ cong (b .N-ob ρ) (isContrElUnit .snd u))
    Psh-Eq-structure .Eq-Structure.EqTmIso A a b .Iso.inv p .N-ob ρ _ = eqIntro (λ i → p i .N-ob ρ ttU)
    Psh-Eq-structure .Eq-Structure.EqTmIso A a b .Iso.inv p .N-hom _  = funExt λ _ → isPropElEq _ _ _ _ _
    Psh-Eq-structure .Eq-Structure.EqTmIso A a b .Iso.sec _           = isSetNatTrans _ _ _ _
    Psh-Eq-structure .Eq-Structure.EqTmIso A a b .Iso.ret _           =
      makeNatTransPath (funExt λ _ → funExt λ _ → isPropElEq _ _ _ _ _)
    Psh-Eq-structure .Eq-Structure.EqTmIsoInvNat _ _ _ _ _            =
      makeNatTransPathP refl _ (funExt λ _ → funExt λ _ → isPropElEq _ _ _ _ _)
