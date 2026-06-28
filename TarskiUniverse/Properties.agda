module TarskiUniverse.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Limits

open import TarskiUniverse.Base

open Functor
open Cone
open LimCone

module _ {ℓU ℓEl : Level} (TU : TarskiUniverse-Base ℓU ℓEl) where

  open Category
  open TarskiUniverse-Base TU

  UCat : Category ℓU ℓEl
  UCat .ob = U
  UCat .Hom[_,_] Δ Γ = El Δ → El Γ
  UCat .id x = x
  UCat ._⋆_ f g x = g (f x)
  UCat .⋆IdL _ = refl
  UCat .⋆IdR _ = refl
  UCat .⋆Assoc _ _ _ = refl
  UCat .isSetHom {y = y} = isSet→ (isSetEl y)

  -- An internal category: a category whose object- and morphism-types are
  -- given by codes (so they live in `U`/`El`), rather than arbitrary types.
  record InternalCategory : Type (ℓ-max ℓU ℓEl) where
    field
      Obᵢ  : U
      Homᵢ : El Obᵢ → El Obᵢ → U
      idᵢ  : (x : El Obᵢ) → El (Homᵢ x x)
      _⋆ᵢ_ : {x y z : El Obᵢ} → El (Homᵢ x y) → El (Homᵢ y z) → El (Homᵢ x z)
      ⋆IdLᵢ   : {x y : El Obᵢ} (f : El (Homᵢ x y)) → idᵢ x ⋆ᵢ f ≡ f
      ⋆IdRᵢ   : {x y : El Obᵢ} (f : El (Homᵢ x y)) → f ⋆ᵢ idᵢ y ≡ f
      ⋆Assocᵢ : {x y z w : El Obᵢ} (f : El (Homᵢ x y)) (g : El (Homᵢ y z)) (h : El (Homᵢ z w))
              → (f ⋆ᵢ g) ⋆ᵢ h ≡ f ⋆ᵢ (g ⋆ᵢ h)

  open InternalCategory

  -- Internal categories are actually categories
  ⟦_⟧Cat : InternalCategory → Category ℓEl ℓEl
  ⟦ D ⟧Cat .ob          = El (D .Obᵢ)
  ⟦ D ⟧Cat .Hom[_,_] x y = El (D .Homᵢ x y)
  ⟦ D ⟧Cat .id {x}      = D .idᵢ x
  ⟦ D ⟧Cat ._⋆_         = D ._⋆ᵢ_
  ⟦ D ⟧Cat .⋆IdL        = D .⋆IdLᵢ
  ⟦ D ⟧Cat .⋆IdR        = D .⋆IdRᵢ
  ⟦ D ⟧Cat .⋆Assoc      = D .⋆Assocᵢ
  ⟦ D ⟧Cat .isSetHom    = isSetEl _

  -- a Tarski universe can be closed under limits of internal diagrams
  record TarskiUniverse-Limit : Type (ℓ-max ℓU ℓEl) where
    field
      Limit : {D : InternalCategory} (J : Functor ⟦ D ⟧Cat UCat) → U
      LimitIso : {D : InternalCategory} (J : Functor ⟦ D ⟧Cat UCat) →
        Iso
          (El (Limit {D} J))
          (Σ
            ((d : El (D .Obᵢ)) → El (J ⟅ d ⟆))
              λ s → {x y : El (D .Obᵢ)} (m : El (D .Homᵢ x y)) → J .F-hom m (s x) ≡ s y)

  -- The limits in the Tarski universe are limits in actual categories
  module _ (TL : TarskiUniverse-Limit) {D : InternalCategory}
           (Dgm : Functor ⟦ D ⟧Cat UCat) where

    open TarskiUniverse-Limit TL

    private
      L : U
      L = Limit {D} Dgm

      ConeT : Type ℓEl
      ConeT = Σ[ s ∈ ((d : El (D .Obᵢ)) → El (Dgm ⟅ d ⟆)) ]
                ({x y : El (D .Obᵢ)} (m : El (D .Homᵢ x y)) → Dgm .F-hom m (s x) ≡ s y)

      limIso : Iso (El L) ConeT
      limIso = LimitIso {D} Dgm

    theCone : Cone Dgm L
    theCone .coneOut v l               = Iso.fun limIso l .fst v
    theCone .coneOutCommutes {u} {v} e = funExt λ l → Iso.fun limIso l .snd {u} {v} e

    theConeIsLimiting : isLimCone Dgm L theCone
    theConeIsLimiting c cc = (f , fConeMor) , uniq
      where
        cn : El c → ConeT
        cn x = (λ d → cc .coneOut d x)
             , λ {u} {v} e → funExt⁻ (cc .coneOutCommutes {u} {v} e) x

        f : El c → El L
        f x = Iso.inv limIso (cn x)

        fConeMor : isConeMor cc theCone f
        fConeMor v = funExt λ x → cong (λ p → p .fst v) (Iso.sec limIso (cn x))

        uniq : (gp : Σ[ g ∈ (El c → El L) ] isConeMor cc theCone g)
             → (f , fConeMor) ≡ gp
        uniq (g , gConeMor) =
          Σ≡Prop (λ h → isPropIsConeMor cc theCone h)
                 (funExt λ x → isoFunInjective limIso (f x) (g x)
                   (Σ≡Prop (λ s → isPropImplicitΠ2 λ _ y → isPropΠ λ m → isSetEl (Dgm ⟅ y ⟆) _ _)
                           (funExt λ v →
                              cong (λ p → p .fst v) (Iso.sec limIso (cn x))
                            ∙ sym (funExt⁻ (gConeMor v) x))))

    LimitLimCone : LimCone Dgm
    LimitLimCone .lim      = L
    LimitLimCone .limCone  = theCone
    LimitLimCone .univProp = theConeIsLimiting

module _ {ℓU ℓEl : Level} (TU : TarskiUniverse ℓU ℓEl) where

  open Category
  open TarskiUniverse TU

  SigPathP : ∀ {A} {B} → {x y : El (Sig A B)} → (fst≡ : fstSig x ≡ fstSig y) → PathP (λ i → El (B (fst≡ i))) (sndSig x) (sndSig y) → x ≡ y
  SigPathP {x = x} {y = y} fst≡ snd≡ = sym (ηSig x) ∙ cong (uncurry pairSig) (ΣPathP (fst≡ , snd≡)) ∙ ηSig y
    where
      open import Cubical.Foundations.Function
      open import Cubical.Data.Sigma
