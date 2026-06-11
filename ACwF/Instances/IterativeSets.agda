{-# OPTIONS --lossy-unification #-}
module ACwF.Instances.IterativeSets  where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Categories.Category

open import ACwF.Base
open import ACwF.Sigma
open import ACwF.Pi

open import Cubical.Data.IterativeSets.Base renaming (V⁰ to V ; El⁰ to El ; isSetEl⁰ to isSetEl)
open import Utils.VCat
open import Cubical.Data.IterativeSets.Sigma
open import Cubical.Data.IterativeSets.Pi
open import Cubical.Data.IterativeSets.Unit

open Category

module _ {ℓ : Level} where

  open Algebraic
  open CwF
  open Iso

  VCwF : CwF VCat (ℓ-suc ℓ) ℓ
  VCwF .⟨⟩                = unit⁰ , λ _ → (λ _ → lift tt) , λ _ _ _ → lift tt
  VCwF .Ty Γ              = El Γ → V {ℓ}
  VCwF .isSetTy Γ         = isSet→ isSetV⁰
  VCwF ._[_]Ty A σ x      = A (σ x)
  VCwF .[id]Ty _          = refl
  VCwF .[][]Ty _ _ _      = refl
  VCwF .Tm Γ A            = (x : El Γ) → El (A x)
  VCwF .isSetTm Γ A       = isSetΠ (λ _ → isSetEl _)
  VCwF ._[_]Tm a σ x      = a (σ x)
  VCwF .[id]Tm _          = refl
  VCwF .[][]Tm _ _ _      = refl
  VCwF ._▹_               = Σ⁰
  VCwF .p                 = fst
  VCwF .q                 = snd
  VCwF ._⁺ σ (x , _) .fst = σ x
  VCwF ._⁺ _ (_ , y) .snd = y
  VCwF .⟨_⟩ _ x .fst      = x
  VCwF .⟨_⟩ a x .snd      = a x
  VCwF .⟨⟩∘ a σ           = refl
  VCwF .p⁺∘⟨q⟩≡id         = refl
  VCwF .∘⁺ σ' σ           = refl
  VCwF .id⁺               = refl
  VCwF .p∘⁺ σ             = refl
  VCwF .[p][⁺]Ty B σ      = refl
  VCwF .q[⁺]Tm σ          = refl
  VCwF .p∘⟨⟩≡id a         = refl
  VCwF .[p][⟨⟩]Ty B a     = refl
  VCwF .q[⟨⟩]Tm a         = refl

module _ {ℓHom : Level} where

  open Algebraic
  open CwF {ℓHom = ℓHom} VCwF

  open Σ-Structure

  V-Σ-Structure : Σ-Structure VCat VCwF
  V-Σ-Structure .ΣTy A B x              = Σ⁰ (A x) (λ y → B (x , y))
  V-Σ-Structure .ΣTyNat A B σ           = refl
  V-Σ-Structure .ΣTmIso A B             = Σ-Π-Iso
  V-Σ-Structure .coerce A B a σ         = refl
  V-Σ-Structure .ΣTmIsoInvNat _ _ _ b σ =
    funExt λ x → ΣPathP (refl , sym (funExt⁻ (substRefl {B = Tm _} _) _))

module _ {ℓHom : Level} where

  open Algebraic
  open CwF {ℓHom = ℓHom} VCwF

  open Π-Structure

  V-Π-Structure : Π-Structure {ℓHom = ℓHom} VCat VCwF
  V-Π-Structure .ΠTy {Γ = Γ} A B x    = Π⁰ (A x) λ y → B (x , y)
  V-Π-Structure .ΠTyNat _ _ _         = refl
  V-Π-Structure .ΠTmIso _ _           = invIso curryIso
  V-Π-Structure .ΠTmIsoInvNat _ _ _ _ = refl
