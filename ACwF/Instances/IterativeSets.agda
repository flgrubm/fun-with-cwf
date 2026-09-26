{-# OPTIONS --lossy-unification #-}
module ACwF.Instances.IterativeSets  where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Functions.FunExtEquiv

open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.Bool

open import Cubical.Categories.Category

open import ACwF.Base
open import ACwF.Sigma
open import ACwF.Pi
open import ACwF.Eq
open import ACwF.Empty
open import ACwF.Unit
open import ACwF.Bool

open import Cubical.Data.IterativeSets.Base renaming (V⁰ to V ; El⁰ to El ; isSetEl⁰ to isSetEl)
open import Utils.VCat
open import Cubical.Data.IterativeSets.Sigma
open import Cubical.Data.IterativeSets.Pi
open import Cubical.Data.IterativeSets.Unit
open import Cubical.Data.IterativeSets.Identity
open import Cubical.Data.IterativeSets.Empty
open import Cubical.Data.IterativeSets.Bool

open Category

module _ {ℓ : Level} where

  open Algebraic
  open CwF
  open Iso

  VCwF : CwF (VCat _) (ℓ-suc ℓ) ℓ
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

  V-Σ-Structure : Σ-Structure (VCat _) VCwF
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

  V-Π-Structure : Π-Structure {ℓHom = ℓHom} (VCat _) VCwF
  V-Π-Structure .ΠTy {Γ = Γ} A B x    = Π⁰ (A x) λ y → B (x , y)

  V-Π-Structure .ΠTyNat _ _ _         = refl
  V-Π-Structure .ΠTmIso _ _           = invIso curryIso
  V-Π-Structure .ΠTmIsoInvNat _ _ _ _ = refl

module _ {ℓHom : Level} where

  open Algebraic
  open CwF {ℓHom = ℓHom} VCwF

  open Eq-Structure

  V-Eq-Structure : Eq-Structure {ℓHom = ℓHom} VCwF
  V-Eq-Structure .EqTy A a b x            = Id⁰ (A x) (a x) (b x)
  V-Eq-Structure .EqTyNat _ _ _ _         = refl
  V-Eq-Structure .EqTmIso _ _ _           = funExtIso
  V-Eq-Structure .EqTmIsoInvNat _ _ _ _ _ = refl

  V-⊥-Structure : ⊥-Structure {ℓHom = ℓHom} VCwF
  V-⊥-Structure .⊥-Structure.⊥Ty _         = empty⁰
  V-⊥-Structure .⊥-Structure.⊥TyNat _      = refl
  V-⊥-Structure .⊥-Structure.⊥-elim A (_ , lift ())
  V-⊥-Structure .⊥-Structure.⊥-elimNat A σ = funExt λ { (_ , lift ()) }

  V-Unit-Structure : Unit-Structure {ℓHom = ℓHom} VCwF
  V-Unit-Structure .Unit-Structure.UnitTy _               = unit⁰
  V-Unit-Structure .Unit-Structure.UnitTyNat _            = refl
  V-Unit-Structure .Unit-Structure.UnitTmIso .Iso.fun _   = tt
  V-Unit-Structure .Unit-Structure.UnitTmIso .Iso.inv _ _ = tt*
  V-Unit-Structure .Unit-Structure.UnitTmIso .Iso.sec tt  = refl
  V-Unit-Structure .Unit-Structure.UnitTmIso .Iso.ret _   = funExt (λ _ → refl)
  V-Unit-Structure .Unit-Structure.UnitTmIsoInvNat t σ    = refl

  private
    V-Bool-elim : ∀ {Γ} A
      → Tm Γ (A [ ⟨ (λ _ → true*) ⟩ ]Ty) × Tm Γ (A [ ⟨ (λ _ → false*) ⟩ ]Ty)
      → Tm (Γ ▹ (λ _ → bool⁰)) A
    V-Bool-elim _ (_ , af) (x , lift false) = af x
    V-Bool-elim _ (at , _) (x , lift true)  = at x

    V-Bool-elimβ : ∀ {Γ} A tf
      → (V-Bool-elim {Γ} A tf [ ⟨ (λ _ → true*) ⟩ ]Tm , V-Bool-elim A tf [ ⟨ (λ _ → false*) ⟩ ]Tm) ≡ tf
    V-Bool-elimβ _ _ = refl

    V-Bool-elimNat : ∀ {Δ Γ} A (σ : El Δ → El Γ) tf
      → let σ↑ = subst (λ X → El (Σ⁰ Δ X) → El (Σ⁰ Γ (λ _ → bool⁰))) refl (σ ⁺) in
          V-Bool-elim (A [ σ↑ ]Ty)
            ( V-Bool-elim A tf [ σ↑ ]Tm [ ⟨ (λ _ → true*) ⟩ ]Tm
            , V-Bool-elim A tf [ σ↑ ]Tm [ ⟨ (λ _ → false*) ⟩ ]Tm)
        ≡ V-Bool-elim A tf [ σ↑ ]Tm
    V-Bool-elimNat _ _ _ = funExt λ { (_ , lift false) → refl
                                    ; (_ , lift true)  → refl }

  V-Bool-Structure : Bool-Structure {ℓHom = ℓHom} VCwF
  V-Bool-Structure .Bool-Structure.BoolTy _       = bool⁰
  V-Bool-Structure .Bool-Structure.BoolTyNat _    = refl
  V-Bool-Structure .Bool-Structure.Btrue _        = true*
  V-Bool-Structure .Bool-Structure.Bfalse _       = false*
  V-Bool-Structure .Bool-Structure.BtrueNat       = refl
  V-Bool-Structure .Bool-Structure.BfalseNat      = refl
  V-Bool-Structure .Bool-Structure.Bool-elim      = V-Bool-elim
  V-Bool-Structure .Bool-Structure.Bool-elimβ     = V-Bool-elimβ
  V-Bool-Structure .Bool-Structure.Bool-elimNat   = V-Bool-elimNat
