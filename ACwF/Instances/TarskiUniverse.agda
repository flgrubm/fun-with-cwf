module ACwF.Instances.TarskiUniverse where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Function
open import Cubical.Data.Sigma

open import Cubical.Categories.Category

open import ACwF.Base
open import ACwF.Sigma
open import ACwF.Pi

open import TarskiUniverse.Base
open import TarskiUniverse.Properties

open import Agda.Builtin.Unit

open Iso
open Category

module _ {ℓU ℓEl : Level} (TU : TarskiUniverse ℓU ℓEl) where

  open Algebraic
  open TarskiUniverse TU

  module _ where
    open CwF

    UCwF : CwF (UCat TU) (ℓ-max ℓU ℓEl) ℓEl
    UCwF .⟨⟩ .fst          = Unit
    UCwF .⟨⟩ .snd _ .fst _ = isContrElUnit .fst
    UCwF .⟨⟩ .snd Γ .snd σ = funExt (λ x → isContrElUnit .snd (σ x))
    UCwF .Ty Γ             = El Γ → U
    UCwF .isSetTy Γ        = isSet→ isSetU
    UCwF ._[_]Ty A σ x     = A (σ x)
    UCwF .[id]Ty _         = refl
    UCwF .[][]Ty _ _ _     = refl
    UCwF .Tm Γ A           = (x : El Γ) → El (A x)
    UCwF .isSetTm _ A      = isSetΠ (λ x → isSetEl (A x))
    UCwF ._[_]Tm a σ x     = a (σ x)
    UCwF .[id]Tm _         = refl
    UCwF .[][]Tm _ _ _     = refl
    UCwF ._▹_              = Sig
    UCwF .p                = fstSig
    UCwF .q                = sndSig
    UCwF ._⁺ σ s           = pairSig (σ (fstSig s)) (sndSig s)
    UCwF .⟨_⟩ a x          = pairSig x (a x)
    UCwF .⟨⟩∘ a σ          = funExt (λ x → cong₂ pairSig (sym (cong σ (fstPairSig x (a (σ x))))) (symP (sndPairSig x (a (σ x)))))
    UCwF .p⁺∘⟨q⟩≡id        = funExt λ x → cong₂ pairSig (cong fstSig (fstPairSig _ _)) (sndPairSig _ _) ∙ ηSig _
    UCwF .∘⁺ σ τ           = funExt λ x → cong₂ pairSig (cong τ (sym (fstPairSig _ _))) (symP (sndPairSig _ _))
    UCwF .id⁺              = funExt λ x → ηSig _
    UCwF .p∘⁺ σ            = funExt λ x → fstPairSig _ _
    UCwF .[p][⁺]Ty B σ     = funExt λ x → cong B (fstPairSig _ _)
    UCwF .q[⁺]Tm σ         = funExt λ x → sndPairSig _ _
    UCwF .p∘⟨⟩≡id a        = funExt λ x → fstPairSig _ _
    UCwF .[p][⟨⟩]Ty B a    = funExt λ x → cong B (fstPairSig _ _)
    UCwF .q[⟨⟩]Tm a        = funExt λ x → sndPairSig _ _

  module U-Σ
    where

    open Algebraic
    open CwF UCwF

    U-Σ-Structure : Σ-Structure (UCat TU) UCwF
    U-Σ-Structure .Σ-Structure.ΣTy A B x                      = Sig (A x) λ y → B (pairSig x y)
    U-Σ-Structure .Σ-Structure.ΣTyNat A B σ                   = funExt λ x → cong (Sig (A (σ x))) (funExt λ y → cong B (cong₂ pairSig (cong σ (sym (fstPairSig _ _))) (symP (sndPairSig _ _))))
    U-Σ-Structure .Σ-Structure.ΣTmIso A B                     = compIso (codomainIsoDep (λ _ → SigIso _ _)) Σ-Π-Iso
    U-Σ-Structure .Σ-Structure.coerce A B a σ                 = funExt λ x → cong B (cong₂ pairSig (cong σ (sym (fstPairSig _ _))) (symP (sndPairSig _ _)))
    U-Σ-Structure .Σ-Structure.ΣTmIsoInvNat {Γ} {Δ} A B a b σ = funExt λ x → congP (λ _ z → uncurry pairSig (a (σ x) , z)) (symP (toPathP (let
      -- don't look at this
      goal :
        transp (λ i → El (B (pairSig (σ (fstPairSig {B = λ v → A (σ v)} x (a (σ x)) i)) (sndPairSig {B = λ v → A (σ v)} x (a (σ x)) i))))
        i0
        (transp (λ i → El (B (pairSig (σ (fstPairSig {B = λ v → A (σ v)} (transp (λ j → El Δ) i x) (a (σ (transp (λ j → El Δ) i x))) (~ i))) (sndPairSig {B = λ v → A (σ v)} (transp (λ j → El Δ) i x) (a (σ (transp (λ j → El Δ) i x))) (~ i)))))
         i0
         (b (σ (transp (λ j → El Δ) i0 x))))
        ≡
          b (σ x)
      goal j = transp (λ i → El (B (pairSig (σ (fstPairSig {B = λ v → A (σ v)} x (a (σ x)) (i ∨ j))) (sndPairSig {B = λ v → A (σ v)} x (a (σ x)) (i ∨ j)))))
        j
        (transp (λ i → El (B (pairSig (σ (fstPairSig {B = λ v → A (σ v)} (transp (λ _ → El Δ) (i ∨ j) x) (a (σ (transp (λ _ → El Δ) (i ∨ j) x))) (~ i ∨ j))) (sndPairSig {B = λ v → A (σ v)} (transp (λ j → El Δ) (i ∨ j) x) (a (σ (transp (λ _ → El Δ) (i ∨ j) x))) (~ i ∨ j)))))
          j
         (b (σ (transp (λ _ → El Δ) j x))))
      in goal)))

  module U-Π where
    open Algebraic
    open CwF UCwF

    U-Π-Structure : Π-Structure (UCat TU) UCwF
    U-Π-Structure .Π-Structure.ΠTy A B x                = Pi (A x) (λ y → B (pairSig x y))
    U-Π-Structure .Π-Structure.ΠTyNat A B σ             = funExt (λ x → cong (Pi (A (σ x))) (funExt (λ y → cong B (cong₂ pairSig (cong σ (sym (fstPairSig x y))) (symP (sndPairSig x y))))))
    U-Π-Structure .Π-Structure.ΠTmIso {Γ} A B           =
      ((a : El Γ) → El (Pi (A a) (λ y → B (pairSig a y))))           Iso⟨ codomainIsoDep (λ x → PiIso (A x) (λ y → B (pairSig x y))) ⟩
      (∀ a b → El (B (pairSig a b)))                                 Iso⟨ invIso curryIso ⟩
      (((a , b) : Σ (El Γ) (λ z → El (A z))) → El (B (pairSig a b))) Iso⟨ invIso (domIsoDep (invIso (SigIso _ _))) ⟩
      (((x : El (Sig Γ A)) → El (B x)))                              ∎Iso
    U-Π-Structure .Π-Structure.ΠTmIsoInvNat A B M σ i x =
      lamPi
        (λ y → M (pairSig (σ (fstPairSig x y (~ i))) (sndPairSig {B = A [ σ ]Ty} x y (~ i))))
