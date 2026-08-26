module ACwF.Instances.TarskiUniverse where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Function
open import Cubical.Functions.FunExtEquiv
open import Cubical.Data.Sigma

open import Cubical.Categories.Category

open import ACwF.Base
open import ACwF.Sigma
open import ACwF.Pi
open import ACwF.Eq

open import TarskiUniverse.Base
open import TarskiUniverse.Properties

open import Agda.Builtin.Unit

open Iso
open Category

module _ {ℓU ℓEl : Level} {U : Type ℓU} (Univ : TarskiUniverse ℓEl U) where

  open Algebraic
  open TarskiUniverse Univ

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
    UCwF ._▹_              = Sigma
    UCwF .p                = fstSigma
    UCwF .q                = sndSigma
    UCwF ._⁺ σ s           = pairSigma (σ (fstSigma s)) (sndSigma s)
    UCwF .⟨_⟩ a x          = pairSigma x (a x)
    UCwF .⟨⟩∘ a σ          = funExt (λ x → cong₂ pairSigma (sym (cong σ (fstPairSigma x (a (σ x))))) (symP (sndPairSigma x (a (σ x)))))
    UCwF .p⁺∘⟨q⟩≡id        = funExt λ x → cong₂ pairSigma (cong fstSigma (fstPairSigma _ _)) (sndPairSigma _ _) ∙ ηSigma _
    UCwF .∘⁺ σ τ           = funExt λ x → cong₂ pairSigma (cong τ (sym (fstPairSigma _ _))) (symP (sndPairSigma _ _))
    UCwF .id⁺              = funExt λ x → ηSigma _
    UCwF .p∘⁺ σ            = funExt λ x → fstPairSigma _ _
    UCwF .[p][⁺]Ty B σ     = funExt λ x → cong B (fstPairSigma _ _)
    UCwF .q[⁺]Tm σ         = funExt λ x → sndPairSigma _ _
    UCwF .p∘⟨⟩≡id a        = funExt λ x → fstPairSigma _ _
    UCwF .[p][⟨⟩]Ty B a    = funExt λ x → cong B (fstPairSigma _ _)
    UCwF .q[⟨⟩]Tm a        = funExt λ x → sndPairSigma _ _

  module U-Σ
    where

    open Algebraic
    open CwF UCwF

    U-Σ-Structure : Σ-Structure (UCat TU) UCwF
    U-Σ-Structure .Σ-Structure.ΣTy A B x                      = Sigma (A x) λ y → B (pairSigma x y)
    U-Σ-Structure .Σ-Structure.ΣTyNat A B σ                   = funExt λ x → cong (Sigma (A (σ x))) (funExt λ y → cong B (cong₂ pairSigma (cong σ (sym (fstPairSigma _ _))) (symP (sndPairSigma _ _))))
    U-Σ-Structure .Σ-Structure.ΣTmIso A B                     = compIso (codomainIsoDep (λ _ → SigmaIso _ _)) Σ-Π-Iso
    U-Σ-Structure .Σ-Structure.coerce A B a σ                 = funExt λ x → cong B (cong₂ pairSigma (cong σ (sym (fstPairSigma _ _))) (symP (sndPairSigma _ _)))
    U-Σ-Structure .Σ-Structure.ΣTmIsoInvNat {Γ} {Δ} A B a b σ = funExt λ x → congP (λ _ z → uncurry pairSigma (a (σ x) , z)) (symP (toPathP (let
      -- don't look at this
      goal :
        transp (λ i → El (B (pairSigma (σ (fstPairSigma {B = λ v → A (σ v)} x (a (σ x)) i)) (sndPairSigma {B = λ v → A (σ v)} x (a (σ x)) i))))
        i0
        (transp (λ i → El (B (pairSigma (σ (fstPairSigma {B = λ v → A (σ v)} (transp (λ j → El Δ) i x) (a (σ (transp (λ j → El Δ) i x))) (~ i))) (sndPairSigma {B = λ v → A (σ v)} (transp (λ j → El Δ) i x) (a (σ (transp (λ j → El Δ) i x))) (~ i)))))
         i0
         (b (σ (transp (λ j → El Δ) i0 x))))
        ≡
          b (σ x)
      goal j = transp (λ i → El (B (pairSigma (σ (fstPairSigma {B = λ v → A (σ v)} x (a (σ x)) (i ∨ j))) (sndPairSigma {B = λ v → A (σ v)} x (a (σ x)) (i ∨ j)))))
        j
        (transp (λ i → El (B (pairSigma (σ (fstPairSigma {B = λ v → A (σ v)} (transp (λ _ → El Δ) (i ∨ j) x) (a (σ (transp (λ _ → El Δ) (i ∨ j) x))) (~ i ∨ j))) (sndPairSigma {B = λ v → A (σ v)} (transp (λ j → El Δ) (i ∨ j) x) (a (σ (transp (λ _ → El Δ) (i ∨ j) x))) (~ i ∨ j)))))
          j
         (b (σ (transp (λ _ → El Δ) j x))))
      in goal)))

  module U-Π (TU-Pi : hasPi TU) where
    open hasPi TU-Pi
    open Algebraic
    open CwF UCwF

    U-Π-Structure : Π-Structure (UCat TU) UCwF
    U-Π-Structure .Π-Structure.ΠTy A B x                = Pi (A x) (λ y → B (pairSigma x y))
    U-Π-Structure .Π-Structure.ΠTyNat A B σ             = funExt (λ x → cong (Pi (A (σ x))) (funExt (λ y → cong B (cong₂ pairSigma (cong σ (sym (fstPairSigma x y))) (symP (sndPairSigma x y))))))
    U-Π-Structure .Π-Structure.ΠTmIso {Γ} A B           =
      ((a : El Γ) → El (Pi (A a) (λ y → B (pairSigma a y))))           Iso⟨ codomainIsoDep (λ x → PiIso (A x) (λ y → B (pairSigma x y))) ⟩
      (∀ a b → El (B (pairSigma a b)))                                 Iso⟨ invIso curryIso ⟩
      (((a , b) : Σ (El Γ) (λ z → El (A z))) → El (B (pairSigma a b))) Iso⟨ invIso (domIsoDep (invIso (SigmaIso _ _))) ⟩
      (((x : El (Sigma Γ A)) → El (B x)))                              ∎Iso
    U-Π-Structure .Π-Structure.ΠTmIsoInvNat A B M σ i x =
      lamPi
        (λ y → M (pairSigma (σ (fstPairSigma x y (~ i))) (sndPairSigma {B = A [ σ ]Ty} x y (~ i))))

  module U-Eq (TU-Eq : hasEq TU) where
    open hasEq TU-Eq
    open Algebraic
    open CwF UCwF

    U-Eq-Structure : Eq-Structure UCwF
    U-Eq-Structure .Eq-Structure.EqTy A a b x            = Eq (A x) (a x) (b x)
    U-Eq-Structure .Eq-Structure.EqTyNat _ _ _ _         = refl
    U-Eq-Structure .Eq-Structure.EqTmIso {Γ} A a b       =
      ((x : El Γ) → El (Eq (A x) (a x) (b x))) Iso⟨ codomainIsoDep (λ x → EqIso (A x) (a x) (b x)) ⟩
      ((x : El Γ) → a x ≡ b x)                 Iso⟨ funExtIso ⟩
      (a ≡ b)                                  ∎Iso
    U-Eq-Structure .Eq-Structure.EqTmIsoInvNat _ _ _ _ _ = refl
