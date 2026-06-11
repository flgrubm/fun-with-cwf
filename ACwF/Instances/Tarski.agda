{-# OPTIONS --lossy-unification #-}
module ACwF.Instances.Tarski where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function

open import Cubical.Functions.FunExtEquiv

open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Limits.Terminal

open import ACwF.Base
open import ACwF.Sigma

open import Agda.Builtin.Unit

open Iso
open Category

module _ {ℓU ℓEl : Level}
         (U : Type ℓU)
         (isSetU : isSet U)
         (El : U → Type ℓEl)
         (isSetEl : (Γ : U) → isSet (El Γ))
         (Unit : U)
         (isTerminalUnit : isContr (El Unit))
         (Sig : (A : U) → (El A → U) → U)
         -- (SigIso : (A : U) (B : El A → U) → Iso (El (Sig A B)) (Σ[ x ∈ El A ] El (B x)))
         (fstSig : {A : U} {B : El A → U} → El (Sig A B) → El A)
         (sndSig : {A : U} {B : El A → U} (p : El (Sig A B)) → El (B (fstSig p)))
         (pairSig : {A : U} {B : El A → U} (x : El A) → (El (B x)) → El (Sig A B))
         (ηSig : {A : U} {B : El A → U} (p : El (Sig A B)) → pairSig (fstSig p) (sndSig p) ≡ p)
         (fstPairSig : {A : U} {B : El A → U} (x : El A) (y : El (B x)) → fstSig (pairSig {B = B} x y) ≡ x)
         (sndPairSig : {A : U} {B : El A → U} (x : El A) (y : El (B x)) → PathP (λ i → El (B (fstPairSig {B = B} x y i))) (sndSig (pairSig {B = B} x y)) y)
  where

  PairIso : {A : U} {B : El A → U} → Iso (El (Sig A B)) (Σ[ x ∈ El A ] El (B x))
  PairIso .fun p .fst = fstSig p
  PairIso .fun p .snd = sndSig p
  PairIso .inv = uncurry pairSig
  PairIso .sec (x , y) = ΣPathP ((fstPairSig x y) , sndPairSig x y)
  PairIso .ret = ηSig
  
  UCat : Category ℓU ℓEl
  UCat .ob = U
  UCat .Hom[_,_] Δ Γ = El Δ → El Γ
  UCat .id x = x
  UCat ._⋆_ f g x = g (f x)
  UCat .⋆IdL _ = refl
  UCat .⋆IdR _ = refl
  UCat .⋆Assoc _ _ _ = refl
  UCat .isSetHom {y = y} = isSet→ (isSetEl y)

  open Algebraic

  module _ where
    open CwF

    UCwF : CwF UCat (ℓ-max ℓU ℓEl) ℓEl
    UCwF .⟨⟩ .fst          = Unit
    UCwF .⟨⟩ .snd _ .fst _ = isTerminalUnit .fst
    UCwF .⟨⟩ .snd Γ .snd σ = funExt (λ x → isTerminalUnit .snd (σ x))
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
    UCwF ._⋆_              = Sig
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

  open Algebraic
  open CwF UCwF

  U-Σ-Structure : Σ-Structure UCat UCwF
  U-Σ-Structure .Σ-Structure.ΣTy A B x = Sig (A x) λ y → B (pairSig x y)
  U-Σ-Structure .Σ-Structure.ΣTyNat A B σ = funExt λ x → cong (Sig (A (σ x))) (funExt λ y → cong B (cong₂ pairSig (cong σ (sym (fstPairSig _ _))) (symP (sndPairSig _ _))))
  U-Σ-Structure .Σ-Structure.ΣTmIso A B = compIso (codomainIsoDep (λ _ → PairIso)) Σ-Π-Iso
  U-Σ-Structure .Σ-Structure.coerce A B a σ = funExt λ x → cong B (cong₂ pairSig (cong σ (sym (fstPairSig _ _))) (symP (sndPairSig _ _)))
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
