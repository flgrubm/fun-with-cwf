module TarskiUniverse.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels

open import Cubical.Categories.Category

open import TarskiUniverse.Base

module _ {ℓU ℓEl : Level} (TU : TarskiUniverse ℓU ℓEl) where

  open Category
  open TarskiUniverse TU

  UCat : Category ℓU ℓEl
  UCat .ob = U
  UCat .Hom[_,_] Δ Γ = El Δ → El Γ
  UCat .id x = x
  UCat ._⋆_ f g x = g (f x)
  UCat .⋆IdL _ = refl
  UCat .⋆IdR _ = refl
  UCat .⋆Assoc _ _ _ = refl
  UCat .isSetHom {y = y} = isSet→ (isSetEl y)

  SigPathP : ∀ {A} {B} → {x y : El (Sig A B)} → (fst≡ : fstSig x ≡ fstSig y) → PathP (λ i → El (B (fst≡ i))) (sndSig x) (sndSig y) → x ≡ y
  SigPathP {x = x} {y = y} fst≡ snd≡ = sym (ηSig x) ∙ cong (uncurry pairSig) (ΣPathP (fst≡ , snd≡)) ∙ ηSig y
    where
      open import Cubical.Foundations.Function
      open import Cubical.Data.Sigma
