module Utils.VCat where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Categories.Category
open import Cubical.Data.IterativeSets.Base renaming (V⁰ to V ; El⁰ to El ; isSetEl⁰ to isSetEl)

open Category

module _ (ℓ : Level) where
  VCat : Category (ℓ-suc ℓ) ℓ
  VCat .ob       = V
  VCat .Hom[_,_] = λ Δ Γ → El Δ → El Γ
  VCat .id       = λ x → x
  VCat ._⋆_      = λ f g x → g (f x)
  VCat .⋆IdL     = λ _ → refl
  VCat .⋆IdR     = λ _ → refl
  VCat .⋆Assoc   = λ _ _ _ → refl
  VCat .isSetHom {y = y} = isSet→ (isSetEl y)
