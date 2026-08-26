module TarskiUniverse.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels

open import Cubical.Categories.Category

open import TarskiUniverse.Base

module _ {ℓU ℓEl : Level} {U : Type ℓU} (TU : BareTarskiUniverse ℓEl U) where

  open Category
  open BareTarskiUniverse TU

  UCat : Category ℓU ℓEl
  UCat .ob = U
  UCat .Hom[_,_] Δ Γ = El Δ → El Γ
  UCat .id x = x
  UCat ._⋆_ f g x = g (f x)
  UCat .⋆IdL _ = refl
  UCat .⋆IdR _ = refl
  UCat .⋆Assoc _ _ _ = refl
  UCat .isSetHom {y = y} = isSet→ (isSetEl y)
