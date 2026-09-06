module TarskiUniverse.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Categories.Category

open import TarskiUniverse.Base

module _ {ℓU ℓEl : Level} {U : Type ℓU} (TU : BareTarskiUniverse ℓEl U) where

  open Category
  open BareTarskiUniverse TU

  -- U is a set, so a path of elements may be reindexed onto any other path of
  -- codes with the same endpoints.  `e` and `e'` are inferable (from the
  -- argument and from the goal), but `TU` is not — `El TU` is a stuck
  -- projection — so it is the one explicit argument.
  ElPathP : {c c' : U} {e e' : c ≡ c'} {x : El c} {y : El c'}
    → PathP (λ i → El (e i)) x y
    → PathP (λ i → El (e' i)) x y
  ElPathP {c} {c'} {e} {e'} {x} {y} path = subst (λ ϵ → PathP (λ i → El (ϵ i)) x y) (isSetU _ _ e e') path

  UCat : Category ℓU ℓEl
  UCat .ob = U
  UCat .Hom[_,_] Δ Γ = El Δ → El Γ
  UCat .id x = x
  UCat ._⋆_ f g x = g (f x)
  UCat .⋆IdL _ = refl
  UCat .⋆IdR _ = refl
  UCat .⋆Assoc _ _ _ = refl
  UCat .isSetHom {y = y} = isSet→ (isSetEl y)

private variable ℓ ℓ' : Level

module _ {ℓU ℓEl : Level} {U : Type ℓU} (Univ : BareTarskiUniverse ℓEl U) where
  open BareTarskiUniverse Univ
  _hasCodeFor_ : {ℓ : Level} → Type ℓ → Type (ℓ-max (ℓ-max ℓU ℓEl) ℓ)
  _hasCodeFor_ X = Σ U λ x → El x ≃ X
  infixl 50 _hasCodeFor_

module _
  {ℓU ℓEl : Level} {U : Type ℓU} (TU : BareTarskiUniverse ℓEl U)
  where
  open BareTarskiUniverse TU
  open hasSigma
  open hasUnit renaming (Unit to TUnit)
  open hasPi
  open hasEq

  _hasCodeForΣ : {A : Type ℓ} {B : A → Type ℓ'}
    → hasSigma TU
    → TU hasCodeFor A
    → (∀ x → TU hasCodeFor (B x))
    → TU hasCodeFor (Σ A B)
  _hasCodeForΣ hasSigmaTU codeForA codeForB .fst = hasSigmaTU .Sigma (codeForA .fst) (λ a → codeForB (codeForA .snd .fst a) .fst)
  _hasCodeForΣ hasSigmaTU codeForA codeForB .snd =
       isoToEquiv (hasSigmaTU .SigmaIso _ _)
    ∙ₑ Σ-cong-equiv (codeForA .snd) (λ a → codeForB _ .snd)

  _hasCodeForUnit : hasUnit TU → TU hasCodeFor Unit
  _hasCodeForUnit hasUnitTU .fst = hasUnitTU .TUnit
  _hasCodeForUnit hasUnitTU .snd = isContr→≃Unit (hasUnitTU .isContrElUnit)

  _hasCodeForΠ : {A : Type ℓ} {B : A → Type ℓ'}
    → hasPi TU
    → TU hasCodeFor A
    → (∀ x → TU hasCodeFor (B x))
    → TU hasCodeFor ((x : A) → B x)
  _hasCodeForΠ hasPiTU codeForA codeForB .fst = hasPiTU .Pi (codeForA .fst) λ a → codeForB (codeForA .snd .fst a) .fst
  _hasCodeForΠ hasPiTU codeForA codeForB .snd =
       isoToEquiv (hasPiTU .PiIso _ _ )
    ∙ₑ equivΠ (codeForA .snd) (λ a → codeForB _ .snd)

  _hasCodeForEq : {A : Type ℓ} (a b : A)
    → hasEq TU
    → TU hasCodeFor A
    → TU hasCodeFor (a ≡ b)
  _hasCodeForEq a b hasEqTU codeForA .fst = hasEqTU .Eq (codeForA .fst) (invEq (codeForA .snd) a) (invEq (codeForA .snd) b)
  _hasCodeForEq a b hasEqTU codeForA .snd =
       isoToEquiv (hasEqTU .EqIso _ _ _)
    ∙ₑ invEquiv (congEquiv (invEquiv (codeForA .snd)))

  _hasCodeForEl : {a : U} → TU hasCodeFor (El a)
  _hasCodeForEl {a} .fst = a
  _hasCodeForEl {a} .snd = idEquiv _
