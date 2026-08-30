module Utils.InternalCategory where

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import TarskiUniverse.Base
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open Category
open Functor

private
  variable
    ℓ ℓ' : Level

-- Define two notions of "small" category (w.r.t a Tarski universe). The first
-- is an internal category: defined like a category, but with codes instead of
-- types. The second is a coded category: a normal category, with an additional
-- code attached to ob and homs.
--
-- We can translate between the two, and we have a section:
-- internal→coded→internal C ≡ C. However, we do not have a retract, because
-- coded→internal→coded forgets the original category and only restores it up to
-- category equivalence. Even if C is univalent, we can't recover an equality
-- because of different universe levels.

module _ {ℓU ℓEl : Level} {U : Type ℓU} (Univ : BareTarskiUniverse ℓEl U) where
  open BareTarskiUniverse Univ
  record InternalCategory : Type (ℓ-max ℓU ℓEl) where
    field
      obᵢ : U
      Hom[_,_]ᵢ : El obᵢ → El obᵢ → U
      idᵢ : ∀ {x} → El (Hom[ x , x ]ᵢ)
      _⋆ᵢ_ : ∀ {x y z} → El (Hom[ x , y ]ᵢ) → El (Hom[ y , z ]ᵢ) → El (Hom[ x , z ]ᵢ)

      ⋆IdLᵢ : ∀ {x y} (f : El (Hom[ x , y ]ᵢ)) → idᵢ ⋆ᵢ f ≡ f
      ⋆IdRᵢ : ∀ {x y} (f : El (Hom[ x , y ]ᵢ)) → f ⋆ᵢ idᵢ ≡ f
      ⋆Assocᵢ : ∀ {x y z w} (f : El (Hom[ x , y ]ᵢ)) (g : El (Hom[ y , z ]ᵢ)) (h : El (Hom[ z , w ]ᵢ))
           → (f ⋆ᵢ g) ⋆ᵢ h ≡ f ⋆ᵢ (g ⋆ᵢ h)

    →Category : Category ℓEl ℓEl
    →Category .ob = El obᵢ
    →Category .Hom[_,_] x y = El Hom[ x , y ]ᵢ
    →Category .id = idᵢ
    →Category ._⋆_ = _⋆ᵢ_
    →Category .⋆IdL = ⋆IdLᵢ
    →Category .⋆IdR = ⋆IdRᵢ
    →Category .⋆Assoc = ⋆Assocᵢ
    →Category .isSetHom = isSetEl _

  open InternalCategory

module _ {ℓU ℓEl : Level} {U : Type ℓU} (Univ : BareTarskiUniverse ℓEl U) where
  open BareTarskiUniverse Univ
  _hasCodeFor_ : {ℓ : Level} → Type ℓ → Type (ℓ-max (ℓ-max ℓU ℓEl) ℓ)
  _hasCodeFor_ X = Σ U λ x → El x ≃ X
  infixl 50 _hasCodeFor_

module _
  {ℓU ℓEl : Level} {U : Type ℓU} (Univ : BareTarskiUniverse ℓEl U)
  {ℓob ℓhom : Level} (C : Category ℓob ℓhom)
  where
  open BareTarskiUniverse Univ
  record [_]CodedCategory : Type (ℓ-max (ℓ-max (ℓ-max ℓU ℓEl) ℓob) ℓhom) where
    field
      isSmallOb : Univ hasCodeFor (C .ob)
      isSmallHom : ∀ x y → Univ hasCodeFor (C [ x , y ])
    obᵢ : U
    obᵢ = isSmallOb .fst
    obᵢ→ob : El obᵢ → C .ob
    obᵢ→ob = isSmallOb .snd .fst
    homᵢ : ∀ x y → U
    homᵢ x y = isSmallHom (obᵢ→ob x) (obᵢ→ob y) .fst
    hom→homᵢ : ∀ {x} {y} → C [ obᵢ→ob x , obᵢ→ob y ] → El (homᵢ x y)
    hom→homᵢ f = invEquiv (isSmallHom _ _ .snd) .fst f
    homᵢ→hom : ∀ {x} {y} → El (homᵢ x y) → C [ obᵢ→ob x , obᵢ→ob y ]
    homᵢ→hom f = isSmallHom _ _ .snd .fst f
    homEquiv : ∀ {x} {y} → El (isSmallHom (obᵢ→ob x) (obᵢ→ob y) .fst)
                         ≃ C [ obᵢ→ob x , obᵢ→ob y ]
    homEquiv = isSmallHom (obᵢ→ob _) (obᵢ→ob _) .snd

module _
  {ℓU ℓEl : Level} {U : Type ℓU} {Univ : BareTarskiUniverse ℓEl U}
  (C : InternalCategory Univ)
  where
  open InternalCategory
  Internal→Coded : [ Univ ]CodedCategory (InternalCategory.→Category C)
  Internal→Coded .[_]CodedCategory.isSmallOb = C .obᵢ , idEquiv _
  Internal→Coded .[_]CodedCategory.isSmallHom x y = (C .Hom[_,_]ᵢ x y) , idEquiv _

module _
  {ℓU ℓEl : Level} {U : Type ℓU} {Univ : BareTarskiUniverse ℓEl U}
  {ℓob ℓhom : Level} {C : Category ℓob ℓhom} (coded : [ Univ ]CodedCategory C)
  where

  open BareTarskiUniverse Univ
  open [_]CodedCategory coded

  Coded→Internal : InternalCategory Univ
  Coded→Internal .InternalCategory.obᵢ = obᵢ
  Coded→Internal .InternalCategory.Hom[_,_]ᵢ = homᵢ
  Coded→Internal .InternalCategory.idᵢ = hom→homᵢ (C .id)
  Coded→Internal .InternalCategory._⋆ᵢ_ f g = hom→homᵢ (homᵢ→hom f ⋆⟨ C ⟩ homᵢ→hom g)
  Coded→Internal .InternalCategory.⋆IdLᵢ f =
    hom→homᵢ ((homᵢ→hom (hom→homᵢ (C .id))) ⋆⟨ C ⟩ (homᵢ→hom f)) ≡⟨ cong (λ k → hom→homᵢ (k ⋆⟨ C ⟩ (homᵢ→hom f))) (secEq homEquiv (C .id)) ⟩
    hom→homᵢ ((C .id) ⋆⟨ C ⟩ (homᵢ→hom f))                       ≡⟨ cong hom→homᵢ (C .⋆IdL (homᵢ→hom f)) ⟩
    hom→homᵢ (homᵢ→hom f)                                        ≡⟨ retEq homEquiv f ⟩
    f                                                            ∎
  Coded→Internal .InternalCategory.⋆IdRᵢ f =
    hom→homᵢ ((homᵢ→hom f) ⋆⟨ C ⟩ (homᵢ→hom (hom→homᵢ (C .id)))) ≡⟨ cong (λ k → hom→homᵢ ((homᵢ→hom f) ⋆⟨ C ⟩ k)) (secEq homEquiv (C .id)) ⟩
    hom→homᵢ ((homᵢ→hom f) ⋆⟨ C ⟩ (C .id))                       ≡⟨ cong hom→homᵢ (C .⋆IdR (homᵢ→hom f)) ⟩
    hom→homᵢ (homᵢ→hom f)                                        ≡⟨ retEq homEquiv f ⟩
    f                                                            ∎
  Coded→Internal .InternalCategory.⋆Assocᵢ f g h =
    hom→homᵢ ((homᵢ→hom (hom→homᵢ ((homᵢ→hom f) ⋆⟨ C ⟩ (homᵢ→hom g)))) ⋆⟨ C ⟩ (homᵢ→hom h)) ≡⟨ cong (λ k → hom→homᵢ (k ⋆⟨ C ⟩ (homᵢ→hom h))) (secEq homEquiv ((homᵢ→hom f) ⋆⟨ C ⟩ (homᵢ→hom g))) ⟩
    hom→homᵢ (((homᵢ→hom f) ⋆⟨ C ⟩ (homᵢ→hom g)) ⋆⟨ C ⟩ (homᵢ→hom h))                       ≡⟨ cong hom→homᵢ (C .⋆Assoc (homᵢ→hom f) (homᵢ→hom g) (homᵢ→hom h)) ⟩
    hom→homᵢ ((homᵢ→hom f) ⋆⟨ C ⟩ ((homᵢ→hom g) ⋆⟨ C ⟩ (homᵢ→hom h)))                       ≡⟨ cong (λ k → hom→homᵢ ((homᵢ→hom f) ⋆⟨ C ⟩ k)) (sym (secEq homEquiv ((homᵢ→hom g) ⋆⟨ C ⟩ (homᵢ→hom h)))) ⟩
    hom→homᵢ ((homᵢ→hom f) ⋆⟨ C ⟩ (homᵢ→hom (hom→homᵢ ((homᵢ→hom g) ⋆⟨ C ⟩ (homᵢ→hom h))))) ∎

  open import Cubical.Categories.Equivalence

  internalizeFunctor : Functor (InternalCategory.→Category Coded→Internal) C
  internalizeFunctor .F-ob = obᵢ→ob
  internalizeFunctor .F-hom = homᵢ→hom
  internalizeFunctor .F-id = secEq homEquiv (C .id)
  internalizeFunctor .F-seq f g = secEq homEquiv _

  internalize≃ : InternalCategory.→Category Coded→Internal ≃ᶜ C
  internalize≃ ._≃ᶜ_.func = internalizeFunctor
  internalize≃ ._≃ᶜ_.isEquiv = isFullyFaithful+isEquivF-ob→isEquiv
    (λ x y → isSmallHom _ _ .snd .snd)
    (isSmallOb .snd .snd)

module _
  {ℓU ℓEl : Level} {U : Type ℓU} {Univ : BareTarskiUniverse ℓEl U}
  (C : InternalCategory Univ)
  where

  open BareTarskiUniverse Univ
  open InternalCategory

  Internal→Coded→Internal : Coded→Internal (Internal→Coded C) ≡ C
  Internal→Coded→Internal i .obᵢ = C .obᵢ
  Internal→Coded→Internal i .Hom[_,_]ᵢ = C .Hom[_,_]ᵢ
  Internal→Coded→Internal i .idᵢ = C .idᵢ
  Internal→Coded→Internal i ._⋆ᵢ_ = C ._⋆ᵢ_
  Internal→Coded→Internal i .⋆IdLᵢ f =
    isSetEl _ _ _ (Coded→Internal (Internal→Coded C) .⋆IdLᵢ f) (C .⋆IdLᵢ f) i
  Internal→Coded→Internal i .⋆IdRᵢ f =
    isSetEl _ _ _ (Coded→Internal (Internal→Coded C) .⋆IdRᵢ f) (C .⋆IdRᵢ f) i
  Internal→Coded→Internal i .⋆Assocᵢ f g h =
    isSetEl _ _ _ (Coded→Internal (Internal→Coded C) .⋆Assocᵢ f g h) (C .⋆Assocᵢ f g h) i

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
