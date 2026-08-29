module Utils.InternalCategory where

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import TarskiUniverse.Base

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
  record [_]CodedCategory : Type (ℓ-max (ℓ-max (ℓ-max ℓU ℓEl) ℓob) ℓhom) where
    field
      isSmallOb : Univ hasCodeFor (C .ob)
      isSmallHom : ∀ x y → Univ hasCodeFor (C [ x , y ])

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

  private
    obᵢ : U
    obᵢ = isSmallOb .fst
    oᵢ→o : El obᵢ → C .ob
    oᵢ→o = isSmallOb .snd .fst
    homᵢ : ∀ x y → U
    homᵢ x y = isSmallHom (oᵢ→o x) (oᵢ→o y) .fst
    h→hᵢ : ∀ {x} {y} → C [ oᵢ→o x , oᵢ→o y ] → El (homᵢ x y)
    h→hᵢ f = invEquiv (isSmallHom _ _ .snd) .fst f
    hᵢ→h : ∀ {x} {y} → El (homᵢ x y) → C [ oᵢ→o x , oᵢ→o y ]
    hᵢ→h f = isSmallHom _ _ .snd .fst f

    homEquiv : ∀ {x} {y} → El (isSmallHom (oᵢ→o x) (oᵢ→o y) .fst)
                         ≃ C [ oᵢ→o x , oᵢ→o y ]
    homEquiv = isSmallHom (oᵢ→o _) (oᵢ→o _) .snd

  Coded→Internal : InternalCategory Univ
  Coded→Internal .InternalCategory.obᵢ = obᵢ
  Coded→Internal .InternalCategory.Hom[_,_]ᵢ = homᵢ
  Coded→Internal .InternalCategory.idᵢ = h→hᵢ (C .id)
  Coded→Internal .InternalCategory._⋆ᵢ_ f g = h→hᵢ (hᵢ→h f ⋆⟨ C ⟩ hᵢ→h g)
  Coded→Internal .InternalCategory.⋆IdLᵢ f =
    h→hᵢ ((hᵢ→h (h→hᵢ (C .id))) ⋆⟨ C ⟩ (hᵢ→h f)) ≡⟨ cong (λ k → h→hᵢ (k ⋆⟨ C ⟩ (hᵢ→h f))) (secEq homEquiv (C .id)) ⟩
    h→hᵢ ((C .id) ⋆⟨ C ⟩ (hᵢ→h f))               ≡⟨ cong h→hᵢ (C .⋆IdL (hᵢ→h f)) ⟩
    h→hᵢ (hᵢ→h f)                                ≡⟨ retEq homEquiv f ⟩
    f                                            ∎
  Coded→Internal .InternalCategory.⋆IdRᵢ f =
    h→hᵢ ((hᵢ→h f) ⋆⟨ C ⟩ (hᵢ→h (h→hᵢ (C .id)))) ≡⟨ cong (λ k → h→hᵢ ((hᵢ→h f) ⋆⟨ C ⟩ k)) (secEq homEquiv (C .id)) ⟩
    h→hᵢ ((hᵢ→h f) ⋆⟨ C ⟩ (C .id))               ≡⟨ cong h→hᵢ (C .⋆IdR (hᵢ→h f)) ⟩
    h→hᵢ (hᵢ→h f)                                ≡⟨ retEq homEquiv f ⟩
    f                                            ∎
  Coded→Internal .InternalCategory.⋆Assocᵢ f g h =
    h→hᵢ ((hᵢ→h (h→hᵢ ((hᵢ→h f) ⋆⟨ C ⟩ (hᵢ→h g)))) ⋆⟨ C ⟩ (hᵢ→h h)) ≡⟨ cong (λ k → h→hᵢ (k ⋆⟨ C ⟩ (hᵢ→h h))) (secEq homEquiv ((hᵢ→h f) ⋆⟨ C ⟩ (hᵢ→h g))) ⟩
    h→hᵢ (((hᵢ→h f) ⋆⟨ C ⟩ (hᵢ→h g)) ⋆⟨ C ⟩ (hᵢ→h h))               ≡⟨ cong h→hᵢ (C .⋆Assoc (hᵢ→h f) (hᵢ→h g) (hᵢ→h h)) ⟩
    h→hᵢ ((hᵢ→h f) ⋆⟨ C ⟩ ((hᵢ→h g) ⋆⟨ C ⟩ (hᵢ→h h)))               ≡⟨ cong (λ k → h→hᵢ ((hᵢ→h f) ⋆⟨ C ⟩ k)) (sym (secEq homEquiv ((hᵢ→h g) ⋆⟨ C ⟩ (hᵢ→h h)))) ⟩
    h→hᵢ ((hᵢ→h f) ⋆⟨ C ⟩ (hᵢ→h (h→hᵢ ((hᵢ→h g) ⋆⟨ C ⟩ (hᵢ→h h))))) ∎

  open import Cubical.Categories.Equivalence

  internalizeFunctor : Functor (InternalCategory.→Category Coded→Internal) C
  internalizeFunctor .F-ob = oᵢ→o
  internalizeFunctor .F-hom = hᵢ→h
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

  section : Coded→Internal (Internal→Coded C) ≡ C
  section i .obᵢ = C .obᵢ
  section i .Hom[_,_]ᵢ = C .Hom[_,_]ᵢ
  section i .idᵢ = C .idᵢ
  section i ._⋆ᵢ_ = C ._⋆ᵢ_
  section i .⋆IdLᵢ f =
    isSetEl _ _ _ (Coded→Internal (Internal→Coded C) .⋆IdLᵢ f) (C .⋆IdLᵢ f) i
  section i .⋆IdRᵢ f =
    isSetEl _ _ _ (Coded→Internal (Internal→Coded C) .⋆IdRᵢ f) (C .⋆IdRᵢ f) i
  section i .⋆Assocᵢ f g h =
    isSetEl _ _ _ (Coded→Internal (Internal→Coded C) .⋆Assocᵢ f g h) (C .⋆Assocᵢ f g h) i
