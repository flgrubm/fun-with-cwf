module TarskiUniverse.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Limits

open import TarskiUniverse.Base

open Functor

module _ {ℓU ℓEl : Level} (TU : TarskiUniverse-Base ℓU ℓEl) where

  open Category
  open TarskiUniverse-Base TU

  UCat : Category ℓU ℓEl
  UCat .ob = U
  UCat .Hom[_,_] Δ Γ = El Δ → El Γ
  UCat .id x = x
  UCat ._⋆_ f g x = g (f x)
  UCat .⋆IdL _ = refl
  UCat .⋆IdR _ = refl
  UCat .⋆Assoc _ _ _ = refl
  UCat .isSetHom {y = y} = isSet→ (isSetEl y)

  -- An internal category: a category whose object- and morphism-types are
  -- given by codes (so they live in `U`/`El`), rather than arbitrary types.
  -- Expressing "the objects are an El" is just storing the code `Obᵢ : U` and
  -- using `El Obᵢ` wherever the object type is needed.
  record InternalCategory : Type (ℓ-max ℓU ℓEl) where
    field
      Obᵢ  : U
      Homᵢ : El Obᵢ → El Obᵢ → U
      idᵢ  : (x : El Obᵢ) → El (Homᵢ x x)
      _⋆ᵢ_ : {x y z : El Obᵢ} → El (Homᵢ x y) → El (Homᵢ y z) → El (Homᵢ x z)
      ⋆IdLᵢ   : {x y : El Obᵢ} (f : El (Homᵢ x y)) → idᵢ x ⋆ᵢ f ≡ f
      ⋆IdRᵢ   : {x y : El Obᵢ} (f : El (Homᵢ x y)) → f ⋆ᵢ idᵢ y ≡ f
      ⋆Assocᵢ : {x y z w : El Obᵢ} (f : El (Homᵢ x y)) (g : El (Homᵢ y z)) (h : El (Homᵢ z w))
              → (f ⋆ᵢ g) ⋆ᵢ h ≡ f ⋆ᵢ (g ⋆ᵢ h)

  open InternalCategory

  -- Externalize an internal category to an ordinary cubical category via `El`,
  -- so we can reuse the `Functor`/`Limits` machinery for diagrams.
  ⟦_⟧Cat : InternalCategory → Category ℓEl ℓEl
  ⟦ D ⟧Cat .ob          = El (D .Obᵢ)
  ⟦ D ⟧Cat .Hom[_,_] x y = El (D .Homᵢ x y)
  ⟦ D ⟧Cat .id {x}      = D .idᵢ x
  ⟦ D ⟧Cat ._⋆_         = D ._⋆ᵢ_
  ⟦ D ⟧Cat .⋆IdL        = D .⋆IdLᵢ
  ⟦ D ⟧Cat .⋆IdR        = D .⋆IdRᵢ
  ⟦ D ⟧Cat .⋆Assoc      = D .⋆Assocᵢ
  ⟦ D ⟧Cat .isSetHom    = isSetEl _

  record TarskiUniverse-Limit : Type (ℓ-max ℓU ℓEl) where
    field
      Limit : {D : InternalCategory} (J : Functor ⟦ D ⟧Cat UCat) → U
      LimitIso : {D : InternalCategory} (J : Functor ⟦ D ⟧Cat UCat) →
        Iso
          (El (Limit {D} J))
          (Σ
            ((d : El (D .Obᵢ)) → El (J ⟅ d ⟆))
              λ s → {x y : El (D .Obᵢ)} (m : El (D .Homᵢ x y)) → J .F-hom m (s x) ≡ s y)

module _ {ℓU ℓEl : Level} (TU : TarskiUniverse ℓU ℓEl) where

  open Category
  open TarskiUniverse TU

  SigPathP : ∀ {A} {B} → {x y : El (Sig A B)} → (fst≡ : fstSig x ≡ fstSig y) → PathP (λ i → El (B (fst≡ i))) (sndSig x) (sndSig y) → x ≡ y
  SigPathP {x = x} {y = y} fst≡ snd≡ = sym (ηSig x) ∙ cong (uncurry pairSig) (ΣPathP (fst≡ , snd≡)) ∙ ηSig y
    where
      open import Cubical.Foundations.Function
      open import Cubical.Data.Sigma
