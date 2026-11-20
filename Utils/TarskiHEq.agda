module Utils.TarskiHEq where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism

open import TarskiUniverse.Base
open import TarskiUniverse.Properties

-- | Heterogeneous equality of elements of a Tarski universe.
--
-- An element together with its code is a point of the total space `∫El`.
-- Codes and elements form sets, so a path there is as good as a path of
-- elements over *any* path of codes with the same ends (`fromHEq`).  A chain
-- of equations between elements of different (but equal) codes can thus be
-- written as an ordinary path composite and turned into a `PathP` only at
-- the end.  Together with the Σ-lemmas below this is what the CwF of
-- families in a Tarski universe needs to reason about elements of
-- `El (Sigma Γ A)`, which are pairs only up to `SigmaIso`.
module TarskiHEq {ℓU ℓEl : Level} {U : Type ℓU} (Univ : TarskiUniverse ℓEl U) where
  open TarskiUniverse Univ

  ∫El : Type (ℓ-max ℓU ℓEl)
  ∫El = Σ U El

  ⟪_⟫ : {X : U} → El X → ∫El
  ⟪ u ⟫ = _ , u

  -- a path of elements over a path of codes is a heterogeneous equation
  toHEq : {X Y : U} {c : X ≡ Y} {u : El X} {v : El Y}
        → PathP (λ i → El (c i)) u v
        → --------------------------
          ⟪ u ⟫ ≡ ⟪ v ⟫
  toHEq {c = c} e i = c i , e i

  -- a heterogeneous equation is a path of elements over any path of codes
  fromHEq : {X Y : U} (c : X ≡ Y) {u : El X} {v : El Y}
          → ⟪ u ⟫ ≡ ⟪ v ⟫
          → ---------------------------
            PathP (λ i → El (c i)) u v
  fromHEq c h = ElPathP TU (cong snd h)

  -- a heterogeneous equation between elements of one code is a path
  HEq→≡ : {X : U} {u v : El X}
        → ⟪ u ⟫ ≡ ⟪ v ⟫
        → --------------
          u ≡ v
  HEq→≡ = fromHEq refl

  -- transport does not change an element, heterogeneously
  substHEq : {ℓ : Level} {X : Type ℓ} (T : X → U) {x y : X} (e : x ≡ y) (u : El (T x))
           → ------------------------------------------------
             ⟪ subst (λ z → El (T z)) e u ⟫ ≡ ⟪ u ⟫
  substHEq T e u = sym (toHEq (subst-filler (λ z → El (T z)) e u))

  -- sections that agree pointwise, heterogeneously, are equal over any path
  -- between their families of codes
  ΠPathP : {ℓ : Level} {X : Type ℓ} {T T' : X → U} (e : T ≡ T')
           {f : (x : X) → El (T x)} {f' : (x : X) → El (T' x)}
         → ((x : X) → ⟪ f x ⟫ ≡ ⟪ f' x ⟫)
         → -----------------------------------------------
           PathP (λ i → (x : X) → El (e i x)) f f'
  ΠPathP e h i x = fromHEq (λ j → e j x) (h x) i

  -- | Pairs
  module _ {Γ : U} {A : El Γ → U} where

    -- `F (fstSigma s) (sndSigma s)` at `s = pairSigma x a` is `F x a`
    Sigma-β : {ℓ : Level} {R : Type ℓ} (F : (x : El Γ) → El (A x) → R) (x : El Γ) (a : El (A x))
            → -------------------------------------------------------------------------------
              F (fstSigma (pairSigma {B = A} x a)) (sndSigma (pairSigma {B = A} x a)) ≡ F x a
    Sigma-β F x a i = F (fstPairSigma {B = A} x a i) (sndPairSigma {B = A} x a i)

    -- `Sigma-β` for a function with a further argument whose type depends on
    -- the first component
    Sigma-β-dep : {ℓ ℓ' : Level} {D : El Γ → Type ℓ'} {R : Type ℓ}
                  (F : (x : El Γ) → El (A x) → D x → R) (x : El Γ) (a : El (A x))
                  (d : D (fstSigma (pairSigma {B = A} x a)))
                → ----------------------------------------------------------------------------
                  F (fstSigma (pairSigma {B = A} x a)) (sndSigma (pairSigma {B = A} x a)) d
                ≡ F x a (subst D (fstPairSigma {B = A} x a) d)
    Sigma-β-dep {D = D} F x a d i =
      F (fstPairSigma {B = A} x a i) (sndPairSigma {B = A} x a i)
        (subst-filler D (fstPairSigma {B = A} x a) d i)

    sndHEq : (x : El Γ) (a : El (A x))
           → -----------------------------------------------
             ⟪ sndSigma (pairSigma {B = A} x a) ⟫ ≡ ⟪ a ⟫
    sndHEq x a = toHEq (sndPairSigma {B = A} x a)

    -- pairs are equal when their components are, heterogeneously
    pair≡ : {x x' : El Γ} {a : El (A x)} {a' : El (A x')} (e : x ≡ x')
          → ⟪ a ⟫ ≡ ⟪ a' ⟫
          → ------------------------------------------------
            pairSigma {B = A} x a ≡ pairSigma x' a'
    pair≡ e h i = pairSigma (e i) (fromHEq (cong A e) h i)

    -- the ways of writing a point as a pair: there is exactly one
    Splitting : El (Sigma Γ A) → Type ℓEl
    Splitting s = fiber (SigmaIso Γ A .Iso.inv) s

    isPropSplitting : (s : El (Sigma Γ A))
                    → --------------------
                      isProp (Splitting s)
    isPropSplitting s = isContr→isProp (isoToIsEquiv (invIso (SigmaIso Γ A)) .equiv-proof s)

  -- maps out of `Sigma Γ T` and `Sigma Γ T'` are equal over a path `T ≡ T'`
  -- if they agree on pairs with heterogeneously equal second components
  module _ {Γ : U} where

    SigmaMapPathP : {ℓ : Level} {R : Type ℓ} {T T' : El Γ → U} (e : T ≡ T')
                    {h : El (Sigma Γ T) → R} {h' : El (Sigma Γ T') → R}
                  → ((x : El Γ) (u : El (T x)) (u' : El (T' x))
                     → ⟪ u ⟫ ≡ ⟪ u' ⟫ → h (pairSigma x u) ≡ h' (pairSigma x u'))
                  → ------------------------------------------------------------
                    PathP (λ i → El (Sigma Γ (e i)) → R) h h'
    SigmaMapPathP {R = R} {T = T} e {h = h} =
      J (λ T' e → {h' : El (Sigma Γ T') → R}
                → ((x : El Γ) (u : El (T x)) (u' : El (T' x))
                   → ⟪ u ⟫ ≡ ⟪ u' ⟫ → h (pairSigma x u) ≡ h' (pairSigma x u'))
                → PathP (λ i → El (Sigma Γ (e i)) → R) h h')
        (λ {h'} H → funExt λ s →
           cong h (sym (ηSigma s)) ∙∙ H _ (sndSigma s) (sndSigma s) refl ∙∙ cong h' (ηSigma s))
        e
