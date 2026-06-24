module Scratch2 where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Functions.Image
open import Cubical.Functions.FunExtEquiv
open import Cubical.HITs.Replacement
open import Cubical.Displayed.Base
open import Cubical.Data.Sigma
open import Cubical.Data.W.W
open import Cubical.Data.IterativeSets.Base
open import Cubical.Data.IterativeMultisets.Base renaming (index to index∞ ; elements to elements∞)
open import Cubical.Functions.Embedding

is[_]Small : (ℓ : Level) {ℓ' : Level} (A : Type ℓ') → Type (ℓ-max (ℓ-suc ℓ) ℓ')
is[_]Small ℓ A = Σ (Type ℓ) λ B → B ≃ A

isLocally[_]Small : (ℓ : Level) {ℓ' : Level} (A : Type ℓ') → Type (ℓ-max (ℓ-suc ℓ) ℓ')
isLocally[_]Small ℓ A = (x y : A) → is[ ℓ ]Small (x ≡ y)

isSmall-≃-isSmall :  ∀ {ℓ} {ℓ'} {ℓ''} {A : Type ℓ'} {A' : Type ℓ''} → is[ ℓ ]Small A → A ≃ A' → is[ ℓ ]Small A'
isSmall-≃-isSmall small equiv .fst = small .fst
isSmall-≃-isSmall small equiv .snd = compEquiv (small .snd) equiv

isSmall≃ : ∀ {ℓ} {ℓ'} {ℓ''} {A : Type ℓ'} {A' : Type ℓ''}
  → is[ ℓ ]Small A
  → is[ ℓ ]Small A'
  → is[ ℓ ]Small (A ≃ A')
isSmall≃ smallA smallA' .fst = smallA .fst ≃ smallA' .fst
isSmall≃ smallA smallA' .snd = equivComp (smallA .snd) (smallA' .snd)

isSmall≡ : ∀ {ℓ} {ℓ'} {A : Type ℓ'} {A' : Type ℓ'}
  → is[ ℓ ]Small A
  → is[ ℓ ]Small A'
  → is[ ℓ ]Small (A ≡ A')
isSmall≡ smallA smallA' = isSmall-≃-isSmall (isSmall≃ smallA smallA') (invEquiv univalence)

isℓSmallℓ : ∀ {ℓ} (A : Type ℓ) → is[ ℓ ]Small A
isℓSmallℓ A .fst = A
isℓSmallℓ A .snd = idEquiv A

isSmallΣ : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ'} {B : A → Type ℓ''}
  → is[ ℓ ]Small A
  → ((a : A) → is[ ℓ ]Small (B a))
  → is[ ℓ ]Small (Σ A B)
isSmallΣ sA sB .fst = Σ[ a' ∈ sA .fst ] sB (sA .snd .fst a') .fst
isSmallΣ sA sB .snd = Σ-cong-equiv (sA .snd) (λ a' → sB (sA .snd .fst a') .snd)

isSmallΠ : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ'} {B : A → Type ℓ''}
  → is[ ℓ ]Small A
  → ((a : A) → is[ ℓ ]Small (B a))
  → is[ ℓ ]Small ((a : A) → B a)
isSmallΠ sA sB .fst = (a' : sA .fst) → sB (sA .snd .fst a') .fst
isSmallΠ sA sB .snd = equivΠ (sA .snd) (λ a' → sB (sA .snd .fst a') .snd)

module _ {ℓ ℓ' : Level} {A : Type ℓ} {B : Type ℓ'} (lsB : isLocally[ ℓ ]Small B) (f : A → B) where

  uaRel : UARel B ℓ
  uaRel .UARel._≅_ x y = lsB x y .fst
  uaRel .UARel.ua x y = lsB x y .snd

  Replacement' : is[ ℓ ]Small (Image f)
  Replacement' .fst = Replacement uaRel f
  Replacement' .snd = replacement≃Image uaRel f

isSmallEl : ∀ {ℓ} (x : V⁰ {ℓ}) → is[ ℓ ]Small (El⁰ x)
isSmallEl x = isℓSmallℓ (El⁰ x)

isLocallySmallV∞ : {ℓ : Level} → isLocally[ ℓ ]Small (V∞ {ℓ})
isLocallySmallV∞ {ℓ} = WInd2 (Type ℓ) (λ A → A) (Type ℓ) (λ A → A)
  (λ x y → is[ ℓ ]Small (x ≡ y)) step
  where
    step : {A : Type ℓ} {α : A → V∞ {ℓ}} {B : Type ℓ} {β : B → V∞ {ℓ}}
      → ((a : A) (b : B) → is[ ℓ ]Small (α a ≡ β b))
      → is[ ℓ ]Small (sup-∞ A α ≡ sup-∞ B β)
    step {A} {α} {B} {β} IH =
      isSmall-≃-isSmall
        (isSmallΣ (isℓSmallℓ (A ≃ B))
          (λ e → isSmall-≃-isSmall
                   (isSmallΠ (isℓSmallℓ A) (λ a → IH a (e .fst a)))
                   funExtEquiv))
        (invEquiv ≡V∞-≃-≡Equiv)

isLocallySmallV : {ℓ : Level} → isLocally[ ℓ ]Small (V⁰ {ℓ})
isLocallySmallV {ℓ} x y =
  isSmall-≃-isSmall (isLocallySmallV∞ (x .fst) (y .fst)) (invEquiv ≡V⁰-≃-≡V∞)

module _ {ℓ : Level} where
  union : V⁰ {ℓ} → V⁰ {ℓ}
  union x = fromEmb (idx , elm)
    where
      union-index : Type ℓ
      union-index = Σ (index x) λ a → index (elements x a)
      union-elements : union-index → V⁰
      union-elements (a , b) = elements (elements x a) b
      idx : Type ℓ
      idx = Replacement' isLocallySmallV union-elements .fst
      elm : idx ↪ V⁰
      elm .fst = unrep (uaRel isLocallySmallV union-elements) union-elements
      elm .snd = isEmbeddingUnrep (uaRel isLocallySmallV union-elements) union-elements
