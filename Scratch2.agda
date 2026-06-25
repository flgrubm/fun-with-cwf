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
open import Cubical.HITs.PropositionalTruncation
open import Cubical.Displayed.Base
open import Cubical.Data.Sigma
open import Cubical.Data.W.W
open import Cubical.Data.IterativeSets.Base
open import Cubical.Data.IterativeSets.UnorderedPair.Base
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
  union-index : (x : V⁰ {ℓ}) → Type ℓ
  union-index x = Σ (index x) λ a → index (elements x a)
  union-elements : (x : V⁰) → union-index x → V⁰
  union-elements x (a , b) = elements (elements x a) b

  uar : (x : V⁰ {ℓ}) → UARel V⁰ ℓ
  uar x = uaRel isLocallySmallV (union-elements x)

  ∪⁰ : V⁰ {ℓ} → V⁰ {ℓ}
  ∪⁰ x = fromEmb (idx , elm)
    where
      idx : Type ℓ
      idx = Replacement' isLocallySmallV (union-elements x) .fst
      elm : idx ↪ V⁰
      elm .fst = unrep (uar x) (union-elements x)
      elm .snd = isEmbeddingUnrep (uaRel isLocallySmallV (union-elements x)) (union-elements x)

  union-correct : ∀ x z → (z ∈⁰ (∪⁰ x)) ≃ (∃[ a ∈ index x ] z ∈⁰ elements x a)
  union-correct x z = 
      (z ∈⁰ ∪⁰ x)
    ≃⟨ idEquiv _ ⟩
      fiber (unrep _ _) z
    ≃⟨ invEquiv (propTruncIdempotent≃ (isEmbedding→hasPropFibers (isEmbeddingUnrep (uar x) (union-elements x)) z)) ⟩
      isInImage (unrep (uar x) (union-elements x)) z
    ≃⟨ idEquiv _ ⟩
      ∃[ x₁ ∈ Replacement (uar x) (union-elements x)] unrep (uar x) (union-elements x) x₁ ≡ z
    ≃⟨ propBiimpl→Equiv squash₁ squash₁
         (rec squash₁ λ (r , p) →
           rec squash₁ (λ ((a , b) , q) →
             ∣ a , ∣ b , cong (unrep (uar x) (union-elements x)) q ∙ p ∣₁ ∣₁)
             (isSurjectiveRep (uar x) (union-elements x) r))
         (rec squash₁ λ (a , h) →
           rec squash₁ (λ (b , p) → ∣ rep (a , b) , p ∣₁) h)
      ⟩
      ∃[ a ∈ index x ] ∃[ b ∈ index (elements x a) ] elements (elements x a) b ≡ z
    ≃⟨ propTrunc≃ (Σ-cong-equiv-snd (λ a → propTruncIdempotent≃ (isProp∈⁰ {x = elements x a} {z = z}))) ⟩
      ∃[ a ∈ index x ] z ∈⁰ elements x a
    ■
  
