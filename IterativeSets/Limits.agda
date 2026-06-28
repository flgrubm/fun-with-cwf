module IterativeSets.Limits where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Sigma

open import Cubical.Data.IterativeSets.Base
open import Cubical.Data.IterativeSets.Sigma
open import Cubical.Data.IterativeSets.Pi
open import Cubical.Data.IterativeSets.Identity

open Iso

private
  variable
    ℓ : Level

module _ (Ob  : V⁰ {ℓ})
         (Hom : El⁰ Ob → El⁰ Ob → V⁰ {ℓ})
         (J₀  : El⁰ Ob → V⁰ {ℓ})
         (Jm  : {x y : El⁰ Ob} → El⁰ (Hom x y) → El⁰ (J₀ x) → El⁰ (J₀ y))
         where

  limit⁰ : V⁰ {ℓ}
  limit⁰ =
    Σ⁰ (Π⁰ Ob J₀)
       (λ s → Π⁰ Ob (λ x → Π⁰ Ob (λ y → Π⁰ (Hom x y)
                (λ m → Id⁰ (J₀ y) (Jm m (s x)) (s y)))))

  Cone : Type ℓ
  Cone =
    Σ[ s ∈ ((d : El⁰ Ob) → El⁰ (J₀ d)) ]
      ({x y : El⁰ Ob} (m : El⁰ (Hom x y)) → Jm m (s x) ≡ s y)

  Iso-El⁰-limit⁰-Cone : Iso (El⁰ limit⁰) Cone
  Iso-El⁰-limit⁰-Cone .fun (s , p) = s , λ {x} {y} m → p x y m
  Iso-El⁰-limit⁰-Cone .inv (s , p) = s , λ x y m → p {x} {y} m
  Iso-El⁰-limit⁰-Cone .sec _       = refl
  Iso-El⁰-limit⁰-Cone .ret _       = refl
