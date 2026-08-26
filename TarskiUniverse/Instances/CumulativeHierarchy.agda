module TarskiUniverse.Instances.CumulativeHierarchy where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Univalence

open import Cubical.Functions.Embedding

open import Cubical.Data.Sigma
open import Cubical.Data.IterativeMultisets.Base
open import Cubical.Data.IterativeSets.Base

open import Cubical.HITs.CumulativeHierarchy
open import Cubical.HITs.PropositionalTruncation

-- Equivalence between the HoTT book V (cumulative hierarchy) and iterative sets.
-- TODO: upstream
-- Largely written by Claude
module _ {ℓ : Level} where

  -- `toV∞` is defined by direct structural recursion on `DeepMonicPresentation`
  -- (a plain, non-HIT inductive type) rather than through `elim`, so it comes
  -- with a genuinely definitional computation rule -- unlike `elim` itself,
  -- which always routes through the canonical monic presentation internally.
  private
    go : {a : V ℓ} → DeepMonicPresentation a → V∞ {ℓ}
    go (dmp ((X , ix , _) , _) rec) = sup-∞ X (λ x → go (rec x))

  toV∞ : V ℓ → V∞ {ℓ}
  toV∞ a = go (V-deeprepr a)

  toV∞-β : (X : Type ℓ) (ix : X → V ℓ) (emb : isEmbedding ix)
         → toV∞ (sett X ix) ≡ sup-∞ X (λ x → toV∞ (ix x))
  toV∞-β X ix emb =
    cong go
      (isPropDeepMonicPresentation (sett X ix)
        (V-deeprepr (sett X ix))
        (dmp ((X , ix , emb) , refl) (λ x → V-deeprepr (ix x))))

  -- unconditional: relates `toV∞ a` to the *canonical* embedding presentation of `a`
  toV∞-canon : (a : V ℓ) → toV∞ a ≡ sup-∞ ⟪ a ⟫ (λ r → toV∞ (⟪ a ⟫↪ r))
  toV∞-canon a = cong toV∞ ⟪ a ⟫-represents ∙ toV∞-β ⟪ a ⟫ ⟪ a ⟫↪ isEmb⟪ a ⟫↪

  toV∞-inj : (a b : V ℓ) → toV∞ a ≡ toV∞ b → a ≡ b
  toV∞-inj a = go-inj (V-deeprepr a)
    where
    go-inj : {a : V ℓ} → DeepMonicPresentation a → (b : V ℓ) → toV∞ a ≡ toV∞ b → a ≡ b
    go-inj {a} (dmp ((X , ix , embX) , pa) recA) b q =
      pa ∙ seteq X ⟪ b ⟫ ix ⟪ b ⟫↪ eqImXB ∙ sym ⟪ b ⟫-represents
      where
      q' : sup-∞ X (λ x → toV∞ (ix x)) ≡ sup-∞ ⟪ b ⟫ (λ r → toV∞ (⟪ b ⟫↪ r))
      q' = sym (toV∞-β X ix embX) ∙ cong toV∞ (sym pa) ∙ q ∙ toV∞-canon b

      e : (X , (λ x → toV∞ (ix x))) ≡Equiv (⟪ b ⟫ , (λ r → toV∞ (⟪ b ⟫↪ r)))
      e = equivFun ≡V∞-≃-≡Equiv q'

      eqImXB : eqImage ix ⟪ b ⟫↪
      eqImXB .fst x =
        ∣ e .fst .fst x , sym (go-inj (recA x) (⟪ b ⟫↪ (e .fst .fst x)) (funExt⁻ (e .snd) x)) ∣₁
      eqImXB .snd r =
        ∣ invEq (e .fst) r
        , go-inj (recA (invEq (e .fst) r)) (⟪ b ⟫↪ r)
            (funExt⁻ (e .snd) (invEq (e .fst) r) ∙ cong (λ z → toV∞ (⟪ b ⟫↪ z)) (secEq (e .fst) r))
        ∣₁

  go≡toV∞ : {a : V ℓ} (da : DeepMonicPresentation a) → go da ≡ toV∞ a
  go≡toV∞ {a} da = cong go (isPropDeepMonicPresentation a da (V-deeprepr a))

  private
    go-iter : {a : V ℓ} (da : DeepMonicPresentation a) → isIterativeSet (go da)
    go-iter (dmp ((X , ix , embX) , _) recA) .fst = isEmbGo
      where
      childIter : (x : X) → isIterativeSet (go (recA x))
      childIter x = go-iter (recA x)

      childV⁰ : X → V⁰ {ℓ}
      childV⁰ x = go (recA x) , childIter x

      injChildV⁰ : {x x' : X} → childV⁰ x ≡ childV⁰ x' → x ≡ x'
      injChildV⁰ {x} {x'} p =
        isEmbedding→Inj embX x x'
          (toV∞-inj (ix x) (ix x')
            (sym (go≡toV∞ (recA x)) ∙ cong fst p ∙ go≡toV∞ (recA x')))

      isEmbChildV⁰ : isEmbedding childV⁰
      isEmbChildV⁰ = injEmbedding isSetV⁰ injChildV⁰

      isEmbGo : isEmbedding (λ x → go (recA x))
      isEmbGo = compEmbedding V⁰↪V∞ (childV⁰ , isEmbChildV⁰) .snd
    go-iter (dmp ((X , ix , embX) , _) recA) .snd x = go-iter (recA x)

  isIterativeSet-toV∞ : (a : V ℓ) → isIterativeSet (toV∞ a)
  isIterativeSet-toV∞ a = go-iter (V-deeprepr a)

  toV⁰ : V ℓ → V⁰ {ℓ}
  toV⁰ a = toV∞ a , isIterativeSet-toV∞ a

  fromV : V⁰ {ℓ} → V ℓ
  fromV (sup-∞ A f , _ , rec) = sett A (λ a → fromV (f a , rec a))

  toV⁰-fromV : (a : V ℓ) → fromV (toV⁰ a) ≡ a
  toV⁰-fromV a = go-round1 (V-deeprepr a)
    where
    go-round1 : {a : V ℓ} (da : DeepMonicPresentation a) → fromV (go da , go-iter da) ≡ a
    go-round1 {a} (dmp ((X , ix , embX) , pa) recA) =
      cong (sett X) (funExt (λ x → go-round1 (recA x))) ∙ sym pa

  private
    toV∞fromV≡fst' : (x : V∞ {ℓ}) (itset : isIterativeSet x) → toV∞ (fromV (x , itset)) ≡ x
    toV∞fromV≡fst' (sup-∞ A f) (embf , recf) =
      toV∞-β A g isEmbG ∙ cong (sup-∞ A) (funExt IH)
      where
      g : A → V ℓ
      g a = fromV (f a , recf a)

      IH : (a : A) → toV∞ (g a) ≡ f a
      IH a = toV∞fromV≡fst' (f a) (recf a)

      isEmbG : isEmbedding g
      isEmbG = injEmbedding setIsSet λ {a} {a'} p → isEmbedding→Inj embf a a'
        (sym (IH a) ∙ cong toV∞ p ∙ IH a')

  toV∞fromV≡fst : (b : V⁰ {ℓ}) → toV∞ (fromV b) ≡ b .fst
  toV∞fromV≡fst (x , itset) = toV∞fromV≡fst' x itset

  fromV-toV⁰ : (b : V⁰ {ℓ}) → toV⁰ (fromV b) ≡ b
  fromV-toV⁰ b = Σ≡Prop isPropIsIterativeSet (toV∞fromV≡fst b)

  Iso-V-V⁰ : Iso (V ℓ) (V⁰ {ℓ})
  Iso-V-V⁰ .Iso.fun = toV⁰
  Iso-V-V⁰ .Iso.inv = fromV
  Iso-V-V⁰ .Iso.sec = fromV-toV⁰
  Iso-V-V⁰ .Iso.ret = toV⁰-fromV

  V≃V⁰ : V ℓ ≃ V⁰ {ℓ}
  V≃V⁰ = isoToEquiv Iso-V-V⁰

  V≡V⁰ : V ℓ ≡ V⁰ {ℓ}
  V≡V⁰ = ua V≃V⁰

-- The Tarski universe instance for the cumulative hierarchy
module _ {ℓ : Level} where

  open import TarskiUniverse.Instances.IterativeSets renaming ( BareTarskiUniverseV to BareTarskiUniverseV⁰
                                                              ; TarskiUniverseV     to TarskiUniverseV⁰
                                                              ; hasPiV              to hasPiV⁰ )
  open import TarskiUniverse.Base

  BareTarskiUniverseV : BareTarskiUniverse ℓ (V ℓ)
  BareTarskiUniverseV = subst⁻ (BareTarskiUniverse ℓ) V≡V⁰ (BareTarskiUniverseV⁰ ℓ)
  
  TarskiUniverseV : TarskiUniverse ℓ (V ℓ)
  TarskiUniverseV = subst⁻ (TarskiUniverse ℓ) V≡V⁰ (TarskiUniverseV⁰ ℓ)

  -- TODO: implement hasPiV : hasPi BareTarskiUniverseV, this is a bit more tedious but should be easy using the SIP
