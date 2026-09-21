{-# OPTIONS --lossy-unification #-}
module ACwF.Instances.TarskiPresheaf.Pi.TmNat where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Functions.FunExtEquiv
open import Cubical.Data.Sigma
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import TarskiUniverse.Base
open import TarskiUniverse.Properties
open import Utils.TarskiPresheaf
open import ACwF.Base
open import ACwF.Pi
open import TarskiUniverse.Solver
open import Utils.InternalCategory
open import ACwF.Instances.TarskiPresheaf.Base
open import ACwF.Instances.TarskiPresheaf.Pi.Tm

open Category
open Functor
open NatTrans

module _ {ℓob ℓhom ℓU ℓEl : Level} (C : Category ℓob ℓhom) {U : Type ℓU} (Univ : TarskiUniverse ℓEl U) where
  open TarskiUniverse Univ
  open Algebraic (PRESHEAFU C TU)
  open CwF (Psh-CwF C Univ)

  open [_]CodedCategory
  module PiTmNat (hasPiTU : hasPi TU) (hasEqTU : hasEq TU) (coded : [ TU ]CodedCategory C) where
    -- Definitions, Restrict, Nat and Tm, re-exported: Pi.agda opens only this.
    open PiTm C Univ hasPiTU hasEqTU coded public

    -- ΠTmIsoInvNat: lam commutes with substitution.  Split off from Tm.agda for
    -- the same reason Tm.agda is split off from Nat.agda — it is by far the most
    -- expensive declaration in the Π construction, and as part of Tm.agda every
    -- edit to it paid for app, lam and both round trips as well.
    --
    -- Like the block at the end of Nat.agda it sits outside the Γ,A,B-fixed
    -- layer, so that lamData can be instantiated at both Γ,A,B and Δ,Aσ,Bσ.  The
    -- assembly is exactly ΠTyNat-hom-canonical's — push a dependent path of
    -- indexed-Πs through ΠcodePathσ by congP₂ — and the content is lamNatσData,
    -- which like lamRestrict is just f .N-ob run along a path of
    -- ∫U (Γ ▹ A)-objects: here κσ's naturality square, glued to W₁σ-ob's
    -- pairSigma repackaging.
    module _ {Γ Δ : Ctx} (A : Functor (∫U Γ) (UCat TU))
             (B : Functor (∫U (Γ ▹ A)) (UCat TU))
             (f : Tm (Γ ▹ A) B) (σ : Δ ⟶ Γ) where
      private
        lamNatσData : (x : ∫U Δ .ob) (s : Fib (x .fst) .ob)
            {a₀ : El (PPathσ A B σ x i0 .F-ob s)} {a₁ : El (PPathσ A B σ x i1 .F-ob s)}
            (aP : PathP (λ i → El (PPathσ A B σ x i .F-ob s)) a₀ a₁)
          → PathP (λ i → El ((B ∘F QPathσ A B σ x i) .F-ob (s , aP i)))
                  (lamData A B f (∫U-hom σ .F-ob x) s a₀)
                  (lamData (A [ σ ]Ty) (B [ σ ⁺ ]Ty) (f [ σ ⁺ ]Tm) x s a₁)
        lamNatσData x s {a₀} {a₁} aP = ElPathP TU c
          where
            obP : Path (∫U (Γ ▹ A) .ob)
                       (s .fst , pairSigma {B = λ u → A .F-ob (s .fst , u)}
                                   (κσ σ x s i0) a₀)
                       (W₁σ A B σ x .F-ob (s , a₁))
            obP = (λ i → s .fst , pairSigma {B = λ u → A .F-ob (s .fst , u)}
                                    (κσ σ x s i) (aP i))
                ∙ W₁σ-ob A B σ x s a₁
            c : PathP (λ i → El (B .F-ob (obP i)))
                      (lamData A B f (∫U-hom σ .F-ob x) s a₀)
                      (lamData (A [ σ ]Ty) (B [ σ ⁺ ]Ty) (f [ σ ⁺ ]Tm) x s a₁)
            c i = f .N-ob (obP i) (isContrElUnit .fst)

        lamNatσ : (x : ∫U Δ .ob)
          → PathP (λ i → indexed-Π (x .fst) (PPathσ A B σ x i) (B ∘F QPathσ A B σ x i))
                  (lamElt A B f (∫U-hom σ .F-ob x))
                  (lamElt (A [ σ ]Ty) (B [ σ ⁺ ]Ty) (f [ σ ⁺ ]Tm) x)
        lamNatσ x = indexed-Π≡P (PPathσ A B σ x)
                      (congP (λ i W → B ∘F W) (QPathσ A B σ x))
                      (λ i s → funExtDep (lamNatσData x s) i)

        -- ΠTyNat's own path, named so that the type and the body of
        -- ΠTmIsoInvNat-at below refer to one elaboration of it rather than two.
        --
        -- This single declaration is ~2m35 of this file's ~2m41, and the cost is
        -- the *signature*, not the proof.  Measured, everything else fixed: the
        -- proof alone 6s; plus the PathP type with Functor≡ written inline and a
        -- hole for the body 10s; plus this name given a signature, >2m30.  A
        -- signature forces Functor≡'s F and G to be *checked* against written-out
        -- functors, and `(ΠTy A B) [ σ ]Ty ⟅ c ⟆ ≡ Πcode … .fst` is dischargeable
        -- only by unfolding ΠTy through indexed-Πcode — the whole macro-generated
        -- term — once per c under a binder.  Left inline in a type the same
        -- endpoints are metas *solved* by unification instead, where
        -- --lossy-unification skips F-id/F-seq and it costs seconds.
        --
        -- Both ways out are blocked: dropping the signature leaves F and G
        -- unsolved, and so does passing `_` for makeNatTransPathP's q, so the
        -- conversion must be paid somewhere.  Paying it once here rather than
        -- once in the type and again in the body took this file from ~4m45 to
        -- ~2m41.  A real fix would have to keep ΠTy's F-ob from mentioning
        -- indexed-Πcode at all — cf. the note on making indexed-Πcode opaque in
        -- CLAUDE.md.
        ΠTyNatσ : (ΠTy A B) [ σ ]Ty ≡ ΠTy (A [ σ ]Ty) (B [ σ ⁺ ]Ty)
        ΠTyNatσ = Functor≡ (ΠTyNat-ob A B σ) (ΠTyNat-hom A B σ)

      ΠTmIsoInvNat-at :
        PathP (λ i → Tm Δ (ΠTyNatσ i))
              (lam A B f [ σ ]Tm) (lam (A [ σ ]Ty) (B [ σ ⁺ ]Ty) (f [ σ ⁺ ]Tm))
      ΠTmIsoInvNat-at = makeNatTransPathP refl ΠTyNatσ
        (λ i x u → invEq (ΠcodePathσ A B σ x i .snd) (lamNatσ x i))
