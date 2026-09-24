{-# OPTIONS --lossy-unification #-}
module ACwF.Instances.TarskiPresheaf.Pi.Nat where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Functions.FunExtEquiv
open import Cubical.Data.Sigma
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Instances.Slice.Base
open import TarskiUniverse.Base
open import TarskiUniverse.Properties
open import Utils.TarskiPresheaf
open import ACwF.Base
open import ACwF.Pi
open import TarskiUniverse.Solver
open import Utils.InternalCategory
open import ACwF.Instances.TarskiPresheaf.Base
open import ACwF.Instances.TarskiPresheaf.Pi.Restrict

open Category
open Functor
open NatTrans

module _ {ℓob ℓhom ℓU ℓEl : Level} (C : Category ℓob ℓhom) {U : Type ℓU} (Univ : TarskiUniverse ℓEl U) where
  open TarskiUniverse Univ
  open Algebraic (PRESHEAFU C TU)
  open CwF (Psh-CwF C Univ)

  open [_]CodedCategory
  module PiNat (hasPiTU : hasPi TU) (hasEqTU : hasEq TU) (coded : [ TU ]CodedCategory C) where
    -- Definitions and Restrict, re-exported: Pi.agda opens only this.
    open PiRestrict C Univ hasPiTU hasEqTU coded public

    -- The Γ,A,B-fixed layer again (Restrict.agda has its own): here it carries only
    -- the reindexing of ΠTy along a context map, i.e. the two halves of ΠTyNat.
    module _ {Γ : Ctx} (A : Functor (∫U Γ) (UCat TU)) (B : Functor (∫U (Γ ▹ A)) (UCat TU)) where
      -- Πtype and Πcode at this A and B, so they can be used unqualified below.
      open PiFam A B

      -- ΠTyNat, part 1/2: agreement of the *index* functor P under reindexing
      -- along a context map σ : Δ ⟶ Γ, as opposed to `restrict` (Restrict.agda), which
      -- reindexes along a morphism of ∫U Γ within one fixed context. σ acts as
      -- ∫U-hom σ .F-ob (I , ρ) = (I , σ .N-ob I ρ): it never moves the C-index
      -- I, so unlike `restrict` there is no Jφ-style change of fibre
      -- category needed — Fib I is shared by both sides on the nose, and only
      -- the ρ-component has to be reindexed, via σ's own naturality square.
      module _ {Δ : Ctx} (σ : Δ ⟶ Γ) where
        -- P-agreement: the fibre of ΠTy A B reindexed along σ is, on the nose (no
        -- transport, unlike restrict/PPath in Restrict.agda), the fibre of
        -- ΠTy (A [ σ ]Ty) _ at x. This is ΠTyNat's part 1/2; part 2/2 is the
        -- matching statement for the Q functor, right below. κσ (Definitions.agda)
        -- is σ's naturality square read off at a fibre object s lying over x.
        PPathσ : (x : ∫U Δ .ob)
               → (A ∘F κ Γ) ∘F ι {Γ} (∫U-hom σ .F-ob x) ≡ ((A ∘F ∫U-hom σ) ∘F κ Δ) ∘F ι {Δ} x
        PPathσ x = Functor≡
          (λ s → cong (A .F-ob) (ΣPathP (refl , κσ σ x s)))
          (λ {s} {t} m → F-hom-PathP A _ _ (ΣPathP (refl , κσ σ x s)) (ΣPathP (refl , κσ σ x t)) refl)

        -- ΠTyNat, part 2/2: κ▹ is natural in σ, i.e. the two ways of building the
        -- fibre of the Q functor (reindex-then-take-κ▹, vs. take-κ▹-then-reindex)
        -- agree, over PPathσ. Mirrors WPath/QPath (Restrict.agda), but since there is no
        -- Jφ-style change of fibre category here (see PPathσ), W₀σ/W₁σ need no
        -- ∫U-base precomposition layer — they are the two composites directly.
        module _ (x : ∫U Δ .ob) where
          W₀σ : Functor (∫U ((A ∘F κ Γ) ∘F ι {Γ} (∫U-hom σ .F-ob x))) (∫U (Γ ▹ A))
          W₀σ = κ▹ Γ A ∘F ∫ι (∫U-hom σ .F-ob x) (A ∘F κ Γ)

          W₁σ : Functor (∫U (((A ∘F ∫U-hom σ) ∘F κ Δ) ∘F ι {Δ} x)) (∫U (Γ ▹ A))
          W₁σ = ∫U-hom (σ ⁺) ∘F κ▹ Δ (A [ σ ]Ty) ∘F ∫ι x ((A [ σ ]Ty) ∘F κ Δ)

          -- the ∫U Γ-morphism underlying PPathσ x i ⟪ m ⟫, exactly as `mᵢ` is for
          -- `PPath` in Restrict.agda
          mᵢσ : (i : I) {s t : Fib (x .fst) .ob} (m : (Fib (x .fst) ^op) [ s , t ])
              → ∫U Γ [ (S-ob s , κσ σ x s i) , (S-ob t , κσ σ x t i) ]
          mᵢσ i {s} {t} m = ∫U-Hom-PathP Γ
            (κ Γ .F-hom (ι {Γ} (∫U-hom σ .F-ob x) .F-hom m)) ((∫U-hom σ ∘F κ Δ) .F-hom (ι {Δ} x .F-hom m))
            (ΣPathP (refl , κσ σ x s)) (ΣPathP (refl , κσ σ x t)) refl i

          -- κ▹ reindexed along PPathσ x: same shape at every i, boundary-checked
          -- against W₀σ/W₁σ below, exactly as WW is for WPath in Restrict.agda.
          WWσ : (i : I) → Functor (∫U (PPathσ x i)) (∫U (Γ ▹ A))
          WWσ i .F-ob (s , v) = S-ob s , pairSigma {B = λ u → A .F-ob (S-ob s , u)} (κσ σ x s i) v
          WWσ i .F-hom (m , p) .fst = m .S-hom
          WWσ i .F-hom (m , p) .snd = ▹witness Γ A (mᵢσ i m) _ _ p
          WWσ i .F-id = ∫U-Hom-PathP (Γ ▹ A) _ _ refl refl refl
          WWσ i .F-seq _ _ = ∫U-Hom-PathP (Γ ▹ A) _ _ refl refl refl

          -- the i = 0 boundary is refl, exactly like WPath's — there is no
          -- pairSigma-of-pairSigma to unfold on the W₀σ side. The i = 1 boundary
          -- is not: ∫U-hom (σ ⁺) introduces one, so it has to be peeled with
          -- fstPairSigma/sndPairSigma to reach WWσ 1's shape.
          W₁σ-ob : (s : Fib (x .fst) .ob) (v : El (((A [ σ ]Ty) ∘F κ Δ ∘F ι {Δ} x) .F-ob s))
                 → WWσ i1 .F-ob (s , v) ≡ W₁σ .F-ob (s , v)
          W₁σ-ob s v = ΣPathP (refl , sym (congP₂
              (λ i a b → pairSigma {B = λ u → A .F-ob (S-ob s , u)} a b)
              (cong (σ .N-ob (S-ob s)) (fstPairSigma (Δ .F-hom (S-arr s) (x .snd)) v))
              (sndPairSigma (Δ .F-hom (S-arr s) (x .snd)) v)))

          QPathσ : PathP (λ i → Functor (∫U (PPathσ x i)) (∫U (Γ ▹ A))) W₀σ W₁σ
          QPathσ = Functor≡ (λ _ → refl) (λ _ → refl)
                 ◁ (λ i → WWσ i)
                 ▷ Functor≡ (λ { (s , v) → W₁σ-ob s v })
                            (λ { {s , v} {t , w} (m , p) →
                                   ∫U-Hom-PathP (Γ ▹ A) _ _ (W₁σ-ob s v) (W₁σ-ob t w) refl })

          -- ΠTyNat's two halves (PPathσ x, QPathσ x) combine through
          -- indexed-Πcode: it is an ordinary function of (I , P , Q), so a
          -- dependent path of its arguments gives a dependent path of its
          -- output by congruence — no extra "codes are unique" argument needed.
          ΠcodePathσ : PathP (λ i → TU hasCodeFor indexed-Π (x .fst) (PPathσ x i) (B ∘F QPathσ i))
                             (Πcode (∫U-hom σ .F-ob x)) (PiFam.Πcode (A [ σ ]Ty) (B [ σ ⁺ ]Ty) x)
          ΠcodePathσ = congP₂ (λ i → indexed-Πcode (x .fst)) (PPathσ x) (congP (λ i W → B ∘F W) QPathσ)

          -- ΠTyNat's F-ob clause: codes live in the constant type U, so the
          -- interesting PathP above collapses to a plain path by projecting .fst.
          ΠTyNat-ob : Πcode (∫U-hom σ .F-ob x) .fst ≡ PiFam.Πcode (A [ σ ]Ty) (B [ σ ⁺ ]Ty) x .fst
          ΠTyNat-ob = congP (λ i z → z .fst) ΠcodePathσ

    -- ΠTyNat's naturality clause: restrict itself commutes with reindexing along a
    -- context map.  The Γ-side restrict (along φΓ) and the Δ-side one (along φ)
    -- share the very same Jφ — it depends only on φ's underlying C-morphism, which
    -- ∫U-hom σ preserves — so the two constructions meet at a common value, exactly
    -- as restrictSeq's two routes meet (Restrict.agda), except that the meeting point
    -- additionally has to cross the PPathσ/QPathσ bridge.  U being a set means the *code* paths
    -- never have to be shown to agree, only the values living over them.  This block
    -- sits outside the Γ,A,B-fixed module above precisely so that it can instantiate
    -- `restrict` at both Γ,A,B and Δ,Aσ,Bσ.
    module _ {Γ Δ : Ctx} (A : Functor (∫U Γ) (UCat TU)) (B : Functor (∫U (Γ ▹ A)) (UCat TU))
             (σ : Δ ⟶ Γ) {x y : ∫U Δ .ob} (φ : ∫U Δ [ x , y ]) where
      -- Every statement below compares a Γ-side construction with its Δ-side
      -- counterpart, so both sides are named up front: spelled out inline they run
      -- to three lines apiece and bury the content.
      Aσ : Functor (∫U Δ) (UCat TU)
      Aσ = A [ σ ]Ty
      Bσ : Functor (∫U (Δ ▹ Aσ)) (UCat TU)
      Bσ = B [ σ ⁺ ]Ty
      module atΓ = PiFam A B
      module atΔ = PiFam Aσ Bσ

      xΓ yΓ : ∫U Γ .ob
      xΓ = ∫U-hom σ .F-ob x
      yΓ = ∫U-hom σ .F-ob y
      φΓ : ∫U Γ [ xΓ , yΓ ]
      φΓ = ∫U-hom σ .F-hom φ

      -- e decoded on each side: the Γ-side restrict's input, and the Δ-side's.
      decodePathσ : (e : El (atΓ.Πcode xΓ .fst))
         → PathP (λ i → indexed-Π (x .fst) (PPathσ A B σ x i) (B ∘F QPathσ A B σ x i))
                 (atΓ.Πcode xΓ .snd .fst e)
                 (atΔ.Πcode x .snd .fst (subst El (ΠTyNat-ob A B σ x) e))
      decodePathσ e i =
        ΠcodePathσ A B σ x i .snd .fst (subst-filler El (ΠTyNat-ob A B σ x) e i)

      -- The crux, pointwise.  Both routes factor through a shared value at
      -- s'' = Jφ .F-ob s: the Γ-side reaches it by restrictβ at Γ, the Δ-side by
      -- restrictβ at Δ, and the two are bridged by decodePathσ (crossP below).  U
      -- being a set, the code-path each PathP is stated over is freely swapped by
      -- ElPathP once the endpoints agree, exactly as in restrictSeq (Restrict.agda).
      restrictNatσData : (e : El (atΓ.Πcode xΓ .fst)) (s : Fib (y .fst) .ob)
          {a₀ : El (PPathσ A B σ y i0 .F-ob s)} {a₁ : El (PPathσ A B σ y i1 .F-ob s)}
          (aP : PathP (λ i → El (PPathσ A B σ y i .F-ob s)) a₀ a₁)
        → PathP (λ i → El ((B ∘F QPathσ A B σ y i) .F-ob (s , aP i)))
                (restrict A B φΓ (atΓ.Πcode xΓ .snd .fst e) .fst s a₀)
                (restrict Aσ Bσ φ
                  (atΔ.Πcode x .snd .fst (subst El (ΠTyNat-ob A B σ x) e)) .fst s a₁)
      restrictNatσData e s {a₀} {a₁} aP = ElPathP TU
        (compPathP' {B = El} (compPathP' {B = El} (symP restrictβΓpiece) crossP) restrictβΔpiece)
        where
          s'' : Fib (x .fst) .ob
          s'' = Jφ A B φΓ .F-ob s

          u u' : indexed-Π (x .fst) _ _
          u = atΓ.Πcode xΓ .snd .fst e
          u' = atΔ.Πcode x .snd .fst (subst El (ΠTyNat-ob A B σ x) e)

          -- a₀ dragged back across Γ's own PPath, then forward across PPathσ at s''
          a₀' : El (((A ∘F κ Γ) ∘F ι xΓ) .F-ob s'')
          a₀' = pull A B φΓ s a₀
          a₀'P : PathP (λ i → El (PPath A B φΓ i .F-ob s)) a₀' a₀
          a₀'P = pullP A B φΓ s a₀

          a₀'' : El (((Aσ ∘F κ Δ) ∘F ι x) .F-ob s'')
          a₀'' = transport (λ i → El (PPathσ A B σ x i .F-ob s'')) a₀'
          a₀''P : PathP (λ i → El (PPathσ A B σ x i .F-ob s'')) a₀' a₀''
          a₀''P = transport-filler (λ i → El (PPathσ A B σ x i .F-ob s'')) a₀'

          -- and a₀'' connected to the given a₁, across Δ's own PPath
          pconn : PathP (λ i → El (PPath Aσ Bσ φ i .F-ob s)) a₀'' a₁
          pconn = ElPathP TU
            (compPathP' {B = El} (compPathP' {B = El} (symP a₀''P) a₀'P) aP)

          crossP : PathP (λ i → El ((B ∘F QPathσ A B σ x i) .F-ob (s'' , a₀''P i)))
                         (u .fst s'' a₀') (u' .fst s'' a₀'')
          crossP = congP (λ i g → g s'' (a₀''P i))
                         (congP (λ i z → z .fst) (decodePathσ e))

          restrictβΓpiece : PathP (λ i → El (QPath A B φΓ i .F-ob (s , a₀'P i)))
                                  (u .fst s'' a₀') (restrict A B φΓ u .fst s a₀)
          restrictβΓpiece = restrictβ A B φΓ u s a₀'P

          restrictβΔpiece : PathP (λ i → El (QPath Aσ Bσ φ i .F-ob (s , pconn i)))
                                  (u' .fst s'' a₀'') (restrict Aσ Bσ φ u' .fst s a₁)
          restrictβΔpiece = restrictβ Aσ Bσ φ u' s pconn

      -- restrictNatσData packaged as a genuine PathP of indexed-Πs: funExt over s
      -- (whose type does not vary) and funExtDep over a (whose type does, along
      -- PPathσ A B σ y).
      restrictNatσ : (e : El (atΓ.Πcode xΓ .fst))
        → PathP (λ i → indexed-Π (y .fst) (PPathσ A B σ y i) (B ∘F QPathσ A B σ y i))
                (restrict A B φΓ (atΓ.Πcode xΓ .snd .fst e))
                (restrict Aσ Bσ φ (atΔ.Πcode x .snd .fst (subst El (ΠTyNat-ob A B σ x) e)))
      restrictNatσ e = indexed-Π≡P (PPathσ A B σ y) (congP (λ i W → B ∘F W) (QPathσ A B σ y))
        (λ i s → funExtDep (restrictNatσData e s) i)

      -- restrictNatσ pushed through the code/equivalence pair ΠcodePathσ at y:
      -- ΠTyNat's F-hom clause at e0, paired with e0's canonical image on the Δ side.
      ΠTyNat-hom-canonical : (e0 : El (atΓ.Πcode xΓ .fst))
        → PathP (λ i → El (ΠTyNat-ob A B σ y i))
                (invEq (atΓ.Πcode yΓ .snd) (restrict A B φΓ (atΓ.Πcode xΓ .snd .fst e0)))
                (invEq (atΔ.Πcode y .snd)
                  (restrict Aσ Bσ φ (atΔ.Πcode x .snd .fst (subst El (ΠTyNat-ob A B σ x) e0))))
      ΠTyNat-hom-canonical e0 =
        congP₂ (λ i g d → invEq (g .snd) d) (ΠcodePathσ A B σ y) (restrictNatσ e0)

      -- ΠTyNat's F-hom clause.  funExtDep needs the general case, but any two paths
      -- connecting e0 to e1 over ΠTyNat-ob agree with `subst`'s (U is a set —
      -- ElPathP's idiom, lifted to a whole function), so the general case is the
      -- canonical one transported along fromPathP.
      --
      -- funExtDep's A and B *must* be given here.  Left implicit, the argument's
      -- goal type is checked while they are still metas, and instead of matching
      -- ΠTyNat-hom-canonical's endpoints syntactically the conversion checker starts
      -- normalising ΠTyNat-ob — hence indexed-Πcode, i.e. the entire
      -- reflection-generated code term.  That alone is the difference between this
      -- clause taking ~20s and not terminating.
      ΠTyNat-hom : PathP (λ i → El (ΠTyNat-ob A B σ x i) → El (ΠTyNat-ob A B σ y i))
                   (λ e → invEq (atΓ.Πcode yΓ .snd) (restrict A B φΓ (atΓ.Πcode xΓ .snd .fst e)))
                   (λ e → invEq (atΔ.Πcode y .snd) (restrict Aσ Bσ φ (atΔ.Πcode x .snd .fst e)))
      ΠTyNat-hom = funExtDep {A = λ i → El (ΠTyNat-ob A B σ x i)}
                             {B = λ i _ → El (ΠTyNat-ob A B σ y i)}
        λ {e0} {e1} eP → ΠTyNat-hom-canonical e0 ▷
          cong (λ z → invEq (atΔ.Πcode y .snd) (restrict Aσ Bσ φ (atΔ.Πcode x .snd .fst z)))
               (fromPathP eP)
