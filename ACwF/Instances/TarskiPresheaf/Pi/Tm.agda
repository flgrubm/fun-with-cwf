{-# OPTIONS --lossy-unification #-}
module ACwF.Instances.TarskiPresheaf.Pi.Tm where

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
open import ACwF.Instances.TarskiPresheaf.Pi.Nat

open Category
open Functor
open NatTrans

module _ {ℓob ℓhom ℓU ℓEl : Level} (C : Category ℓob ℓhom) {U : Type ℓU} (Univ : TarskiUniverse ℓEl U) where
  open TarskiUniverse Univ
  open Algebraic (PRESHEAFU C TU)
  open CwF (Psh-CwF C Univ)

  open [_]CodedCategory
  module PiTm (hasPiTU : hasPi TU) (hasEqTU : hasEq TU) (coded : [ TU ]CodedCategory C) where
    -- Definitions, Restrict and Nat, re-exported.
    open PiNat C Univ hasPiTU hasEqTU coded public

    module _ {Γ : Ctx} (A : Functor (∫U Γ) (UCat TU)) (B : Functor (∫U (Γ ▹ A)) (UCat TU)) where
      open PiFam A B

      -- λ-abstraction, data clause.  The fibre of ΠTy over x at a slice object s
      -- is `El (B .F-ob (S-ob s , pairSigma (Γ .F-hom (S-arr s) ρ) a))` — which is
      -- *definitionally* where f already takes its value — so this needs no
      -- transport whatsoever.  Everything hard about lam is in its two naturality
      -- obligations, not here.
      lamData : (f : Tm (Γ ▹ A) B) (x : ∫U Γ .ob)
              → indexed-Πdata (x .fst) ((A ∘F κ Γ) ∘F ι x)
                              (B ∘F κ▹ Γ A ∘F ∫ι x (A ∘F κ Γ))
      lamData f x s a =
        f .N-ob (S-ob s , pairSigma (Γ .F-hom (S-arr s) (x .snd)) a) (isContrElUnit .fst)

      -- … and its naturality clause is just f's own naturality, read off at the
      -- ∫U (Γ ▹ A)-morphism that κ▹ ∘ ∫ι produces.  Again no transport: the
      -- source and target of that morphism are definitionally lamData's two sides.
      lamNat : (f : Tm (Γ ▹ A) B) (x : ∫U Γ .ob)
             → indexed-Πnat (x .fst) ((A ∘F κ Γ) ∘F ι x)
                            (B ∘F κ▹ Γ A ∘F ∫ι x (A ∘F κ Γ))
                            (lamData f x)
      lamNat f x s t m a = sym (funExt⁻ (f .N-hom _) (isContrElUnit .fst))

      lamElt : (f : Tm (Γ ▹ A) B) (x : ∫U Γ .ob) → Πtype x
      lamElt f x = lamData f x , lamNat f x

      -- The whole content of lam's naturality: λ-abstraction commutes with
      -- restriction.  Same shape as restrictId (Restrict.agda) — restrictβ moves
      -- the transport out of the way, and what is left is `f .N-ob` applied along
      -- a path of ∫U (Γ ▹ A)-objects, namely γ paired with the pull filler.
      lamRestrict : (f : Tm (Γ ▹ A) B) {x y : ∫U Γ .ob} (φ : ∫U Γ [ x , y ])
                  → restrict A B φ (lamElt f x) ≡ lamElt f y
      lamRestrict f {x} {y} φ =
        indexed-Π≡ (y .fst) Py Qy (funExt λ s → funExt λ a → goal s a)
        where
          Px : PresheafU (Fib (x .fst)) TU
          Px = (A ∘F κ Γ) ∘F ι x
          Py : PresheafU (Fib (y .fst)) TU
          Py = (A ∘F κ Γ) ∘F ι y
          Qy : Functor (∫U Py) (UCat TU)
          Qy = B ∘F κ▹ Γ A ∘F ∫ι y (A ∘F κ Γ)
          goal : (s : Fib (y .fst) .ob) (a : El (Py .F-ob s))
               → restrict A B φ (lamElt f x) .fst s a ≡ lamData f y s a
          goal s a =
            restrict A B φ (lamElt f x) .fst s a
              ≡⟨ sym (fromPathP (restrictβ A B φ (lamElt f x) s aP)) ⟩
            mid
              ≡⟨ fromPathP c' ⟩
            lamData f y s a ∎
            where
              a₀ : El ((Px ∘F Jφ A B φ) .F-ob s)
              a₀ = pull A B φ s a
              aP : PathP (λ i → El (PPath A B φ i .F-ob s)) a₀ a
              aP = pullP A B φ s a
              c : PathP (λ i → El (B .F-ob (S-ob s
                    , pairSigma {B = λ u → A .F-ob (S-ob s , u)} (γ A B φ s i) (aP i))))
                        (lamData f x (Jφ A B φ .F-ob s) a₀) (lamData f y s a)
              c i = f .N-ob (S-ob s , pairSigma (γ A B φ s i) (aP i)) (isContrElUnit .fst)
              c' : PathP (λ i → El (QPath A B φ i .F-ob (s , aP i)))
                         (lamData f x (Jφ A B φ .F-ob s) a₀) (lamData f y s a)
              c' = ElPathP TU c
              -- both routes out of `lamData f x (Jφ .F-ob s) a₀` meet here
              mid : El (Qy .F-ob (s , a))
              mid = transport (λ i → El (QPath A B φ i .F-ob (s , aP i)))
                              (lamData f x (Jφ A B φ .F-ob s) a₀)

      -- λ-abstraction.  ΠTy's F-hom is `restrict` conjugated by the code
      -- equivalence, so naturality is lamRestrict with secEq peeling off the
      -- encode/decode round trip that conjugation inserts.
      lam : Tm (Γ ▹ A) B → Tm Γ (ΠTy A B)
      lam f .N-ob x _ = invEq (Πcode x .snd) (lamElt f x)
      lam f .N-hom {x} {y} φ = funExt λ _ → sym
        ( cong (λ v → invEq (Πcode y .snd) (restrict A B φ v))
               (secEq (Πcode x .snd) (lamElt f x))
        ∙ cong (invEq (Πcode y .snd)) (lamRestrict f φ) )

      -- Application evaluates the Π at the *identity* slice.  Γ .F-id holds only
      -- propositionally, so — unlike lam — this direction genuinely transports:
      -- `za` is the argument dragged back along it, and `zpath` carries the
      -- result home from κ▹'s repackaged context to z itself.
      module _ (z : ∫U (Γ ▹ A) .ob) where
        private
          Elᴬ : El (Γ .F-ob (z .fst)) → Type ℓEl
          Elᴬ u = El (A .F-ob (z .fst , u))

        zρ : El (Γ .F-ob (z .fst))
        zρ = fstSigma (z .snd)

        zx : ∫U Γ .ob
        zx = z .fst , zρ

        idρ : Γ .F-hom (C .id) zρ ≡ zρ
        idρ = funExt⁻ (Γ .F-id) zρ

        za : Elᴬ (Γ .F-hom (C .id) zρ)
        za = transport (λ i → Elᴬ (idρ (~ i))) (sndSigma (z .snd))

        zaP : PathP (λ i → Elᴬ (idρ i)) za (sndSigma (z .snd))
        zaP = symP (transport-filler (λ i → Elᴬ (idρ (~ i))) (sndSigma (z .snd)))

        -- kept separate from zpath below, and never composed into it: every
        -- object path in this file has to keep a definitionally constant .fst, or
        -- the C-component of an ∫U-Hom-PathP over it stops typechecking.
        zpathSnd : pairSigma {B = λ u → A .F-ob (z .fst , u)}
                     (Γ .F-hom (C .id) zρ) za ≡ z .snd
        zpathSnd = SigmaPathP
          (fstPairSigma _ _ ∙ idρ)
          (compPathP' {B = Elᴬ} (sndPairSigma _ _) zaP)

        zpath : (z .fst , pairSigma {B = λ u → A .F-ob (z .fst , u)}
                            (Γ .F-hom (C .id) zρ) za) ≡ z
        zpath = ΣPathP (refl , zpathSnd)

      module _ (F : Tm Γ (ΠTy A B)) where
        Fu : (x : ∫U Γ .ob) → Πtype x
        Fu x = Πcode x .snd .fst (F .N-ob x (isContrElUnit .fst))

        appRaw : (z : ∫U (Γ ▹ A) .ob)
               → El (B .F-ob (z .fst , pairSigma {B = λ u → A .F-ob (z .fst , u)}
                                        (Γ .F-hom (C .id) (zρ z)) (za z)))
        appRaw z = Fu (zx z) .fst (sliceob (C .id)) (za z)

        appData : (z : ∫U (Γ ▹ A) .ob) → El (B .F-ob z)
        appData z = transport (λ i → El (B .F-ob (zpath z i))) (appRaw z)

        appβ : (z : ∫U (Γ ▹ A) .ob)
             → PathP (λ i → El (B .F-ob (zpath z i))) (appRaw z) (appData z)
        appβ z = transport-filler (λ i → El (B .F-ob (zpath z i))) (appRaw z)

        -- app's naturality.  Three separate facts meet here: F's own naturality
        -- (FuNat — Fu at the target *is* a restrict of Fu at the source), the
        -- indexed-Πnat clause of Fu itself (q1), and restrictβ (q2), mirrored back
        -- to appRaw by q3.  Both routes out of `B ⟪ M₀ ⟫ (appRaw z)` are made to
        -- meet, exactly as in restrictSeq (Restrict.agda); U being a set, the
        -- code-paths never have to be shown equal, only the values over them.
        module _ {z z' : ∫U (Γ ▹ A) .ob} (m : ∫U (Γ ▹ A) [ z , z' ]) where
          private
            g : C [ z' .fst , z .fst ]
            g = m .fst

            -- m's witness, read off on the Γ-part: Base.agda's qbase for q .N-hom
            qbase : Γ .F-hom g (zρ z) ≡ zρ z'
            qbase = sym (fstPairSigma _ _) ∙ cong fstSigma (m .snd)

            ψ : ∫U Γ [ zx z , zx z' ]
            ψ = g , qbase

            Px : PresheafU (Fib (z .fst)) TU
            Px = (A ∘F κ Γ) ∘F ι {Γ} (zx z)

            -- the identity slice at each end...
            s : Fib (z .fst) .ob
            s = sliceob (C .id)
            s' : Fib (z' .fst) .ob
            s' = sliceob (C .id)
            -- ...and s' reindexed backward into Fib (z .fst) — same role as s'' in
            -- Nat.agda's restrictNatσData.
            s'' : Fib (z .fst) .ob
            s'' = Jφ A B ψ .F-ob s'

            m' : Fib (z .fst) [ s'' , s ]
            m' = slicehom (C .id ⋆⟨ C ⟩ g) (C .⋆IdR _)

            -- za z transported along m' agrees with za z', up to PPath: the
            -- argument half of app's naturality, self-contained from the result
            -- half below (Tob onward), which only ever needs zaAgree's type.
            zaAgree : PathP (λ i → El (PPath A B ψ i .F-ob s'))
                            (Px .F-hom m' (za z)) (za z')
            zaAgree = ElPathP TU (compPathP' {B = λ u → El (A .F-ob (z' .fst , u))}
                        (compPathP' {B = λ u → El (A .F-ob (z' .fst , u))} u1 u2)
                        (symP (zaP z')))
              where
                -- Px ⟪ m' ⟫ and A ⟪ g ⟫ are the same map up to where their endpoints
                -- sit: F-hom-PathP says A .F-hom only sees the C-morphism, and u1
                -- below is exactly that fact, bridging the gap ⋆IdL leaves.
                mκ : ∫U Γ [ (z .fst , Γ .F-hom (C .id) (zρ z))
                          , (z' .fst , Γ .F-hom (C .id ⋆⟨ C ⟩ g) (zρ z)) ]
                mκ = κ Γ .F-hom (ι {Γ} (zx z) .F-hom m')

                -- spelled out rather than left as `g , refl`: F-hom-PathP's x'/y' are
                -- otherwise metas that it has to invert srcP/tgtP to recover
                mg : ∫U Γ [ (z .fst , zρ z) , (z' .fst , Γ .F-hom g (zρ z)) ]
                mg = g , refl

                -- Path (∫U Γ .ob), not ≡: inferred from the pairs alone the Σ's second
                -- family stays a meta, and F-hom-PathP then cannot match its endpoints.
                srcP : Path (∫U Γ .ob) (z .fst , Γ .F-hom (C .id) (zρ z)) (z .fst , zρ z)
                srcP i = z .fst , idρ z i
                tgtP : Path (∫U Γ .ob) (z' .fst , Γ .F-hom (C .id ⋆⟨ C ⟩ g) (zρ z))
                                       (z' .fst , Γ .F-hom g (zρ z))
                tgtP i = z' .fst , Γ .F-hom (C .⋆IdL g i) (zρ z)

                -- A's action on za z, computed via mκ and via mg, agree.
                u1 : PathP (λ i → El (A .F-ob (tgtP i)))
                           (A .F-hom mκ (za z))
                           (A .F-hom mg (sndSigma (z .snd)))
                u1 i = F-hom-PathP A mκ mg srcP tgtP (C .⋆IdL g) i (zaP z i)

                -- A's action on mg matches sndSigma (z' .snd), via m's own witness.
                u2 : PathP (λ i → El (A .F-ob (z' .fst , qbase i)))
                           (A .F-hom mg (sndSigma (z .snd))) (sndSigma (z' .snd))
                u2 = compPathP' {B = λ u → El (A .F-ob (z' .fst , u))}
                       (symP (sndPairSigma _ _)) (cong sndSigma (m .snd))

            Tob : ∫U (Γ ▹ A) .ob
            Tob = z' .fst , pairSigma {B = λ u → A .F-ob (z' .fst , u)}
                              (Γ .F-hom (C .id ⋆⟨ C ⟩ g) (zρ z)) (Px .F-hom m' (za z))

            Tpath : Tob ≡ z'
            Tpath = ΣPathP (refl , congP₂
                      (λ i a b → pairSigma {B = λ u → A .F-ob (z' .fst , u)} a b)
                      (γ A B ψ s') zaAgree
                    ∙ zpathSnd z')

            M₀ : ∫U (Γ ▹ A) [ zpath z i0 , Tob ]
            M₀ = (κ▹ Γ A ∘F ∫ι {Γ} (zx z) (A ∘F κ Γ)) .F-hom (m' , refl)

            Mpath : PathP (λ i → ∫U (Γ ▹ A) [ zpath z i , Tpath i ]) M₀ m
            Mpath = ∫U-Hom-PathP (Γ ▹ A) M₀ m (zpath z) Tpath (C .⋆IdL g)

            -- F's naturality, decoded: Fu at zx z' is Fu at zx z restricted along ψ
            FuNat : Fu (zx z') ≡ restrict A B ψ (Fu (zx z))
            FuNat = cong (Πcode (zx z') .snd .fst)
                         (funExt⁻ (F .N-hom ψ) (isContrElUnit .fst))
                  ∙ secEq (Πcode (zx z') .snd) (restrict A B ψ (Fu (zx z)))

            q1 : B .F-hom M₀ (appRaw z) ≡ Fu (zx z) .fst s'' (Px .F-hom m' (za z))
            q1 = Fu (zx z) .snd s s'' m' (za z)

            q2 : PathP (λ i → El (QPath A B ψ i .F-ob (s' , zaAgree i)))
                       (Fu (zx z) .fst s'' (Px .F-hom m' (za z)))
                       (restrict A B ψ (Fu (zx z)) .fst s' (za z'))
            q2 = restrictβ A B ψ (Fu (zx z)) s' zaAgree

            -- the mirror of q1, through F's own naturality (FuNat) rather than Fu's.
            q3 : restrict A B ψ (Fu (zx z)) .fst s' (za z') ≡ appRaw z'
            q3 = cong (λ u → u .fst s' (za z')) (sym FuNat)

            -- the two routes out of B ⟪ M₀ ⟫ (appRaw z)
            viaFu : PathP (λ i → El (B .F-ob (Tpath i)))
                          (B .F-hom M₀ (appRaw z)) (appData z')
            viaFu = ElPathP TU (compPathP' {B = El} (q1 ◁ q2 ▷ q3) (appβ z'))

            viaM : PathP (λ i → El (B .F-ob (Tpath i)))
                         (B .F-hom M₀ (appRaw z)) (B .F-hom m (appData z))
            viaM = congP₂ (λ i mm w → B .F-hom mm w) Mpath (appβ z)

          appNat : appData z' ≡ B .F-hom m (appData z)
          appNat = sym (fromPathP viaFu) ∙ fromPathP viaM

        app : Tm (Γ ▹ A) B
        app .N-ob z _ = appData z
        app .N-hom m = funExt λ _ → appNat m

        -- lam (app F) ≡ F, pointwise on the indexed-Π data.  Same three
        -- ingredients as appNat, at the morphism ψs : x ⟶ zx w that s itself
        -- provides; the only new step is that Jψs lands on s only up to ⋆IdL,
        -- which `et` absorbs.
        module _ {x : ∫U Γ .ob} (s : Fib (x .fst) .ob)
                 (a : El (((A ∘F κ Γ) ∘F ι {Γ} x) .F-ob s)) where
          private
            Elᴬ : El (Γ .F-ob (S-ob s)) → Type ℓEl
            Elᴬ v = El (A .F-ob (S-ob s , v))

            w : ∫U (Γ ▹ A) .ob
            w = S-ob s , pairSigma {B = λ u → A .F-ob (S-ob s , u)}
                           (Γ .F-hom (S-arr s) (x .snd)) a

            ψs : ∫U Γ [ x , zx w ]
            ψs = S-arr s , sym (fstPairSigma _ _)

            s₁ : Fib (zx w .fst) .ob
            s₁ = sliceob {S-ob = S-ob s} (C .id)
            t₁ : Fib (x .fst) .ob
            t₁ = Jφ A B ψs .F-ob s₁

            et : Path (Fib (x .fst) .ob) t₁ s
            et i = sliceob (C .⋆IdL (S-arr s) i)

            a₀ : El ((((A ∘F κ Γ) ∘F ι {Γ} x) ∘F Jφ A B ψs) .F-ob s₁)
            a₀ = pull A B ψs s₁ (za w)
            aP : PathP (λ i → El (PPath A B ψs i .F-ob s₁)) a₀ (za w)
            aP = pullP A B ψs s₁ (za w)

            -- a₀ ↝ za w ↝ sndSigma (w .snd) ↝ a, all inside El (A ⟅ S-ob s , – ⟆)
            aa : PathP (λ i → El (((A ∘F κ Γ) ∘F ι {Γ} x) .F-ob (et i))) a₀ a
            aa = ElPathP TU (compPathP' {B = Elᴬ}
                   (compPathP' {B = Elᴬ} aP (zaP w)) (sndPairSigma _ _))

            cc : PathP (λ i → El ((B ∘F κ▹ Γ A ∘F ∫ι {Γ} x (A ∘F κ Γ))
                                    .F-ob (et i , aa i)))
                       (Fu x .fst t₁ a₀) (Fu x .fst s a)
            cc i = Fu x .fst (et i) (aa i)

            FuNats : Fu (zx w) ≡ restrict A B ψs (Fu x)
            FuNats = cong (Πcode (zx w) .snd .fst)
                          (funExt⁻ (F .N-hom ψs) (isContrElUnit .fst))
                   ∙ secEq (Πcode (zx w) .snd) (restrict A B ψs (Fu x))

            r1 : appRaw w ≡ restrict A B ψs (Fu x) .fst s₁ (za w)
            r1 = cong (λ u → u .fst s₁ (za w)) FuNats

            r2 : PathP (λ i → El (QPath A B ψs i .F-ob (s₁ , aP i)))
                       (Fu x .fst t₁ a₀) (restrict A B ψs (Fu x) .fst s₁ (za w))
            r2 = restrictβ A B ψs (Fu x) s₁ aP

            chain : PathP (λ i → El (B .F-ob (zpath w i))) (appRaw w) (Fu x .fst s a)
            chain = ElPathP TU (compPathP' {B = El} (r1 ◁ symP r2) cc)

          lamAppData : appData w ≡ Fu x .fst s a
          lamAppData = sym (fromPathP (appβ w)) ∙ fromPathP chain

        lamApp : lam app ≡ F
        lamApp = makeNatTransPath (funExt λ x → funExt λ u →
            cong (invEq (Πcode x .snd))
                 (indexed-Π≡ (x .fst) ((A ∘F κ Γ) ∘F ι {Γ} x)
                             (B ∘F κ▹ Γ A ∘F ∫ι {Γ} x (A ∘F κ Γ))
                             (funExt λ s → funExt λ a → lamAppData s a))
          ∙ retEq (Πcode x .snd) (F .N-ob x (isContrElUnit .fst))
          ∙ cong (F .N-ob x) (isContrElUnit .snd u))

      -- app (lam f) ≡ f: the transport that app inserts is undone by running f
      -- itself along zpath, once secEq has peeled lam's encode/decode round trip.
      appLam : (f : Tm (Γ ▹ A) B) → app (lam f) ≡ f
      appLam f = makeNatTransPath (funExt λ z → funExt λ u →
          sym (fromPathP (appβ (lam f) z))
        ∙ cong (transport (λ i → El (B .F-ob (zpath z i))))
               (cong (λ v → v .fst (sliceob (C .id)) (za z))
                     (secEq (Πcode (zx z) .snd) (lamElt f (zx z))))
        ∙ fromPathP (λ i → f .N-ob (zpath z i) (isContrElUnit .fst))
        ∙ cong (f .N-ob z) (isContrElUnit .snd u))

      ΠTmIso-at : Iso (Tm Γ (ΠTy A B)) (Tm (Γ ▹ A) B)
      ΠTmIso-at .Iso.fun = app
      ΠTmIso-at .Iso.inv = lam
      ΠTmIso-at .Iso.sec = appLam
      ΠTmIso-at .Iso.ret = lamApp
