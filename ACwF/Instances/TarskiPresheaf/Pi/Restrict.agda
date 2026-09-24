{-# OPTIONS --lossy-unification #-}
module ACwF.Instances.TarskiPresheaf.Pi.Restrict where

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
open import ACwF.Instances.TarskiPresheaf.Pi.Definitions

open Category
open Functor
open NatTrans

module _ {ℓob ℓhom ℓU ℓEl : Level} (C : Category ℓob ℓhom) {U : Type ℓU} (Univ : TarskiUniverse ℓEl U) where
  open TarskiUniverse Univ
  open Algebraic (PRESHEAFU C TU)
  open CwF (Psh-CwF C Univ)

  open [_]CodedCategory
  module PiRestrict (hasPiTU : hasPi TU) (hasEqTU : hasEq TU) (coded : [ TU ]CodedCategory C) where
    -- Fib, Idx, κ, ι, κ▹, ∫ι, Fib⋆ and indexed-Π with this module's parameters
    -- already applied, and re-exported so that the files downstream of this one
    -- need a single open rather than one per layer.
    open PiDefs C Univ hasPiTU hasEqTU coded public

    -- Restricting an indexed Π along a functor of fibres is pure precomposition:
    -- ∫U-base J P sends (m , refl) to (J ⟪ m ⟫ , refl), which is exactly what the
    -- naturality clause needs, so no transport appears.
    Π-precomp : {I I' : C .ob}
                (P : PresheafU (Fib I) TU) (Q : Functor (∫U P) (UCat TU))
                (Jf : Functor (Fib I' ^op) (Fib I ^op))
              → indexed-Π I P Q → indexed-Π I' (P ∘F Jf) (Q ∘F ∫U-base Jf P)
    Π-precomp P Q Jf (w , nat) .fst s a = w (Jf .F-ob s) a
    Π-precomp P Q Jf (w , nat) .snd s t m a = nat (Jf .F-ob s) (Jf .F-ob t) (Jf .F-hom m) a

    module _ {Γ : Ctx} (A : Functor (∫U Γ) (UCat TU)) (B : Functor (∫U (Γ ▹ A)) (UCat TU)) where
      -- Πtype and Πcode at this A and B, so they can be used unqualified below.
      open PiFam A B

      -- Restriction along φ : ∫U Γ [ x , y ] reindexes the fibre by (_⋆ φ .fst) …
      module _ {x y : ∫U Γ .ob} (φ : ∫U Γ [ x , y ]) where
        Jφ : Functor (Fib (y .fst) ^op) (Fib (x .fst) ^op)
        Jφ = (Fib⋆ (φ .fst)) ^opF

        -- … and the two fibrewise values of A differ by exactly φ's witness.
        γ : (s : Fib (y .fst) .ob)
          → Γ .F-hom (S-arr s ⋆⟨ C ⟩ φ .fst) (x .snd) ≡ Γ .F-hom (S-arr s) (y .snd)
        γ s = funExt⁻ (Γ .F-seq (φ .fst) (S-arr s)) (x .snd)
            ∙ cong (Γ .F-hom (S-arr s)) (φ .snd)

        PPath : ((A ∘F κ Γ) ∘F ι x) ∘F Jφ ≡ (A ∘F κ Γ) ∘F ι y
        PPath = Functor≡
          (λ s → cong (A .F-ob) (ΣPathP (refl , γ s)))
          (λ {s} {t} m → F-hom-PathP A _ _ (ΣPathP (refl , γ s)) (ΣPathP (refl , γ t)) refl)

        W₀ : Functor (∫U (((A ∘F κ Γ) ∘F ι x) ∘F Jφ)) (∫U (Γ ▹ A))
        W₀ = (κ▹ Γ A ∘F ∫ι x (A ∘F κ Γ)) ∘F ∫U-base Jφ ((A ∘F κ Γ) ∘F ι x)

        W₁ : Functor (∫U ((A ∘F κ Γ) ∘F ι y)) (∫U (Γ ▹ A))
        W₁ = κ▹ Γ A ∘F ∫ι y (A ∘F κ Γ)

        -- the ∫U Γ-morphism underlying PPath i ⟪ m ⟫
        mᵢ : (i : I) {s t : Fib (y .fst) .ob} (m : (Fib (y .fst) ^op) [ s , t ])
           → ∫U Γ [ (S-ob s , γ s i) , (S-ob t , γ t i) ]
        mᵢ i {s} {t} m = ∫U-Hom-PathP Γ
          (κ Γ .F-hom (ι {Γ} x .F-hom (Jφ .F-hom m))) (κ Γ .F-hom (ι {Γ} y .F-hom m))
          (ΣPathP (refl , γ s)) (ΣPathP (refl , γ t)) refl i

        -- κ▹ reindexed along PPath: same shape at every i, so ▹witness serves all of
        -- them.  Stated without a boundary and glued on afterwards, because F-id and
        -- F-seq only agree with W₀/W₁'s propositionally.
        WW : (i : I) → Functor (∫U (PPath i)) (∫U (Γ ▹ A))
        WW i .F-ob (s , v) = S-ob s , pairSigma {B = λ u → A .F-ob (S-ob s , u)} (γ s i) v
        WW i .F-hom (m , p) .fst = m .S-hom
        WW i .F-hom (m , p) .snd = ▹witness Γ A (mᵢ i m) _ _ p
        WW i .F-id = ∫U-Hom-PathP (Γ ▹ A) _ _ refl refl refl
        WW i .F-seq _ _ = ∫U-Hom-PathP (Γ ▹ A) _ _ refl refl refl

        WPath : PathP (λ i → Functor (∫U (PPath i)) (∫U (Γ ▹ A))) W₀ W₁
        WPath = Functor≡ (λ _ → refl) (λ _ → refl)
              ◁ (λ i → WW i)
              ▷ Functor≡ (λ _ → refl) (λ _ → refl)

        QPath : PathP (λ i → Functor (∫U (PPath i)) (UCat TU))
                      ((B ∘F κ▹ Γ A ∘F ∫ι x (A ∘F κ Γ)) ∘F ∫U-base Jφ ((A ∘F κ Γ) ∘F ι x))
                      (B ∘F κ▹ Γ A ∘F ∫ι y (A ∘F κ Γ))
        QPath = sym F-assoc ◁ congP (λ i W → B ∘F W) WPath

        -- Restriction along φ: precomposition (free), then transport across the gap
        -- between the reindexed fibre and the fibre at y.
        restrict : Πtype x → Πtype y
        restrict u = transport (λ i → indexed-Π (y .fst) (PPath i) (QPath i))
                       (Π-precomp _ _ Jφ u)

        -- β-rule for restrict, stated as a PathP over the coercion rather than a
        -- subst: U is a set, so the use site can reindex it onto whichever path it
        -- finds convenient.  This is the only place the transport is ever computed.
        restrictβ : (u : Πtype x) (s : Fib (y .fst) .ob)
                    {a₀ : El ((((A ∘F κ Γ) ∘F ι x) ∘F Jφ) .F-ob s)}
                    {a₁ : El (((A ∘F κ Γ) ∘F ι y) .F-ob s)}
                    (p : PathP (λ i → El (PPath i .F-ob s)) a₀ a₁)
                  → PathP (λ i → El (QPath i .F-ob (s , p i)))
                          (u .fst (Jφ .F-ob s) a₀)
                          (restrict u .fst s a₁)
        restrictβ u s p i = filler i .fst s (p i)
          where
            filler : PathP (λ i → indexed-Π (y .fst) (PPath i) (QPath i))
                           (Π-precomp _ _ Jφ u) (restrict u)
            filler = transport-filler
                       (λ i → indexed-Π (y .fst) (PPath i) (QPath i))
                       (Π-precomp _ _ Jφ u)

        -- `a` dragged back across PPath, together with the filler connecting the
        -- two.  restrictβ takes an arbitrary path, because some callers feed it a
        -- composite; but the common case is this canonical one, so it is named
        -- once here instead of being respelled at each use site.
        pull : (s : Fib (y .fst) .ob) (a : El (((A ∘F κ Γ) ∘F ι y) .F-ob s))
             → El ((((A ∘F κ Γ) ∘F ι x) ∘F Jφ) .F-ob s)
        pull s a = transport (λ i → El (PPath (~ i) .F-ob s)) a

        pullP : (s : Fib (y .fst) .ob) (a : El (((A ∘F κ Γ) ∘F ι y) .F-ob s))
              → PathP (λ i → El (PPath i .F-ob s)) (pull s a) a
        pullP s a = symP (transport-filler (λ i → El (PPath (~ i) .F-ob s)) a)

      -- Fib⋆ (C .id) is the identity only up to ⋆IdR, so even at φ = id the
      -- transport is real work.  restrictβ reduces it to a path in U, and U is a
      -- set, so it can be reindexed onto the path coming from ⋆IdR itself.
      restrictId : {x : ∫U Γ .ob} (u : Πtype x) → restrict (∫U Γ .id) u ≡ u
      restrictId {x} u = indexed-Π≡ (x .fst) Px Qx (funExt λ s → funExt λ a → goal s a)
        where
          idx : ∫U Γ [ x , x ]
          idx = ∫U Γ .id
          Px : PresheafU (Fib (x .fst)) TU
          Px = (A ∘F κ Γ) ∘F ι x
          Qx : Functor (∫U Px) (UCat TU)
          Qx = B ∘F κ▹ Γ A ∘F ∫ι x (A ∘F κ Γ)
          goal : (s : Fib (x .fst) .ob) (a : El (Px .F-ob s))
               → restrict idx u .fst s a ≡ u .fst s a
          goal s a =
            restrict idx u .fst s a ≡⟨ sym (fromPathP (restrictβ idx u s aP)) ⟩
            mid                     ≡⟨ fromPathP c' ⟩
            u .fst s a ∎
            where
              a₀ : El ((Px ∘F Jφ idx) .F-ob s)
              a₀ = pull idx s a
              aP : PathP (λ i → El (PPath idx i .F-ob s)) a₀ a
              aP = pullP idx s a
              -- the fibre reindexing is the identity, up to ⋆IdR
              e : Jφ idx .F-ob s ≡ s
              e = λ i → sliceob (C .⋆IdR (S-arr s) i)
              ap : PathP (λ i → El (Px .F-ob (e i))) a₀ a
              ap = ElPathP TU aP
              c : PathP (λ i → El (Qx .F-ob (e i , ap i)))
                        (u .fst (Jφ idx .F-ob s) a₀) (u .fst s a)
              c i = u .fst (e i) (ap i)
              c' : PathP (λ i → El (QPath idx i .F-ob (s , aP i)))
                         (u .fst (Jφ idx .F-ob s) a₀) (u .fst s a)
              c' = ElPathP TU c
              -- both routes from `u .fst (Jφ idx .F-ob s) a₀` meet here
              mid : El (Qx .F-ob (s , a))
              mid = transport (λ i → El (QPath idx i .F-ob (s , aP i)))
                              (u .fst (Jφ idx .F-ob s) a₀)

      -- Fib⋆ is functorial only up to ⋆Assoc, so composing two restrictions is
      -- again a transport question.  Both sides are routed back to one common
      -- starting element and compared there; U is a set, so the two routes may be
      -- reindexed onto a single path of codes.
      restrictSeq : {x y z : ∫U Γ .ob} (φ : ∫U Γ [ x , y ]) (ψ : ∫U Γ [ y , z ])
                    (u : Πtype x)
                  → restrict (φ ⋆⟨ ∫U Γ ⟩ ψ) u ≡ restrict ψ (restrict φ u)
      restrictSeq {x} {y} {z} φ ψ u =
        indexed-Π≡ (z .fst) Pz Qz (funExt λ s → funExt λ a → goal s a)
        where
          φψ : ∫U Γ [ x , z ]
          φψ = φ ⋆⟨ ∫U Γ ⟩ ψ
          Px : PresheafU (Fib (x .fst)) TU
          Px = (A ∘F κ Γ) ∘F ι x
          Py : PresheafU (Fib (y .fst)) TU
          Py = (A ∘F κ Γ) ∘F ι y
          Pz : PresheafU (Fib (z .fst)) TU
          Pz = (A ∘F κ Γ) ∘F ι z
          Qx : Functor (∫U Px) (UCat TU)
          Qx = B ∘F κ▹ Γ A ∘F ∫ι x (A ∘F κ Γ)
          Qz : Functor (∫U Pz) (UCat TU)
          Qz = B ∘F κ▹ Γ A ∘F ∫ι z (A ∘F κ Γ)
          goal : (s : Fib (z .fst) .ob) (a : El (Pz .F-ob s))
               → restrict φψ u .fst s a ≡ restrict ψ (restrict φ u) .fst s a
          goal s a =
            restrict φψ u .fst s a            ≡⟨ sym (fromPathP chainA) ⟩
            mid                               ≡⟨ fromPathP chainB ⟩
            restrict ψ (restrict φ u) .fst s a ∎
            where
              -- `a` transported backwards along each of the three restrictions
              a₀ : El ((Px ∘F Jφ φψ) .F-ob s)
              a₀ = pull φψ s a
              aP : PathP (λ i → El (PPath φψ i .F-ob s)) a₀ a
              aP = pullP φψ s a
              b₀ : El ((Py ∘F Jφ ψ) .F-ob s)
              b₀ = pull ψ s a
              bP : PathP (λ i → El (PPath ψ i .F-ob s)) b₀ a
              bP = pullP ψ s a
              t : Fib (y .fst) .ob
              t = Jφ ψ .F-ob s
              c₀ : El ((Px ∘F Jφ φ) .F-ob t)
              c₀ = pull φ t b₀
              cP : PathP (λ i → El (PPath φ i .F-ob t)) c₀ b₀
              cP = pullP φ t b₀
              -- reindexing by ψ then by φ is reindexing by ψ ⋆ φ, up to ⋆Assoc
              e : Jφ φ .F-ob t ≡ Jφ φψ .F-ob s
              e = λ i → sliceob (C .⋆Assoc (S-arr s) (ψ .fst) (φ .fst) i)
              dP : PathP (λ i → El (Px .F-ob (e i))) c₀ a₀
              dP = ElPathP TU (compPathP' {B = El} (compPathP' {B = El} cP bP) (symP aP))
              start : El (Qx .F-ob (Jφ φ .F-ob t , c₀))
              start = u .fst (Jφ φ .F-ob t) c₀
              cc : PathP (λ i → El (Qx .F-ob (e i , dP i)))
                         start (u .fst (Jφ φψ .F-ob s) a₀)
              cc i = u .fst (e i) (dP i)
              famA : Qx .F-ob (Jφ φ .F-ob t , c₀) ≡ Qz .F-ob (s , a)
              famA = (λ i → Qx .F-ob (e i , dP i))
                   ∙ (λ i → QPath φψ i .F-ob (s , aP i))
              chainA : PathP (λ i → El (famA i)) start (restrict φψ u .fst s a)
              chainA = compPathP' {B = El} cc (restrictβ φψ u s aP)
              chainB : PathP (λ i → El (famA i))
                             start (restrict ψ (restrict φ u) .fst s a)
              chainB = ElPathP TU (compPathP' {B = El}
                         (restrictβ φ u t cP)
                         (restrictβ ψ (restrict φ u) s bP))
              -- both routes out of `start` meet here
              mid : El (Qz .F-ob (s , a))
              mid = transport (λ i → El (famA i)) start


      -- ΠTy itself.  It is a plain definition rather than copatterns on the
      -- Π-Structure record because Pi/Tm.agda has to mention `Tm Γ (ΠTy A B)`,
      -- and a record defined by copatterns cannot be referred to from inside its
      -- own definition.  Pi.agda's ΠTy field is literally this.
      ΠTy : Ty Γ
      ΠTy .F-ob x = Πcode x .fst
      ΠTy .F-hom {x} {y} φ e = invEq (Πcode y .snd) (restrict φ (Πcode x .snd .fst e))
      ΠTy .F-id {x} = funExt λ e →
        cong (invEq (Πcode x .snd)) (restrictId (Πcode x .snd .fst e))
        ∙ retEq (Πcode x .snd) e
      ΠTy .F-seq {x} {y} {z} φ ψ = funExt λ e →
        cong (invEq (Πcode z .snd)) (restrictSeq φ ψ (Πcode x .snd .fst e))
        ∙ cong (λ v → invEq (Πcode z .snd) (restrict ψ v))
               (sym (secEq (Πcode y .snd) (restrict φ (Πcode x .snd .fst e))))
