{-# OPTIONS --lossy-unification #-}
module ACwF.Instances.TarskiPresheaf.Pi where

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

open Category
open Functor
open NatTrans

module _ {ℓob ℓhom ℓU ℓEl : Level} (C : Category ℓob ℓhom) {U : Type ℓU} (Univ : TarskiUniverse ℓEl U) where
  open TarskiUniverse Univ
  open Algebraic (PRESHEAFU C TU)
  open CwF (Psh-CwF C Univ)

  open [_]CodedCategory
  -- module _ (Γ : Ctx) (A : Functor (∫U Γ) (UCat TU)) where
  --   ▹ob : (x : ∫U Γ .ob) → (a : El (A .F-ob x)) → ∫U (Γ ▹ A) .ob
  --   ▹ob x a = (x .fst) , (pairSigma (x .snd) a)
  --   ▹hom : ∀ {y} {z} → (f : (∫U Γ) [ y , z ]) (a : El (A .F-ob y)) → ∫U (Γ ▹ A) [ ▹ob y a , ▹ob z (A .F-hom f a) ]
  --   ▹hom f a .fst = f .fst
  --   ▹hom {y} {z} f a .snd = cong₂ pairSigma
  --     (cong (Γ .F-hom (f .fst)) (fstPairSigma (y .snd) a) ∙ f .snd)
  --     (compPathP' {B = λ v → El (A .F-ob (z .fst , v))}
  --       (congP (λ i s → A .F-hom (f .fst , refl) s) (sndPairSigma (y .snd) a))
  --       (funExt⁻ (F-hom-PathP A (f .fst , refl) f refl (ΣPathP (refl , f .snd)) refl) a))
  module _ (hasPiTU : hasPi TU) (hasEqTU : hasEq TU) (coded : [ TU ]CodedCategory C) where
    -- The Γ-free fibre of the index category over c₀ : C .ob: the slice C / c₀,
    -- spelled with Σ rather than SliceCat so that solveCode can decompose it.
    -- Restriction is the *opposite* direction, so PresheafU (Fib c₀) TU is exactly
    -- the restriction functor and ∫U applies to it directly.
    private
      FibHom≡ : {c₀ : C .ob} {a b : Σ[ c ∈ C .ob ] C [ c , c₀ ]}
                {m m' : Σ[ h ∈ C [ a .fst , b .fst ] ] (h ⋆⟨ C ⟩ b .snd ≡ a .snd)}
              → m .fst ≡ m' .fst → m ≡ m'
      FibHom≡ = Σ≡Prop λ _ → C .isSetHom _ _

    Fib : C .ob → Category (ℓ-max ℓob ℓhom) ℓhom
    Fib c₀ .ob = Σ[ c ∈ C .ob ] C [ c , c₀ ]
    Fib c₀ .Hom[_,_] a b = Σ[ h ∈ C [ a .fst , b .fst ] ] (h ⋆⟨ C ⟩ b .snd ≡ a .snd)
    Fib c₀ .id = C .id , C .⋆IdL _
    Fib c₀ ._⋆_ m m' = (m .fst ⋆⟨ C ⟩ m' .fst)
      , C .⋆Assoc _ _ _ ∙ cong (λ z → m .fst ⋆⟨ C ⟩ z) (m' .snd) ∙ m .snd
    Fib c₀ .⋆IdL _ = FibHom≡ (C .⋆IdL _)
    Fib c₀ .⋆IdR _ = FibHom≡ (C .⋆IdR _)
    Fib c₀ .⋆Assoc _ _ _ = FibHom≡ (C .⋆Assoc _ _ _)
    Fib c₀ .isSetHom = isSetΣSndProp (C .isSetHom) λ _ → C .isSetHom _ _

    -- Reindexing a fibre object along a C-morphism: postcomposition.
    _⋆*_ : {c₀ c₁ : C .ob} → C [ c₀ , c₁ ] → Fib c₀ .ob → Fib c₁ .ob
    φ ⋆* s = s .fst , (s .snd ⋆⟨ C ⟩ φ)

    private
      -- named so that unification can recover Γ: in the raw Σ, Γ occurs only under
      -- ∫U Γ [ _ , _ ], which reduces away and is not invertible
      IdxHom : (Γ : Ctx) (x x' : ∫U Γ .ob)
             → Fib (x .fst) .ob → Fib (x' .fst) .ob → Type (ℓ-max ℓhom ℓEl)
      IdxHom Γ x x' s s' = Σ[ f ∈ ∫U Γ [ x' , x ] ] (Fib (x' .fst) [ s' , f .fst ⋆* s ])

      IdxHom≡ : (Γ : Ctx) {x x' : ∫U Γ .ob}
                {s : Fib (x .fst) .ob} {s' : Fib (x' .fst) .ob}
                {m m' : IdxHom Γ x x' s s'}
              → m .fst .fst ≡ m' .fst .fst → m .snd .fst ≡ m' .snd .fst → m ≡ m'
      IdxHom≡ Γ {x} p q = ΣPathP
        ( ΣPathP (p , isProp→PathP (λ _ → isSetEl (Γ .F-ob (x .fst)) _ _) _ _)
        , ΣPathP (q , isProp→PathP (λ _ → C .isSetHom _ _) _ _) )

    -- The total index category, oriented like Fib: restriction runs from (x , s) to
    -- (x' , s'), i.e. backwards in Idx, so that PresheafU (Idx Γ) TU is the
    -- restriction functor.  Idx Γ ^op is the twisted arrow category of ∫U Γ,
    -- presented so that the fibre over x mentions only C.
    Idx : Ctx → Category (ℓ-max (ℓ-max ℓob ℓhom) ℓEl) (ℓ-max ℓhom ℓEl)
    Idx Γ .ob = Σ[ x ∈ ∫U Γ .ob ] Fib (x .fst) .ob
    Idx Γ .Hom[_,_] (x' , s') (x , s) = IdxHom Γ x x' s s'
    Idx Γ .id = ∫U Γ .id , C .id , C .⋆IdL _ ∙ C .⋆IdR _
    Idx Γ ._⋆_ m m' =
        (m .fst ⋆⟨ ∫U Γ ⟩ m' .fst)
      , (m .snd .fst ⋆⟨ C ⟩ m' .snd .fst)
      , ( C .⋆Assoc _ _ _
        ∙ cong (λ z → m .snd .fst ⋆⟨ C ⟩ (m' .snd .fst ⋆⟨ C ⟩ z)) (sym (C .⋆Assoc _ _ _))
        ∙ cong (λ z → m .snd .fst ⋆⟨ C ⟩ z) (sym (C .⋆Assoc _ _ _))
        ∙ cong (λ z → m .snd .fst ⋆⟨ C ⟩ (z ⋆⟨ C ⟩ m .fst .fst)) (m' .snd .snd)
        ∙ m .snd .snd )
    Idx Γ .⋆IdL _ = IdxHom≡ Γ (C .⋆IdR _) (C .⋆IdL _)
    Idx Γ .⋆IdR _ = IdxHom≡ Γ (C .⋆IdL _) (C .⋆IdR _)
    Idx Γ .⋆Assoc _ _ _ = IdxHom≡ Γ (sym (C .⋆Assoc _ _ _)) (C .⋆Assoc _ _ _)
    Idx Γ .isSetHom =
      isSetΣ (∫U Γ .isSetHom) λ _ → isSetΣSndProp (C .isSetHom) λ _ → C .isSetHom _ _

    κ : ∀ Γ → Functor (Idx Γ ^op) (∫U Γ)
    κ Γ .F-ob (x , s) = s .fst , Γ .F-hom (s .snd) (x .snd)
    κ Γ .F-hom (F , h , e) .fst = h
    κ Γ .F-hom {x , s} {x' , s'} (F , h , e) .snd =
        sym (funExt⁻ (Γ .F-seq (s .snd) h) (x .snd))
      ∙ cong (Γ .F-hom (h ⋆⟨ C ⟩ s .snd)) (sym (F .snd))
      ∙ sym (funExt⁻ (Γ .F-seq (F .fst) (h ⋆⟨ C ⟩ s .snd)) (x' .snd))
      ∙ cong (λ z → Γ .F-hom z (x' .snd)) (C .⋆Assoc h (s .snd) (F .fst) ∙ e)
    κ Γ .F-id = ∫U-Hom-PathP Γ _ _ refl refl refl
    κ Γ .F-seq _ _ = ∫U-Hom-PathP Γ _ _ refl refl refl

    ι : ∀ {Γ} (x : ∫U Γ .ob) → Functor (Fib (x .fst) ^op) (Idx Γ ^op)
    ι {Γ} x .F-ob s = x , s
    ι {Γ} x .F-hom (f , p) = ∫U Γ .id , f , cong (λ z → f ⋆⟨ C ⟩ z) (C .⋆IdR _) ∙ p
    ι {Γ} x .F-id = IdxHom≡ Γ refl refl
    ι {Γ} x .F-seq f g = IdxHom≡ Γ (sym (C .⋆IdL _)) refl

    -- The witness that (Γ ▹ A) ⟪ n .fst ⟫ transports a pairSigma along n.  Used both
    -- by κ▹ and by the path WPath below, which is κ▹ reindexed along PPath.
    ▹witness : ∀ Γ (A : Functor (∫U Γ) (UCat TU)) {o o' : ∫U Γ .ob}
               (n : ∫U Γ [ o , o' ]) (v : El (A .F-ob o)) (w : El (A .F-ob o'))
             → A .F-hom n v ≡ w
             → (Γ ▹ A) .F-hom (n .fst) (pairSigma (o .snd) v) ≡ pairSigma (o' .snd) w
    ▹witness Γ A {o} {o'} n v w p =
      cong₂ pairSigma
        (cong (Γ .F-hom (n .fst)) (fstPairSigma _ _) ∙ n .snd)
        (compPathP' {B = λ z → El (A .F-ob (o' .fst , z))}
          (congP (λ i z → A .F-hom (n .fst , refl) z) (sndPairSigma _ _))
          ((λ i → F-hom-PathP A (n .fst , refl) n refl (ΣPathP (refl , n .snd)) refl i v) ▷ p))

    κ▹ : ∀ Γ A → Functor (∫U (A ∘F κ Γ)) (∫U (Γ ▹ A))
    κ▹ Γ A .F-ob ((x , c , f) , a) = c , pairSigma (Γ .F-hom f (x .snd)) a
    κ▹ Γ A .F-hom (m , p) .fst = m .snd .fst
    κ▹ Γ A .F-hom (m , p) .snd = ▹witness Γ A (κ Γ .F-hom m) _ _ p
    κ▹ Γ A .F-id = ∫U-Hom-PathP (Γ ▹ A) _ _ refl refl refl
    κ▹ Γ A .F-seq _ _ = ∫U-Hom-PathP (Γ ▹ A) _ _ refl refl refl
    ∫ι  : ∀ {Γ} (x : ∫U Γ .ob) (R : PresheafU (Idx Γ) TU)
      → Functor (∫U (R ∘F ι x)) (∫U R)
    ∫ι x R = ∫U-base (ι x) R

    -- Reindexing a whole fibre along a C-morphism: postcomposition, functorially.
    Fib⋆ : {c₀ c₁ : C .ob} (ψ : C [ c₀ , c₁ ]) → Functor (Fib c₀) (Fib c₁)
    Fib⋆ ψ .F-ob s = ψ ⋆* s
    Fib⋆ ψ .F-hom m = m .fst , sym (C .⋆Assoc _ _ _) ∙ cong (λ z → z ⋆⟨ C ⟩ ψ) (m .snd)
    Fib⋆ ψ .F-id = FibHom≡ refl
    Fib⋆ ψ .F-seq _ _ = FibHom≡ refl

    module _ {Γ : Ctx} (c₀ : C .ob) (P : PresheafU (Fib c₀) TU) (Q : Functor (∫U P) (UCat TU)) where
      indexed-Πdata : Type _
      indexed-Πdata = (s : Fib c₀ .ob) (a : El (P .F-ob s)) → El (Q .F-ob (s , a))
      indexed-Πnat : indexed-Πdata → Type _
      indexed-Πnat w = (s t : Fib c₀ .ob) (m : Fib c₀ [ t , s ]) (a : El (P .F-ob s))
        → Q .F-hom (m , refl) (w s a) ≡  w t (P .F-hom m a)

      indexed-Π : Type _
      indexed-Π = Σ indexed-Πdata indexed-Πnat

      -- Naturality is an equation in El, so it is a proposition: a path of indexed
      -- Πs is exactly a path of its data.  Every law about ΠTy factors through this.
      isProp-indexed-Πnat : (w : indexed-Πdata) → isProp (indexed-Πnat w)
      isProp-indexed-Πnat w =
        isPropΠ4 λ s t m a → isSetEl (Q .F-ob (t , P .F-hom m a)) _ _

      indexed-Π≡ : {u v : indexed-Π} → u .fst ≡ v .fst → u ≡ v
      indexed-Π≡ = Σ≡Prop isProp-indexed-Πnat
      -- indexed-Πcode : TU hasCodeFor indexed-Π
      -- indexed-Πcode = solveCode (coded .isSmallOb ◂ coded .isSmallHom ◂ hasSigmaTU ◂ hasPiTU ◂ hasEqTU ◂ ε)

    -- Restricting an indexed Π along a functor of fibres is pure precomposition:
    -- ∫U-base J P sends (m , refl) to (J ⟪ m ⟫ , refl), which is exactly what the
    -- naturality clause needs, so no transport appears.
    Π-precomp : {Γ : Ctx} {c₀ c₁ : C .ob}
                (P : PresheafU (Fib c₀) TU) (Q : Functor (∫U P) (UCat TU))
                (J : Functor (Fib c₁ ^op) (Fib c₀ ^op))
              → indexed-Π {Γ} c₀ P Q → indexed-Π {Γ} c₁ (P ∘F J) (Q ∘F ∫U-base J P)
    Π-precomp P Q J (w , nat) .fst s a = w (J .F-ob s) a
    Π-precomp P Q J (w , nat) .snd s t m a = nat (J .F-ob s) (J .F-ob t) (J .F-hom m) a

    module _ {Γ : Ctx} (A : Functor (∫U Γ) (UCat TU)) (B : Functor (∫U (Γ ▹ A)) (UCat TU)) where
      Πtype : ∫U Γ .ob → Type _
      Πtype x = indexed-Π {Γ} (x .fst) ((A ∘F κ Γ) ∘F ι x) (B ∘F κ▹ Γ A ∘F ∫ι x (A ∘F κ Γ))
      Πcode : (x : ∫U Γ .ob) → TU hasCodeFor (Πtype x)
      Πcode x = solveCode (coded .isSmallOb ◂ coded .isSmallHom ◂ hasSigmaTU ◂ hasPiTU ◂ hasEqTU ◂ ε)

      -- Restriction along φ : ∫U Γ [ x , y ] reindexes the fibre by (_⋆ φ .fst) …
      module _ {x y : ∫U Γ .ob} (φ : ∫U Γ [ x , y ]) where
        Jφ : Functor (Fib (y .fst) ^op) (Fib (x .fst) ^op)
        Jφ = (Fib⋆ (φ .fst)) ^opF

        -- … and the two fibrewise values of A differ by exactly φ's witness.
        γ : (s : Fib (y .fst) .ob)
          → Γ .F-hom (s .snd ⋆⟨ C ⟩ φ .fst) (x .snd) ≡ Γ .F-hom (s .snd) (y .snd)
        γ s = funExt⁻ (Γ .F-seq (φ .fst) (s .snd)) (x .snd)
            ∙ cong (Γ .F-hom (s .snd)) (φ .snd)

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
           → ∫U Γ [ (s .fst , γ s i) , (t .fst , γ t i) ]
        mᵢ i {s} {t} m = ∫U-Hom-PathP Γ
          (κ Γ .F-hom (ι {Γ} x .F-hom (Jφ .F-hom m))) (κ Γ .F-hom (ι {Γ} y .F-hom m))
          (ΣPathP (refl , γ s)) (ΣPathP (refl , γ t)) refl i

        -- κ▹ reindexed along PPath: same shape at every i, so ▹witness serves all of
        -- them.  Stated without a boundary and glued on afterwards, because F-id and
        -- F-seq only agree with W₀/W₁'s propositionally.
        WW : (i : I) → Functor (∫U (PPath i)) (∫U (Γ ▹ A))
        WW i .F-ob (s , v) = s .fst , pairSigma {B = λ u → A .F-ob (s .fst , u)} (γ s i) v
        WW i .F-hom (m , p) .fst = m .fst
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
        restrict u = transport (λ i → indexed-Π {Γ} (y .fst) (PPath i) (QPath i))
                       (Π-precomp {Γ} _ _ Jφ u)

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
            filler : PathP (λ i → indexed-Π {Γ} (y .fst) (PPath i) (QPath i))
                           (Π-precomp {Γ} _ _ Jφ u) (restrict u)
            filler = transport-filler
                       (λ i → indexed-Π {Γ} (y .fst) (PPath i) (QPath i))
                       (Π-precomp {Γ} _ _ Jφ u)

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
              a₀ = transport (λ i → El (PPath idx (~ i) .F-ob s)) a
              aP : PathP (λ i → El (PPath idx i .F-ob s)) a₀ a
              aP = symP (transport-filler (λ i → El (PPath idx (~ i) .F-ob s)) a)
              -- the fibre reindexing is the identity, up to ⋆IdR
              e : Jφ idx .F-ob s ≡ s
              e = ΣPathP (refl , C .⋆IdR (s .snd))
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
              a₀ = transport (λ i → El (PPath φψ (~ i) .F-ob s)) a
              aP : PathP (λ i → El (PPath φψ i .F-ob s)) a₀ a
              aP = symP (transport-filler (λ i → El (PPath φψ (~ i) .F-ob s)) a)
              b₀ : El ((Py ∘F Jφ ψ) .F-ob s)
              b₀ = transport (λ i → El (PPath ψ (~ i) .F-ob s)) a
              bP : PathP (λ i → El (PPath ψ i .F-ob s)) b₀ a
              bP = symP (transport-filler (λ i → El (PPath ψ (~ i) .F-ob s)) a)
              t : Fib (y .fst) .ob
              t = Jφ ψ .F-ob s
              c₀ : El ((Px ∘F Jφ φ) .F-ob t)
              c₀ = transport (λ i → El (PPath φ (~ i) .F-ob t)) b₀
              cP : PathP (λ i → El (PPath φ i .F-ob t)) c₀ b₀
              cP = symP (transport-filler (λ i → El (PPath φ (~ i) .F-ob t)) b₀)
              -- reindexing by ψ then by φ is reindexing by ψ ⋆ φ, up to ⋆Assoc
              e : Jφ φ .F-ob t ≡ Jφ φψ .F-ob s
              e = ΣPathP (refl , C .⋆Assoc (s .snd) (ψ .fst) (φ .fst))
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

    Psh-Π-structure : Π-Structure _ (Psh-CwF C Univ)
    Psh-Π-structure .Π-Structure.ΠTy A B .F-ob x = Πcode A B x .fst
    Psh-Π-structure .Π-Structure.ΠTy {Γ} A B .F-hom {x} {y} φ e =
      invEq (Πcode A B y .snd) (restrict {Γ} A B {x} {y} φ (Πcode A B x .snd .fst e))
    Psh-Π-structure .Π-Structure.ΠTy {Γ} A B .F-id {x} = funExt λ e →
      cong (invEq (Πcode A B x .snd)) (restrictId {Γ} A B (Πcode A B x .snd .fst e))
      ∙ retEq (Πcode A B x .snd) e
    Psh-Π-structure .Π-Structure.ΠTy {Γ} A B .F-seq {x} {y} {z} φ ψ = funExt λ e →
      cong (invEq (Πcode A B z .snd))
           (restrictSeq {Γ} A B φ ψ (Πcode A B x .snd .fst e))
      ∙ cong (λ v → invEq (Πcode A B z .snd) (restrict {Γ} A B ψ v))
             (sym (secEq (Πcode A B y .snd)
                         (restrict {Γ} A B φ (Πcode A B x .snd .fst e))))
    Psh-Π-structure .Π-Structure.ΠTyNat = {!!}
    Psh-Π-structure .Π-Structure.ΠTmIso = {!!}
    Psh-Π-structure .Π-Structure.ΠTmIsoInvNat = {!!}
