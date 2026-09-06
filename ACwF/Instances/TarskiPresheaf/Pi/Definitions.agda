module ACwF.Instances.TarskiPresheaf.Pi.Definitions where

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
  module PiDefs (hasPiTU : hasPi TU) (hasEqTU : hasEq TU) (coded : [ TU ]CodedCategory C) where
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

      indexed-Πcode : TU hasCodeFor indexed-Π
      indexed-Πcode = solveCode (coded .isSmallOb ◂ coded .isSmallHom ◂ hasSigmaTU ◂ hasPiTU ◂ hasEqTU ◂ ε)

    module PiFam {Γ : Ctx} (A : Functor (∫U Γ) (UCat TU)) (B : Functor (∫U (Γ ▹ A)) (UCat TU)) where
      Πtype : ∫U Γ .ob → Type _
      Πtype x = indexed-Π {Γ} (x .fst) ((A ∘F κ Γ) ∘F ι x) (B ∘F κ▹ Γ A ∘F ∫ι x (A ∘F κ Γ))
      Πcode : (x : ∫U Γ .ob) → TU hasCodeFor (Πtype x)
      Πcode x = indexed-Πcode {Γ} (x .fst) ((A ∘F κ Γ) ∘F ι x) (B ∘F κ▹ Γ A ∘F ∫ι x (A ∘F κ Γ))
