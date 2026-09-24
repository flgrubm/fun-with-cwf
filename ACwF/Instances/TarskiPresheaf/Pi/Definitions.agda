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
open import Cubical.Categories.Instances.Slice.Base
open import Cubical.Categories.Instances.Slice.Functor using (∑_)
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
    -- The Γ-free fibre of the index category over I : C .ob: the slice C / I.
    -- Restriction is the *opposite* direction, so PresheafU (Fib I) TU is exactly
    -- the restriction functor and ∫U applies to it directly.
    Fib : C .ob → Category (ℓ-max ℓob ℓhom) ℓhom
    Fib I = SliceCat C I

    -- solveCode cannot see inside the records SliceOb/SliceHom, so their codes
    -- are the Σ-codes moved across the evident isos, and passed to it as hints.
    private
      SliceOb-Σ-Iso : {I : C .ob} → Iso (Σ[ J ∈ C .ob ] C [ J , I ]) (SliceOb C I)
      SliceOb-Σ-Iso .Iso.fun (J , f) = sliceob f
      SliceOb-Σ-Iso .Iso.inv s = S-ob s , S-arr s
      SliceOb-Σ-Iso .Iso.sec _ = refl
      SliceOb-Σ-Iso .Iso.ret _ = refl

      sliceObCode : (I : C .ob) → TU hasCodeFor (SliceOb C I)
      sliceObCode I = code .fst , code .snd ∙ₑ isoToEquiv SliceOb-Σ-Iso
        where code : TU hasCodeFor (Σ[ J ∈ C .ob ] C [ J , I ])
              code = solveCode (coded .isSmallOb ◂ coded .isSmallHom ◂ hasSigmaTU ◂ ε)

      sliceHomCode : (I : C .ob) (a b : SliceOb C I) → TU hasCodeFor (SliceHom C I a b)
      sliceHomCode I a b = code .fst , code .snd ∙ₑ isoToEquiv (invIso (SliceHom-Σ-Iso C I))
        where code : TU hasCodeFor (Σ[ h ∈ C [ S-ob a , S-ob b ] ] h ⋆⟨ C ⟩ S-arr b ≡ S-arr a)
              code = solveCode (coded .isSmallHom ◂ hasSigmaTU ◂ hasEqTU ◂ ε)

    private
      -- named so that unification can recover Γ: in the raw Σ, Γ occurs only under
      -- ∫U Γ [ _ , _ ], which reduces away and is not invertible
      IdxHom : (Γ : Ctx) (Iρ I'ρ' : ∫U Γ .ob)
             → Fib (Iρ .fst) .ob → Fib (I'ρ' .fst) .ob → Type (ℓ-max ℓhom ℓEl)
      IdxHom Γ (I , ρ) (I' , ρ') s s' =
        Σ[ f ∈ ∫U Γ [ (I' , ρ') , (I , ρ) ] ] (Fib I' [ s' , (∑ f .fst) .F-ob s ])

      IdxHom≡ : (Γ : Ctx) {Iρ I'ρ' : ∫U Γ .ob}
                {s : Fib (Iρ .fst) .ob} {s' : Fib (I'ρ' .fst) .ob}
                {m m' : IdxHom Γ Iρ I'ρ' s s'}
              → m .fst .fst ≡ m' .fst .fst → m .snd .S-hom ≡ m' .snd .S-hom → m ≡ m'
      IdxHom≡ Γ {Iρ} {m = m} {m'} p q = ΣPathP
        ( ∫U-Hom-PathP Γ _ _ refl refl p
        , congP (λ _ → Iso.inv (SliceHom-Σ-Iso C _))
            (ΣPathP (q , isProp→PathP (λ _ → C .isSetHom _ _) _ _)) )

    -- The total index category, oriented like Fib: restriction runs from (Iρ , s) to
    -- (I'ρ' , s'), i.e. backwards in Idx, so that PresheafU (Idx Γ) TU is the
    -- restriction functor.  Idx Γ ^op is equivalent to, but deliberately not,
    -- the library's TwistedArrowCategory (∫U Γ): there an object is an ∫U Γ-arrow,
    -- carrying an El-equality, whereas here the fibre over Iρ mentions only C.
    Idx : Ctx → Category (ℓ-max (ℓ-max ℓob ℓhom) ℓEl) (ℓ-max ℓhom ℓEl)
    Idx Γ .ob = Σ[ Iρ ∈ ∫U Γ .ob ] Fib (Iρ .fst) .ob
    Idx Γ .Hom[_,_] (I'ρ' , s') (Iρ , s) = IdxHom Γ Iρ I'ρ' s s'
    Idx Γ .id = ∫U Γ .id , slicehom (C .id) (C .⋆IdL _ ∙ C .⋆IdR _)
    Idx Γ ._⋆_ m m' =
        (m .fst ⋆⟨ ∫U Γ ⟩ m' .fst)
      , slicehom (m .snd .S-hom ⋆⟨ C ⟩ m' .snd .S-hom)
        ( C .⋆Assoc _ _ _
        ∙ cong (λ z → m .snd .S-hom ⋆⟨ C ⟩ (m' .snd .S-hom ⋆⟨ C ⟩ z)) (sym (C .⋆Assoc _ _ _))
        ∙ cong (λ z → m .snd .S-hom ⋆⟨ C ⟩ z) (sym (C .⋆Assoc _ _ _))
        ∙ cong (λ z → m .snd .S-hom ⋆⟨ C ⟩ (z ⋆⟨ C ⟩ m .fst .fst)) (m' .snd .S-comm)
        ∙ m .snd .S-comm )
    Idx Γ .⋆IdL _ = IdxHom≡ Γ (C .⋆IdR _) (C .⋆IdL _)
    Idx Γ .⋆IdR _ = IdxHom≡ Γ (C .⋆IdL _) (C .⋆IdR _)
    Idx Γ .⋆Assoc _ _ _ = IdxHom≡ Γ (sym (C .⋆Assoc _ _ _)) (C .⋆Assoc _ _ _)
    Idx Γ .isSetHom =
      isSetΣ (∫U Γ .isSetHom) λ _ → SliceCat C _ .isSetHom

    κ : ∀ Γ → Functor (Idx Γ ^op) (∫U Γ)
    κ Γ .F-ob ((I , ρ) , s) = S-ob s , Γ .F-hom (S-arr s) ρ
    κ Γ .F-hom (F , slicehom h e) .fst = h
    κ Γ .F-hom {(I , ρ) , s} {(I' , ρ') , s'} (F , slicehom h e) .snd =
        sym (funExt⁻ (Γ .F-seq (S-arr s) h) ρ)
      ∙ cong (Γ .F-hom (h ⋆⟨ C ⟩ S-arr s)) (sym (F .snd))
      ∙ sym (funExt⁻ (Γ .F-seq (F .fst) (h ⋆⟨ C ⟩ S-arr s)) ρ')
      ∙ cong (λ z → Γ .F-hom z ρ') (C .⋆Assoc h (S-arr s) (F .fst) ∙ e)
    κ Γ .F-id = ∫U-Hom-PathP Γ _ _ refl refl refl
    κ Γ .F-seq _ _ = ∫U-Hom-PathP Γ _ _ refl refl refl

    -- κ's naturality in a context map σ : Δ ⟶ Γ, read off at a fibre object s
    -- lying over Iρ.  Unlike the fibre reindexing ∑ (φ .fst) that restrict uses
    -- (Restrict.agda), which stays inside one fixed context, σ never moves the
    -- C-index — ∫U-hom σ .F-ob (I , ρ) is (I , σ ρ) — so this single square is
    -- the whole difference between the two sides.  PPathσ (Nat.agda) is built
    -- out of it.
    κσ : {Γ Δ : Ctx} (σ : Δ ⟶ Γ) (Iρ : ∫U Δ .ob) (s : Fib (Iρ .fst) .ob)
       → Γ .F-hom (S-arr s) (σ .N-ob (Iρ .fst) (Iρ .snd))
           ≡ σ .N-ob (S-ob s) (Δ .F-hom (S-arr s) (Iρ .snd))
    κσ σ Iρ s = sym (funExt⁻ (σ .N-hom (S-arr s)) (Iρ .snd))

    ι : ∀ {Γ} (Iρ : ∫U Γ .ob) → Functor (Fib (Iρ .fst) ^op) (Idx Γ ^op)
    ι {Γ} Iρ .F-ob s = Iρ , s
    ι {Γ} Iρ .F-hom (slicehom f p) = ∫U Γ .id , slicehom f (cong (λ z → f ⋆⟨ C ⟩ z) (C .⋆IdR _) ∙ p)
    ι {Γ} Iρ .F-id = IdxHom≡ Γ refl refl
    ι {Γ} Iρ .F-seq f g = IdxHom≡ Γ (sym (C .⋆IdL _)) refl

    -- The witness that (Γ ▹ A) ⟪ n .fst ⟫ transports a pairSigma along n.  Used both
    -- by κ▹ and by the path WPath below, which is κ▹ reindexed along PPath.
    ▹witness : ∀ Γ (A : Functor (∫U Γ) (UCat TU)) {Iρ I'ρ' : ∫U Γ .ob}
               (n : ∫U Γ [ Iρ , I'ρ' ]) (v : El (A .F-ob Iρ)) (w : El (A .F-ob I'ρ'))
             → A .F-hom n v ≡ w
             → (Γ ▹ A) .F-hom (n .fst) (pairSigma (Iρ .snd) v) ≡ pairSigma (I'ρ' .snd) w
    ▹witness Γ A {Iρ} {I'ρ'@(I' , ρ')} n v w p =
      cong₂ pairSigma
        (cong (Γ .F-hom (n .fst)) (fstPairSigma _ _) ∙ n .snd)
        (compPathP' {B = λ z → El (A .F-ob (I' , z))}
          (congP (λ i z → A .F-hom (n .fst , refl) z) (sndPairSigma _ _))
          ((λ i → F-hom-PathP A (n .fst , refl) n refl (ΣPathP (refl , n .snd)) refl i v) ▷ p))

    κ▹ : ∀ Γ A → Functor (∫U (A ∘F κ Γ)) (∫U (Γ ▹ A))
    κ▹ Γ A .F-ob (((I , ρ) , sliceob {J} f) , a) = J , pairSigma (Γ .F-hom f ρ) a
    κ▹ Γ A .F-hom (m , p) .fst = m .snd .S-hom
    κ▹ Γ A .F-hom (m , p) .snd = ▹witness Γ A (κ Γ .F-hom m) _ _ p
    κ▹ Γ A .F-id = ∫U-Hom-PathP (Γ ▹ A) _ _ refl refl refl
    κ▹ Γ A .F-seq _ _ = ∫U-Hom-PathP (Γ ▹ A) _ _ refl refl refl
    ∫ι  : ∀ {Γ} (Iρ : ∫U Γ .ob) (R : PresheafU (Idx Γ) TU)
      → Functor (∫U (R ∘F ι Iρ)) (∫U R)
    ∫ι Iρ R = ∫U-base (ι Iρ) R

    module _ (I : C .ob) (P : PresheafU (Fib I) TU) (Q : Functor (∫U P) (UCat TU)) where
      indexed-Πdata : Type _
      indexed-Πdata = (s : Fib I .ob) (a : El (P .F-ob s)) → El (Q .F-ob (s , a))
      indexed-Πnat : indexed-Πdata → Type _
      indexed-Πnat w = (s t : Fib I .ob) (m : Fib I [ t , s ]) (a : El (P .F-ob s))
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
      indexed-Πcode = solveCode (sliceObCode I ◂ sliceHomCode I ◂ hasSigmaTU ◂ hasPiTU ◂ hasEqTU ◂ ε)

    -- Dependent version of indexed-Π≡, for comparing indexed-Πs over genuinely
    -- different (P , Q) — needed by ΠTyNat (Pi.agda), which relates indexed-Πs
    -- reindexed by a context map to indexed-Πs at the substituted context.
    -- Naturality stays a proposition all along a path of (P , Q), so a PathP of
    -- indexed-Πs is still exactly a PathP of their data.
    indexed-Π≡P : {Iob : C .ob}
                  {P0 P1 : PresheafU (Fib Iob) TU} (Ppath : P0 ≡ P1)
                  {Q0 : Functor (∫U P0) (UCat TU)} {Q1 : Functor (∫U P1) (UCat TU)}
                  (Qpath : PathP (λ i → Functor (∫U (Ppath i)) (UCat TU)) Q0 Q1)
                  {u : indexed-Π Iob P0 Q0} {v : indexed-Π Iob P1 Q1}
                → PathP (λ i → indexed-Πdata Iob (Ppath i) (Qpath i)) (u .fst) (v .fst)
                → PathP (λ i → indexed-Π Iob (Ppath i) (Qpath i)) u v
    indexed-Π≡P {Iob = Iob} Ppath Qpath dataP = ΣPathP
      (dataP , isProp→PathP (λ i → isProp-indexed-Πnat Iob (Ppath i) (Qpath i) (dataP i)) _ _)

    module PiFam {Γ : Ctx} (A : Functor (∫U Γ) (UCat TU)) (B : Functor (∫U (Γ ▹ A)) (UCat TU)) where
      Πtype : ∫U Γ .ob → Type _
      Πtype Iρ = indexed-Π (Iρ .fst) ((A ∘F κ Γ) ∘F ι Iρ) (B ∘F κ▹ Γ A ∘F ∫ι Iρ (A ∘F κ Γ))
      Πcode : (Iρ : ∫U Γ .ob) → TU hasCodeFor (Πtype Iρ)
      Πcode Iρ = indexed-Πcode (Iρ .fst) ((A ∘F κ Γ) ∘F ι Iρ) (B ∘F κ▹ Γ A ∘F ∫ι Iρ (A ∘F κ Γ))
