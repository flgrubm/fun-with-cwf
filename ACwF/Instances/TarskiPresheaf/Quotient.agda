{-# OPTIONS --lossy-unification #-}
module ACwF.Instances.TarskiPresheaf.Quotient where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.HITs.SetQuotients as SQ using (eq/)
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import TarskiUniverse.Base
open import TarskiUniverse.Properties
open import Utils.TarskiPresheaf
open import Utils.TarskiQuotient
open import ACwF.Base
open import ACwF.Quotient
open import ACwF.Instances.TarskiPresheaf.Base

open Category
open Functor
open NatTrans

-- | Quotient types in presheaves valued in a Tarski universe with set
-- quotients.  They are pointwise: at a stage `(c , ρ)` of `∫ Γ`, `QTy A R`
-- is the quotient of `A (c , ρ)` by `R` at the re-paired triple (as in the
-- families model, `ACwF.Instances.TarskiUniverse`), and a morphism acts on
-- classes by the action of `A` (`quotMap`), which preserves the relation
-- because `R` is a presheaf too.  At each stage `c` everything is the
-- fibrewise construction of `Utils.TarskiQuotient` over the code `Γ c`; what
-- is left here is naturality.  Elimination is stagewise elimination, which
-- is natural because every element is merely a class.
module _ {ℓob ℓhom ℓU ℓEl : Level} (C : Category ℓob ℓhom) {U : Type ℓU} (Univ : TarskiUniverse ℓEl U) where
  open TarskiUniverse Univ
  open Algebraic (PRESHEAFU C TU)
  open CwF (Psh-CwF C Univ)
  open Fibrewise Univ

  private variable
    Γ Δ : Ctx

  -- | The action of a type on a morphism of `C`, along a dependent path of
  -- its argument: it only depends on the underlying morphism of `C`.
  homO : (B : Ty Γ) {c d : C .ob} (f : C [ d , c ])
         {x x' : El (Γ .F-ob c)} {y y' : El (Γ .F-ob d)}
         (e : Γ .F-hom f x ≡ y) (e' : Γ .F-hom f x' ≡ y')
         {b : El (B .F-ob (c , x))} {b' : El (B .F-ob (c , x'))}
       → Over (λ x → B .F-ob (c , x)) b b'
       → -------------------------------------------------------------------------
         Over (λ y → B .F-ob (d , y)) (B .F-hom (f , e) b) (B .F-hom (f , e') b')
  homO {Γ = Γ} B {c} {d} f {y = y} {y'} e e' (overPath q h) =
    overPath base (λ i → F-hom-PathP B (f , e) (f , e') (λ j → c , q j) (λ j → d , base j) refl i (h i))
    where
      base : y ≡ y'
      base = sym e ∙∙ cong (Γ .F-hom f) q ∙∙ e'

  module Psh-Quot (TU-Quot : hasQuotient TU) where
    open hasQuotient TU-Quot

    -- | At stage `c`: the fibrewise quotient over the code `Γ c`.
    module St {Γ : Ctx} {A : Ty Γ} (R : Ty (Γ ▹ A ▹ A [ p ]Ty)) (c : C .ob) =
      QuotRel TU-Quot (λ x → A .F-ob (c , x)) (λ w → R .F-ob (c , w))

    -- | Re-pairing commutes with the action of a morphism `(f , e)` of `∫ Γ`:
    -- the three components of the moved triple are those of the triple of
    -- the moved components, by the β-laws of `pairSigma`.
    module _ {A : Ty Γ} {c d : C .ob} (f : C [ d , c ])
             {ρ : El (Γ .F-ob c)} {ρ' : El (Γ .F-ob d)} (e : Γ .F-hom f ρ ≡ ρ')
             (a b : El (A .F-ob (c , ρ))) where
      private
        Aᶜ : El (Γ .F-ob c) → U
        Aᶜ x = A .F-ob (c , x)

        Aᵈ : El (Γ .F-ob d) → U
        Aᵈ y = A .F-ob (d , y)

        moved : El ((Γ ▹ A ▹ A [ p ]Ty) .F-ob d)
        moved = (Γ ▹ A ▹ A [ p ]Ty) .F-hom f (pair² Aᶜ (ρ , a , b))

        -- the second component of the moved triple
        moved₂ : Over Aᵈ (unpair² Aᵈ moved .snd .fst) (A .F-hom (f , e) a)
        moved₂ =  congO Aᵈ {f = fstSigma} sndSigma (fstPairSigma _ _)
               ∙O sndPairO Aᵈ _ _
               ∙O homO A f refl e (unpair²-pair²O₂ Aᶜ (ρ , a , b))

        -- the third component of the moved triple
        moved₃ : Over Aᵈ (unpair² Aᵈ moved .snd .snd) (A .F-hom (f , e) b)
        moved₃ =  overPath (cong fstSigma (fstPairSigma _ _)) (sndPairSigma _ _)
               ∙O homO A f _ e (unpair²-pair²O₃ Aᶜ (ρ , a , b))

        unpair²-moved : unpair² Aᵈ moved ≡ (ρ' , A .F-hom (f , e) a , A .F-hom (f , e) b)
        unpair²-moved = ΣPathP (moved₂ .Over.base , ΣPathP (moved₂ .Over.path ,
                                                             over Aᵈ moved₃ (moved₂ .Over.base)))

      pair²Nat : moved ≡ pair² Aᵈ (ρ' , A .F-hom (f , e) a , A .F-hom (f , e) b)
      pair²Nat = sym (pair²-unpair² Aᵈ moved) ∙ cong (pair² Aᵈ) unpair²-moved

    -- | The quotient type: pointwise, acting on classes by `A`.
    Psh-QTy : (A : Ty Γ) (R : Ty (Γ ▹ A ▹ A [ p ]Ty))
            → -------------------------------------------
              Ty Γ
    Psh-QTy A R .F-ob (c , ρ)  = St.Q R c ρ
    Psh-QTy A R .F-hom (f , e) =
      quotMap TU-Quot (A .F-hom (f , e)) (λ a b r → eq/ _ _ (R .F-hom (f , pair²Nat {A = A} f e a b) r))
    Psh-QTy A R .F-id          = funExt (quotMap-id TU-Quot (funExt⁻ (A .F-id)))
    Psh-QTy A R .F-seq f g     = funExt (quotMap-seq TU-Quot (funExt⁻ (A .F-seq f g)))

    -- | `σ ⁺²`: `sub²` at each stage.  Its naturality is that of `(σ ⁺) ⁺`,
    -- carried along the path `Psh-⁺²-ob`.
    module _ {A : Ty Γ} (σ : Δ ⟶ Γ) where
      private
        Dom : I → Ctx
        Dom i = Δ ▹ A [ σ ]Ty ▹ [p][⁺]Ty A σ i

        Cod : Ctx
        Cod = Γ ▹ A ▹ A [ p ]Ty

      Psh-⁺²-ob : (i : I) (c : C .ob) → El (Dom i .F-ob c) → El (Cod .F-ob c)
      Psh-⁺²-ob i c w = sub²-filler (λ x → A .F-ob (c , x)) (σ .N-ob c) i
                                    (fstSigma (fstSigma w)) (sndSigma (fstSigma w)) (sndSigma w)

      private
        HomTy : I → Type (ℓ-max (ℓ-max ℓob ℓhom) ℓEl)
        HomTy i = {c d : C .ob} (f : C [ d , c ])
                → Path (El (Dom i .F-ob c) → El (Cod .F-ob d))
                       (λ w → Psh-⁺²-ob i d (Dom i .F-hom f w)) (λ w → Cod .F-hom f (Psh-⁺²-ob i c w))

      Psh-⁺² : Δ ▹ A [ σ ]Ty ▹ A [ σ ]Ty [ p ]Ty ⟶ Cod
      Psh-⁺² .N-ob  = Psh-⁺²-ob i1
      Psh-⁺² .N-hom = transport (λ i → HomTy i) (_⁺ {A = A [ p ]Ty} (σ ⁺) .N-hom)

      Psh-⁺²≡ : PathP (λ i → Dom i ⟶ Cod) ((σ ⁺) ⁺) Psh-⁺²
      Psh-⁺²≡ = makeNatTransPathP (λ i → Dom i) refl (λ i → Psh-⁺²-ob i)

      -- the relations of `QTy A R [ σ ]` and `QTy (A [ σ ]) (R [ σ ⁺² ])` at a
      -- stage agree (`relSub²`)
      relNat : (R : Ty Cod) (c : C .ob) (ρ : El (Δ .F-ob c))
             → ---------------------------------------------------------------------------------
               Path (El (A .F-ob (c , σ .N-ob c ρ)) → El (A .F-ob (c , σ .N-ob c ρ)) → U)
                    (λ a b → R .F-ob (c , pair² (λ x → A .F-ob (c , x)) (σ .N-ob c ρ , a , b)))
                    (λ a b → R .F-ob (c , Psh-⁺² .N-ob c (pair² (λ x → A .F-ob (c , σ .N-ob c x)) (ρ , a , b))))
      relNat R c ρ = relSub² (λ x → A .F-ob (c , x)) (σ .N-ob c) (λ w → R .F-ob (c , w)) ρ

    -- | The two quotients agree on objects by `relNat`, and act on classes
    -- by the same map; the proofs that it preserves the relations agree,
    -- being paths in a set quotient.
    module _ {A : Ty Γ} (R : Ty (Γ ▹ A ▹ A [ p ]Ty)) (σ : Δ ⟶ Γ) where
      private
        lhs rhs : Ty Δ
        lhs = Psh-QTy A R [ σ ]Ty
        rhs = Psh-QTy (A [ σ ]Ty) (R [ Psh-⁺² σ ]Ty)

      -- the two quotients agree at each stage, by `relNat`
      Psh-QTyNat-ob : (x : ∫U Δ .ob) → lhs .F-ob x ≡ rhs .F-ob x
      Psh-QTyNat-ob x = cong (Quot _) (relNat σ R (x .fst) (x .snd))

      private
        QTyNat-hom : {x y : ∫U Δ .ob} (f : ∫U Δ [ x , y ])
                   → PathP (λ i → El (Psh-QTyNat-ob x i) → El (Psh-QTyNat-ob y i)) (lhs .F-hom f) (rhs .F-hom f)
        QTyNat-hom f = quotMap-PathP TU-Quot (A .F-hom (∫U-hom σ .F-hom f)) _ _

      Psh-QTyNat : Psh-QTy A R [ σ ]Ty ≡ Psh-QTy (A [ σ ]Ty) (R [ Psh-⁺² σ ]Ty)
      Psh-QTyNat = Functor≡ Psh-QTyNat-ob QTyNat-hom

    -- | Introduction.
    Psh-classTm : {A : Ty Γ} {R : Ty (Γ ▹ A ▹ A [ p ]Ty)}
                → Tm Γ A
                → ----------------
                  Tm Γ (Psh-QTy A R)
    Psh-classTm a .N-ob x u  = classQuot (a .N-ob x u)
    Psh-classTm a .N-hom f   = funExt λ u →
      cong classQuot (funExt⁻ (a .N-hom f) u) ∙ sym (quotMap-class TU-Quot _ _ (a .N-ob _ u))

    -- a class lies over `Psh-QTyNat`
    Psh-classTmNat : {A : Ty Γ} (R : Ty (Γ ▹ A ▹ A [ p ]Ty)) (a : Tm Γ A) (σ : Δ ⟶ Γ)
                   → -----------------------------------------------------------------
                     PathP (λ i → Tm Δ (Psh-QTyNat R σ i))
                           (Psh-classTm {R = R} a [ σ ]Tm) (Psh-classTm {R = R [ Psh-⁺² σ ]Ty} (a [ σ ]Tm))
    Psh-classTmNat R a σ =
      makeNatTransPathP refl (Psh-QTyNat R σ)
        (λ i x u → classQuot {R = relNat σ R (x .fst) (x .snd) i} (a .N-ob (∫U-hom σ .F-ob x) u))

    module _ {A : Ty Γ} (R : Ty (Γ ▹ A ▹ A [ p ]Ty)) where
      -- the class of the last variable commutes with the action of `f`
      clsNat : {c d : C .ob} (f : C [ d , c ]) (w : El ((Γ ▹ A) .F-ob c))
             → ------------------------------------------------------------------------------
               St.cls R d ((Γ ▹ A) .F-hom f w) ≡ (Γ ▹ Psh-QTy A R) .F-hom f (St.cls R c w)
      clsNat {c} {d} f w = pairO (St.Q R d) snd≡
        where
          snd≡ : Over (St.Q R d) (classQuot (sndSigma ((Γ ▹ A) .F-hom f w)))
                                  (Psh-QTy A R .F-hom (f , refl) (sndSigma (St.cls R c w)))
          snd≡ =   mapO (λ _ → classQuot) (sndPairO (λ y → A .F-ob (d , y)) _ _)
                ∙O overPath refl (sym (quotMap-class TU-Quot _ _ (sndSigma w)))
                ∙O homO (Psh-QTy A R) f refl refl (symO (sndPairO (St.Q R c) _ _))

      Psh-classSub : Γ ▹ A ⟶ Γ ▹ Psh-QTy A R
      Psh-classSub .N-ob c  = St.cls R c
      Psh-classSub .N-hom f = funExt (clsNat f)

      private
        -- the type of the second component along the β-law of the pair
        clsβ : (x : ∫U (Γ ▹ A) .ob) → St.Q R (x .fst) (fstSigma (St.cls R (x .fst) (x .snd))) ≡ St.Q R (x .fst) (fstSigma (x .snd))
        clsβ x i = St.Q R (x .fst) (fstPairSigma {B = St.Q R (x .fst)} (fstSigma (x .snd)) (classQuot (sndSigma (x .snd))) i)

      -- `q [ classSub ]` is the class of `q`: the β-law of the pair, then
      -- `relNat` at `p`
      q[classSub]-ob : (x : ∫U (Γ ▹ A) .ob)
                     → ---------------------------------------------------------------
                       PathP (λ i → El ((clsβ x ∙ Psh-QTyNat-ob {A = A} R (p {A = A}) x) i))
                             (sndSigma (St.cls R (x .fst) (x .snd))) (classQuot (sndSigma (x .snd)))
      q[classSub]-ob x =
        compPathP' {B = El} {p = clsβ x} {q = Psh-QTyNat-ob {A = A} R (p {A = A}) x}
          (sndPairSigma _ _) (λ i → classQuot {R = relNat {A = A} (p {A = A}) R (x .fst) (x .snd) i} (sndSigma (x .snd)))

    -- | Elimination: the fibrewise eliminator at each stage, its naturality,
    -- and its β- and η-laws.
    module _ {A : Ty Γ} (R : Ty (Γ ▹ A ▹ A [ p ]Ty)) (P : Ty (Γ ▹ Psh-QTy A R)) where
      private
        Q : Ty Γ
        Q = Psh-QTy A R

        Pᶜ : (c : C .ob) → El ((Γ ▹ Q) .F-ob c) → U
        Pᶜ c s = P .F-ob (c , s)

        Cases : Type (ℓ-max (ℓ-max ℓob ℓhom) ℓEl)
        Cases = Tm (Γ ▹ A) (P [ Psh-classSub R ]Ty)

        cases : Cases → (c : C .ob) (u : El Unit) (w : El ((Γ ▹ A) .F-ob c)) → El (Pᶜ c (St.cls R c w))
        cases m c u w = m .N-ob (c , w) u

      -- `m` respects `R` at every stage
      Psh-Respects : Cases → Type (ℓ-max ℓob ℓEl)
      Psh-Respects m = (c : C .ob) (u : El Unit) → St.Respects R c (Pᶜ c) (cases m c u)

      private
        elimOb : (m : Cases) → Psh-Respects m → (c : C .ob) (u : El Unit) (s : El ((Γ ▹ Q) .F-ob c)) → El (Pᶜ c s)
        elimOb m r c u = St.elim R c (Pᶜ c) (cases m c u) (r c u)

        elimOb-β : (m : Cases) (r : Psh-Respects m) (c : C .ob) (u : El Unit) (w : El ((Γ ▹ A) .F-ob c))
                 → elimOb m r c u (St.cls R c w) ≡ cases m c u w
        elimOb-β m r c u = St.elim-β R c (Pᶜ c) (cases m c u) (r c u)

        module _ (m : Cases) (r : Psh-Respects m) {c d : C .ob} (f : C [ d , c ]) (u : El Unit) where

          -- naturality at a class: both sides are the cases, by the
          -- β-law and the naturality of the cases
          elimNat-cls : (w : El ((Γ ▹ A) .F-ob c))
                      → elimOb m r d u ((Γ ▹ Q) .F-hom f (St.cls R c w))
                      ≡ P .F-hom (f , refl) (elimOb m r c u (St.cls R c w))
          elimNat-cls w = over≡ (Pᶜ d)
            (  congO (Pᶜ d) (elimOb m r d u) (sym (clsNat R f w))
            ∙O overPath refl (elimOb-β m r d u ((Γ ▹ A) .F-hom f w))
            ∙O overPath refl (funExt⁻ (m .N-hom {c , w} {d , (Γ ▹ A) .F-hom f w} (f , refl)) u)
            ∙O homO P f _ refl (overPath refl (sym (elimOb-β m r c u w))))

          -- naturality along `(f , refl)` at every element, from the case of
          -- classes by `cls-ext`
          elimNat-pt : (s : El ((Γ ▹ Q) .F-ob c))
                     → elimOb m r d u ((Γ ▹ Q) .F-hom f s) ≡ P .F-hom (f , refl) (elimOb m r c u s)
          elimNat-pt = funExt⁻ (St.cls-ext R c (λ s → Pᶜ d ((Γ ▹ Q) .F-hom f s))
                                  (λ s → elimOb m r d u ((Γ ▹ Q) .F-hom f s))
                                  (λ s → P .F-hom (f , refl) (elimOb m r c u s))
                                  elimNat-cls)

          -- naturality along any morphism `(f , e)` of `∫ (Γ ▹ Q)`, from the case `e = refl`
          elimNat : {s : El ((Γ ▹ Q) .F-ob c)} {s' : El ((Γ ▹ Q) .F-ob d)} (e : (Γ ▹ Q) .F-hom f s ≡ s')
                  → elimOb m r d u s' ≡ P .F-hom (f , e) (elimOb m r c u s)
          elimNat {s} e = over≡ (Pᶜ d)
            (  congO (Pᶜ d) (elimOb m r d u) (sym e)
            ∙O overPath refl (elimNat-pt s)
            ∙O homO P f refl e (overPath refl refl))

      Psh-quotElim : (m : Cases) → Psh-Respects m → Tm (Γ ▹ Q) P
      Psh-quotElim m r .N-ob (c , s) u = elimOb m r c u s
      Psh-quotElim m r .N-hom (f , e)  = funExt λ u → elimNat m r f u e

      -- the β-law: the eliminator at classes is the cases
      Psh-quotElim-β : (m : Cases) (r : Psh-Respects m)
                     → ------------------------------------------
                       Psh-quotElim m r [ Psh-classSub R ]Tm ≡ m
      Psh-quotElim-β m r = makeNatTransPath (funExt λ x → funExt λ u → elimOb-β m r (x .fst) u (x .snd))

      -- the η-law: a term is the eliminator of its instance at classes
      Psh-quotElim-η : (t : Tm (Γ ▹ Q) P) (r : Psh-Respects (t [ Psh-classSub R ]Tm))
                     → ---------------------------------------------------------
                       Psh-quotElim (t [ Psh-classSub R ]Tm) r ≡ t
      Psh-quotElim-η t r = makeNatTransPath (funExt λ x → funExt λ u →
        funExt⁻ (St.elim-η R (x .fst) (Pᶜ (x .fst)) (λ s → t .N-ob (x .fst , s) u) (r (x .fst) u)) (x .snd))

    Psh-Quot-Structure : Quot-Structure (Psh-CwF C Univ)
    Psh-Quot-Structure .Quot-Structure.QTy                  = Psh-QTy
    Psh-Quot-Structure .Quot-Structure._⁺²                  = Psh-⁺²
    Psh-Quot-Structure .Quot-Structure.⁺²≡                  = Psh-⁺²≡
    Psh-Quot-Structure .Quot-Structure.QTyNat A R σ         = Psh-QTyNat R σ
    Psh-Quot-Structure .Quot-Structure.classTm              = Psh-classTm
    Psh-Quot-Structure .Quot-Structure.classTmNat {R = R}   = Psh-classTmNat R
    Psh-Quot-Structure .Quot-Structure.classSub {R = R}     = Psh-classSub R
    Psh-Quot-Structure .Quot-Structure.p∘classSub           = makeNatTransPath (funExt λ c → funExt λ w → fstPairSigma _ _)
    Psh-Quot-Structure .Quot-Structure.q[classSub] {R = R}  =
      makeNatTransPathP refl _ (funExt λ x → funExt λ u → ElPathP TU (q[classSub]-ob R x))
    Psh-Quot-Structure .Quot-Structure.classSubSound {R = R} = makeNatTransPath (funExt λ c → funExt (St.cls-sound R c))
    Psh-Quot-Structure .Quot-Structure.isEquivQuotCases A R P =
      isEquivCases (Psh-quotElim R P) (Psh-quotElim-β R P) (Psh-quotElim-η R P)
        (λ _ → isOfHLevelPathP' 1 (isSetTm _ _) _ _)
        (λ m r c u → St.toRespects R c (λ s → P .F-ob (c , s)) (λ w → m .N-ob (c , w) u)
                                   (λ z → ElPathP TU (λ i → r i .N-ob (c , z) u)))
