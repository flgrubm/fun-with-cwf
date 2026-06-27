{-# OPTIONS --lossy-unification #-}
module ACwF.Instances.TarskiPresheaf where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Functions.FunExtEquiv
open import Cubical.Data.Sigma
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Functors.Constant
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Limits.Terminal
open import TarskiUniverse.Base
open import TarskiUniverse.Properties
open import Utils.TarskiPresheaf
open import ACwF.Base

open Category
open Functor
open NatTrans

module _ {ℓob ℓhom ℓU ℓEl : Level} (C : Category ℓob ℓhom) (Univ : TarskiUniverse ℓU ℓEl) where
  open TarskiUniverse Univ
  open Algebraic (PRESHEAFU C Univ)
  private abstract
    -- The empty context
    PSH-TerminalObject : PresheafU C Univ
    PSH-TerminalObject .F-ob x = Unit
    PSH-TerminalObject .F-hom _ x = x
    PSH-TerminalObject .F-id = refl
    PSH-TerminalObject .F-seq _ _ = refl

    PSH-Terminal : Terminal (PRESHEAFU C Univ)
    PSH-Terminal .fst = PSH-TerminalObject
    PSH-Terminal .snd _ .fst .NatTrans.N-ob _ _ = isContrElUnit .fst
    PSH-Terminal .snd _ .fst .NatTrans.N-hom _ = refl
    PSH-Terminal .snd _ .snd η = makeNatTransPath (funExt λ I → funExt λ x → isContrElUnit .snd (N-ob η I x))

  -- the unit type
  Psh-UnitType : {Γ : PresheafU C Univ} → Functor (∫U Γ) (UCat Univ)
  Psh-UnitType = Constant _ _ Unit

  -- elements of A (terms) can be seen as natural transformations from the unit type to A
  private module _ (Γ : PresheafU C Univ) (A : Functor (∫U Γ) (UCat Univ)) where
    Psh-Tm : Type (ℓ-max (ℓ-max ℓob ℓhom) ℓEl)
    Psh-Tm = FUNCTOR (∫U Γ) (UCat Univ) [ Psh-UnitType , A ]
    Psh-Tm-isSet : isSet (Psh-Tm)
    Psh-Tm-isSet = isSetNatTrans

  private
    []Tm : ∀ Γ Δ
      → (A : Functor (∫U Γ) (UCat Univ))
      → (σ : NatTrans Δ Γ)
      → Psh-Tm Γ A
      → Psh-Tm Δ (A ∘F ∫U-hom σ)
    []Tm Γ Δ A σ M .N-ob x = M .N-ob (∫U-hom σ .F-ob x)
    []Tm Γ Δ A σ M .N-hom f = (M .N-hom) _

  Psh-CwF : CwF (ℓ-max (ℓ-max ℓob ℓhom) (ℓ-max ℓU ℓEl)) (ℓ-max (ℓ-max ℓob ℓhom) ℓEl)
  open CwF Psh-CwF
  Psh-CwF .CwF.⟨⟩ = PSH-Terminal

  Psh-CwF .CwF.Ty Γ = Functor (∫U Γ) (UCat Univ)
  Psh-CwF .CwF.isSetTy Γ = isSetFunctor isSetU
  Psh-CwF .CwF._[_]Ty A σ = A ∘F ∫U-hom σ
  Psh-CwF .CwF.[id]Ty {Γ} A =
    Functor≡
      (λ c → refl)
      (λ f → cong (A .F-hom) (ΣPathP (refl , isSetEl (Γ .F-ob _) _ _ _ _)))
  Psh-CwF .CwF.[][]Ty {Γ = Γ} A σ' σ =
    Functor≡ (λ c → refl) λ f → cong (A .F-hom) (ΣPathP (refl , isSetEl (Γ .F-ob _) _ _ _ _))

  Psh-CwF .CwF.Tm Γ A = Psh-Tm Γ A
  Psh-CwF .CwF.isSetTm = Psh-Tm-isSet
  Psh-CwF .CwF._[_]Tm M σ = []Tm _ _ _ σ M
  Psh-CwF .CwF.[id]Tm M = makeNatTransPathP refl ([id]Ty _) refl
  Psh-CwF .CwF.[][]Tm M σ' σ = makeNatTransPathP refl ([][]Ty _ _ _) refl

  Psh-CwF .CwF._▹_ Γ A .F-ob I = Sig (Γ .F-ob I) (λ x → A .F-ob (I , x))
  Psh-CwF .CwF._▹_ Γ A .F-hom {I} {J} f x = pairSig (Γ .F-hom f (fstSig x)) (A .F-hom (f , refl) (sndSig x))
  Psh-CwF .CwF._▹_ Γ A .F-id {I} = funExt λ x →
    cong₂ pairSig
      (funExt⁻ (Γ .F-id) (fstSig x))
      (goal x ▷ funExt⁻ (A .F-id) (sndSig x))
    ∙ ηSig x
    where
      Elᴬ : El (Γ .F-ob I) → Type ℓEl
      Elᴬ z = El (A .F-ob (I , z))
      goal : ∀ x →
        PathP (λ i → Elᴬ (Γ .F-id i (fstSig x)))
          (A .F-hom (id C , refl) (sndSig x))
          (A .F-hom (∫U Γ .id) (sndSig x))
      goal x =
        funExt⁻ (F-hom-PathP A (id C , refl) (id C , _) refl (λ i → I , Γ .F-id i (fstSig x)) refl) (sndSig x)
  Psh-CwF .CwF._▹_ Γ A .F-seq {I} {J} {K} f g = funExt λ x → cong₂ pairSig
    (funExt⁻ (Γ .F-seq f g) (fstSig x) ∙ cong (Γ .F-hom g) (sym (fstPairSig _ _)))
    (compPathP' {B = Elᴬ}
      (goal x)
      (congP (λ i z → A .F-hom (g , refl) z) (symP (sndPairSig _ _))))
    where
      Elᴬ : El (Γ .F-ob K) → Type ℓEl
      Elᴬ z = El (A .F-ob (K , z))
      goal' : ∀ x →
        PathP (λ i → Elᴬ (funExt⁻ (Γ .F-seq f g) (fstSig x) i))
          (A .F-hom (g ⋆⟨ C ⟩ f , refl) (sndSig x))
          (A .F-hom ((f , refl) ⋆⟨ ∫U Γ ⟩ (g , refl)) (sndSig x))
      goal' x =
        funExt⁻ (F-hom-PathP A (seq' C g f , refl)
                  (seq' (∫U Γ) (f , refl) (g , refl)) refl (λ i → K , Γ .F-seq f g i (fstSig x)) refl) (sndSig x)
      goal : ∀ x →
        PathP (λ i → Elᴬ (funExt⁻ (Γ .F-seq f g) (fstSig x) i))
          (A .F-hom (g ⋆⟨ C ⟩ f , refl) (sndSig x))
          (A .F-hom (g , refl) (A .F-hom (f , refl) (sndSig x)))
      goal x = goal' x ▷ funExt⁻ (A .F-seq (f , refl) (g , refl)) (sndSig x)

  Psh-CwF .CwF.p .N-ob I x = fstSig x
  Psh-CwF .CwF.p .N-hom f = funExt (λ _ → fstPairSig _ _)

  Psh-CwF .CwF.q .N-ob x _ = sndSig (x .snd)
  Psh-CwF .CwF.q {Γ} {A} .N-hom {x} {y} (f , p) = funExt λ _ →
    sym (fromPathP bigPathP)
    ∙ fromPathP (funExt⁻ (F-hom-PathP A (f , refl)
                  (∫U-hom (Psh-CwF .CwF.p {Γ} {A}) .F-hom (f , p))
                  refl (λ i → y .fst , qbase i) refl) (sndSig (x .snd)))
    where
      Elᴬ : El (Γ .F-ob (y .fst)) → Type ℓEl
      Elᴬ z = El (A .F-ob (y .fst , z))
      qbase : Γ .F-hom f (fstSig (x .snd)) ≡ fstSig (y .snd)
      qbase = sym (fstPairSig _ _) ∙ cong fstSig p
      bigPathP : PathP (λ i → Elᴬ (qbase i))
                       (A .F-hom (f , refl) (sndSig (x .snd))) (sndSig (y .snd))
      bigPathP = compPathP' {B = Elᴬ}
                   (symP (sndPairSig _ _)) (cong sndSig p)

  Psh-CwF .CwF._⁺ σ .N-ob I x = pairSig (σ .N-ob I (fstSig x)) (sndSig x)
  Psh-CwF .CwF._⁺ {Γ} {Δ} {A} σ .N-hom {I} {J} f = funExt λ x → cong₂ pairSig
    (cong (σ .N-ob J) (fstPairSig _ _) ∙ funExt⁻ (σ .N-hom f) (fstSig x) ∙ cong (Γ .F-hom f) (sym (fstPairSig _ _)))
    (compPathP' {B = Elᴬ}
      (sndPairSig _ _)
      (compPathP' {B = Elᴬ}
        (snd≡ x)
        (congP (λ i z → A .F-hom (f , refl) z) (symP (sndPairSig _ _)))))
    where
      Elᴬ : El (Γ .F-ob J) → Type ℓEl
      Elᴬ z = El (A .F-ob (J , z))
      snd≡ : ∀ x → PathP
                    (λ i → Elᴬ (funExt⁻ (σ .N-hom f) (fstSig x) i))
                    (A .F-hom (f , _) (sndSig x))
                    (A .F-hom (f , refl) (sndSig x))
      snd≡ x = funExt⁻ (F-hom-PathP A (f , _) (f , refl) refl (λ i → J , funExt⁻ (σ .N-hom f) (fstSig x) i) refl) (sndSig x)

  Psh-CwF .CwF.⟨_⟩ M .N-ob I x = pairSig x (M .N-ob (I , x) (isContrElUnit .fst))
  Psh-CwF .CwF.⟨_⟩ {Γ} {A} M .N-hom {I} {J} f = funExt λ x → cong₂ pairSig
    (cong (Γ .F-hom f) (sym (fstPairSig _ _)))
    ((funExt⁻ (M .N-hom (f , refl)) (isContrElUnit .fst)) ◁ congP (λ i z → A .F-hom (f , refl) z) (symP (sndPairSig _ _)))

  Psh-CwF .CwF.⟨⟩∘ M σ = makeNatTransPath (funExt λ I → funExt λ x →
    cong₂ pairSig (cong (σ .N-ob I) (sym (fstPairSig _ _))) (symP (sndPairSig _ _)))
  Psh-CwF .CwF.p⁺∘⟨q⟩≡id = makeNatTransPath (funExt λ I → funExt λ x →
    cong₂ pairSig (cong fstSig (fstPairSig _ _)) (sndPairSig _ _) ∙ ηSig _)
  Psh-CwF .CwF.∘⁺ {Γ} {Δ} {Θ} {A} σ' σ =
    makeNatTransPathP (cong (Δ ▹_) ([][]Ty A σ' σ)) refl
      (funExt λ I → funExt λ w → cong₂ pairSig (cong (σ .N-ob I) (sym (fstPairSig _ _))) (symP (sndPairSig _ _)))
  Psh-CwF .CwF.id⁺ {Γ} {A} =
    makeNatTransPathP (cong (Γ ▹_) ([id]Ty A)) refl (funExt λ I → funExt λ w → ηSig _)
  Psh-CwF .CwF.p∘⁺ σ = makeNatTransPath (funExt λ I → funExt λ w → fstPairSig _ _)
  Psh-CwF .CwF.[p][⁺]Ty {Γ} {Δ} B σ =
    Functor≡ (λ c → cong (B .F-ob) (ΣPathP (refl , fstPairSig _ _)))
             (λ f → F-hom-PathP B _ _ (ΣPathP (refl , fstPairSig _ _)) (ΣPathP (refl , fstPairSig _ _)) refl)
  Psh-CwF .CwF.q[⁺]Tm {A = A} σ = makeNatTransPathP refl ([p][⁺]Ty _ σ)
    (λ i x u → sndPairSig {B = λ v → A .F-ob (x .fst , v)} (σ .N-ob (x .fst) (fstSig (x .snd))) (sndSig (x .snd)) i)
  Psh-CwF .CwF.p∘⟨⟩≡id M = makeNatTransPath (funExt λ I → funExt λ z → fstPairSig _ _)
  Psh-CwF .CwF.[p][⟨⟩]Ty B a =
    Functor≡ (λ c → cong (B .F-ob) (ΣPathP (refl , fstPairSig _ _)))
             (λ f → F-hom-PathP B _ _ (ΣPathP (refl , fstPairSig _ _)) (ΣPathP (refl , fstPairSig _ _)) refl)
  Psh-CwF .CwF.q[⟨⟩]Tm {A = A} M = makeNatTransPathP refl ([p][⟨⟩]Ty A M)
    (λ i x u → (sndPairSig {B = λ v → A .F-ob (x .fst , v)} (x .snd) (M .N-ob x (isContrElUnit .fst))
                  ▷ cong (M .N-ob x) (isContrElUnit .snd u)) i)

  -- The CwF of presheaves has a Σ-structure. It is defined pointwise using the
  -- universe's Sig:
  --
  -- ```
  -- (Σ A B) (I , ρ) = Sig (A (I , ρ)) (λ x → B (I , (ρ , x)))
  -- ```
  --
  -- The non-computational parts (proofs) were generated using Claude and are
  -- very ugly, if not unreadable. A lot of them is just threading pairSig and
  -- fstPairSig deep into the terms. V-valued presheaves would not have this
  -- problem as these are definitional.
  open import ACwF.Sigma
  Psh-Σ-structure : Σ-Structure (PRESHEAFU C Univ) Psh-CwF
  Psh-Σ-structure .Σ-Structure.ΣTy A B .F-ob (I , ρ) = Sig (A .F-ob (I , ρ)) (λ x → B .F-ob (I , pairSig ρ x))
  Psh-Σ-structure .Σ-Structure.ΣTy {Γ = Γ} A B .F-hom {x = X} {y = Y} (f , p) x =
    pairSig (A .F-hom (f , p) (fstSig x)) (B .F-hom (f , eqproof) (sndSig x))
    where
      Elᴬ : El (Γ .F-ob (Y .fst)) → Type ℓEl
      Elᴬ z = El (A .F-ob (Y .fst , z))
      eqproof = cong₂ pairSig (cong (Γ .F-hom f) (fstPairSig _ _) ∙ p)
        (compPathP' {B = Elᴬ}
          (congP (λ i z → A .F-hom (f , refl) z) (sndPairSig _ _))
          (funExt⁻ (F-hom-PathP A (f , refl) (f , p) refl (ΣPathP (refl , p)) refl) (fstSig x)))
  Psh-Σ-structure .Σ-Structure.ΣTy {Γ = Γ} A B .F-id {I , ρ} = funExt λ x → SigPathP
    (fstPairSig _ _ ∙ funExt⁻ (F-id-PathP A (funExt⁻ (Γ .F-id) _)) (fstSig x))
    (compPathP' {B = λ z → El (B .F-ob (I , pairSig ρ z))}
      (sndPairSig _ _)
      (congP (λ i m → B .F-hom m (sndSig x))
             (∫U-Hom-PathP (Γ ▹ A) _ (∫U (Γ ▹ A) .id) refl
                           (ΣPathP (refl , cong (pairSig ρ) (funExt⁻ (F-id-PathP A (funExt⁻ (Γ .F-id) _)) (fstSig x)))) refl)
        ▷ funExt⁻ (B .F-id) (sndSig x)))
  Psh-Σ-structure .Σ-Structure.ΣTy {Γ = Γ} A B .F-seq {x = X} {y = Y} {z = Z} f g =
    funExt λ x → SigPathP
      (fstPairSig _ _
        ∙ funExt⁻ (A .F-seq f g) (fstSig x)
        ∙ cong (A .F-hom g) (sym (fstPairSig _ _))
        ∙ sym (fstPairSig _ _))
      (compPathP' {B = Bmot}
        (sndPairSig _ _)
        (compPathP' {B = Bmot}
          (funExt⁻ (F-hom-PathP B _ ((f .fst , eqp f (fstSig x)) ⋆⟨ ∫U (Γ ▹ A) ⟩ (g .fst , eqp g (A .F-hom f (fstSig x)))) refl
                      (cong (λ v → Z .fst , pairSig (Z .snd) v) (funExt⁻ (A .F-seq f g) (fstSig x))) refl)
                   (sndSig x)
            ▷ funExt⁻ (B .F-seq (f .fst , eqp f (fstSig x)) (g .fst , eqp g (A .F-hom f (fstSig x)))) (sndSig x))
          (compPathP' {B = Bmot}
            (congP₂ (λ i m z → B .F-hom m z)
              (∫U-Hom-PathP (Γ ▹ A) (g .fst , eqp g (A .F-hom f (fstSig x))) _
                (cong (λ v → Y .fst , pairSig (Y .snd) v) (sym (fstPairSig _ _)))
                (cong (λ v → Z .fst , pairSig (Z .snd) (A .F-hom g v)) (sym (fstPairSig _ _)))
                refl)
              (symP (sndPairSig _ _)))
            (symP (sndPairSig _ _)))))
    where
      Bmot : El (A .F-ob Z) → Type ℓEl
      Bmot v = El (B .F-ob (Z .fst , pairSig (Z .snd) v))
      eqp : {O O' : ∫U Γ .ob} (m : ∫U Γ [ O , O' ]) (s : El (A .F-ob O))
          → (Γ ▹ A) .F-hom (m .fst) (pairSig (O .snd) s) ≡ pairSig (O' .snd) (A .F-hom m s)
      eqp {O} {O'} (m₀ , mp) s = cong₂ pairSig
        (cong (Γ .F-hom m₀) (fstPairSig _ _) ∙ mp)
        (compPathP' {B = λ v → El (A .F-ob (O' .fst , v))}
          (congP (λ i z → A .F-hom (m₀ , refl) z) (sndPairSig _ _))
          (funExt⁻ (F-hom-PathP A (m₀ , refl) (m₀ , mp) refl (ΣPathP (refl , mp)) refl) s))

  Psh-Σ-structure .Σ-Structure.ΣTyNat {Γ = Γ} {Δ = Δ} A B σ = Functor≡
    (λ c → cong₂ Sig refl (funExt λ v → cong (B .F-ob) (BObj c v)))
    (λ {c} {c'} f → funExtDep (λ {s₀} {s₁} p →
      congP₂ (λ i a b → pairSig {B = λ v → B .F-ob (BObj c' v i)} a b)
        (cong (A .F-hom (∫U-hom σ .F-hom f)) (congP (λ i → fstSig {B = λ v → B .F-ob (BObj c v i)}) p))
        (congP₂ (λ i m z → B .F-hom m z)
          (∫U-Hom-PathP (Γ ▹ A) _ _
            (λ i → BObj c (fstSig (p i)) i)
            (λ i → BObj c' (A .F-hom (∫U-hom σ .F-hom f) (fstSig (p i))) i)
            refl)
          (congP (λ i → sndSig {B = λ v → B .F-ob (BObj c v i)}) p))))
    where
      BObj : (cc : ∫U Δ .ob) (v : El (A .F-ob (cc .fst , σ .N-ob (cc .fst) (cc .snd))))
           → Path (∫U (Γ ▹ A) .ob)
                  (cc .fst , pairSig (σ .N-ob (cc .fst) (cc .snd)) v)
                  (cc .fst , (_⁺ {A = A} σ) .N-ob (cc .fst) (pairSig {B = λ z → A .F-ob (cc .fst , σ .N-ob (cc .fst) z)} (cc .snd) v))
      BObj cc v = ΣPathP (refl , cong₂ pairSig (cong (σ .N-ob (cc .fst)) (sym (fstPairSig _ _))) (symP (sndPairSig _ _)))

  Psh-Σ-structure .Σ-Structure.ΣTmIso {Γ = Γ} A B .Iso.fun M .fst .N-ob o u = fstSig (M .N-ob o u)
  Psh-Σ-structure .Σ-Structure.ΣTmIso {Γ = Γ} A B .Iso.fun M .fst .N-hom f =
    funExt λ u → cong fstSig (funExt⁻ (M .N-hom f) u) ∙ fstPairSig _ _
  Psh-Σ-structure .Σ-Structure.ΣTmIso {Γ = Γ} A B .Iso.fun M .snd .N-ob o u = sndSig (M .N-ob o (isContrElUnit .fst))
  Psh-Σ-structure .Σ-Structure.ΣTmIso {Γ = Γ} A B .Iso.fun M .snd .N-hom {x} {y} f =
    funExt λ u →
      let Mx = M .N-ob x (isContrElUnit .fst)
          mnhom = funExt⁻ (M .N-hom f) (isContrElUnit .fst)
          base = cong fstSig mnhom ∙ fstPairSig _ _
          bigPathP = compPathP' {B = λ w → El (B .F-ob (y .fst , pairSig (y .snd) w))}
            (cong sndSig mnhom) (sndPairSig _ _)
          P3 = funExt⁻ (F-hom-PathP B _ _ refl (ΣPathP (refl , cong (pairSig (y .snd)) base)) refl) (sndSig Mx)
      in sym (fromPathP (symP bigPathP)) ∙ fromPathP (symP P3)
  Psh-Σ-structure .Σ-Structure.ΣTmIso {Γ = Γ} A B .Iso.inv (a , b) .N-ob o u =
    pairSig (a .N-ob o (isContrElUnit .fst)) (b .N-ob o u)
  Psh-Σ-structure .Σ-Structure.ΣTmIso {Γ = Γ} A B .Iso.inv (a , b) .N-hom {x} {y} f =
    funExt λ u →
      let fst≡ = funExt⁻ (a .N-hom f) (isContrElUnit .fst) ∙ cong (A .F-hom f) (sym (fstPairSig _ _))
      in cong₂ pairSig fst≡
           (funExt⁻ (b .N-hom f) u ◁
             congP₂ (λ i m z → B .F-hom m z)
               (∫U-Hom-PathP (Γ ▹ A) _ _
                 (cong (λ w → x .fst , pairSig (x .snd) w) (sym (fstPairSig _ _)))
                 (cong (λ w → y .fst , pairSig (y .snd) w) fst≡)
                 refl)
               (symP (sndPairSig _ _)))
  Psh-Σ-structure .Σ-Structure.ΣTmIso {Γ = Γ} A B .Iso.sec (a , b) = ΣPathP (
    (makeNatTransPath (funExt λ o → funExt λ u → fstPairSig _ _ ∙ cong (N-ob a o) (isContrElUnit .snd u)))
    , makeNatTransPathP refl
        (cong (λ a' → B [ ⟨ a' ⟩ ]Ty)
          (makeNatTransPath (funExt λ o → funExt λ u → fstPairSig _ _ ∙ cong (N-ob a o) (isContrElUnit .snd u))))
        (λ i o u → compPathP' {B = λ v → El (B .F-ob (o .fst , pairSig (o .snd) v))}
          (sndPairSig (N-ob a o (isContrElUnit .fst)) (N-ob b o (isContrElUnit .fst)))
          (subst
            (λ p → PathP (λ j → El (B .F-ob (o .fst , pairSig (o .snd) (p j))))
                         (N-ob b o (isContrElUnit .fst)) (N-ob b o u))
            (sym (cong (cong (N-ob a o))
              (isProp→isSet (isContr→isProp isContrElUnit) _ _ (isContrElUnit .snd (isContrElUnit .fst)) refl)))
            (cong (N-ob b o) (isContrElUnit .snd u)))
          i))
  Psh-Σ-structure .Σ-Structure.ΣTmIso {Γ = Γ} A B .Iso.ret M =
    makeNatTransPath (funExt λ o → funExt λ u → ηSig _ ∙ cong (M .N-ob o) (isContrElUnit .snd u))

  Psh-Σ-structure .Σ-Structure.coerce A B x σ = Functor≡
    (λ c → cong (B .F-ob) (ΣPathP (refl , cong₂ pairSig (cong (σ .N-ob (c .fst)) (sym (fstPairSig _ _ ))) (symP (sndPairSig _ _)))))
    (λ {c} {c'} f → F-hom-PathP B _ _
      (ΣPathP (refl , cong₂ pairSig (cong (σ .N-ob (c .fst)) (sym (fstPairSig _ _))) (symP (sndPairSig _ _))))
      (ΣPathP (refl , cong₂ pairSig (cong (σ .N-ob (c' .fst)) (sym (fstPairSig _ _))) (symP (sndPairSig _ _))))
      refl)

  Psh-Σ-structure .Σ-Structure.ΣTmIsoInvNat {Γ} {Δ} A B a b σ =
    makeNatTransPathP refl _ (λ i o u →
      let
        σo : ∫U Γ .ob
        σo = ∫U-hom σ .F-ob o
        av : El (A .F-ob σo)
        av = a .N-ob σo (isContrElUnit .fst)
        bσ : Tm Δ ((B [ ⟨ a ⟩ ]Ty) [ σ ]Ty)
        bσ = b [ σ ]Tm
        cee : (B [ ⟨ a ⟩ ]Ty) [ σ ]Ty ≡ (B [ σ ⁺ ]Ty) [ ⟨ a [ σ ]Tm ⟩ ]Ty
        cee = Psh-Σ-structure .Σ-Structure.coerce A B a σ
        b' : Tm Δ ((B [ σ ⁺ ]Ty) [ ⟨ a [ σ ]Tm ⟩ ]Ty)
        b' = subst (Tm Δ) cee bσ
        cand : PathP (λ j → El (cee j .F-ob o)) (bσ .N-ob o u) (b' .N-ob o u)
        cand j = subst-filler (Tm Δ) cee bσ j .N-ob o u
        bobj : (v : El (A .F-ob σo))
             → Path (∫U (Γ ▹ A) .ob)
                    (o .fst , pairSig (σ .N-ob (o .fst) (o .snd)) v)
                    (o .fst , (_⁺ {A = A} σ) .N-ob (o .fst) (pairSig (o .snd) v))
        bobj v = ΣPathP (refl , cong₂ pairSig (cong (σ .N-ob (o .fst)) (sym (fstPairSig _ _))) (symP (sndPairSig _ _)))
        sndPath : PathP (λ j → El (B .F-ob (bobj av j))) (bσ .N-ob o u) (b' .N-ob o u)
        sndPath = subst (λ r → PathP (λ j → El (r j)) (bσ .N-ob o u) (b' .N-ob o u))
                        (isSetU _ _ (λ j → cee j .F-ob o) (λ j → B .F-ob (bobj av j)))
                        cand
      in congP (λ j z → pairSig {B = λ v → B .F-ob (bobj v j)} av z) sndPath i)

