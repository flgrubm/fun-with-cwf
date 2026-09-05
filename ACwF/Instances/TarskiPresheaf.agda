{-# OPTIONS --lossy-unification #-}
module ACwF.Instances.TarskiPresheaf where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
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

module _ {ℓob ℓhom ℓU ℓEl : Level} (C : Category ℓob ℓhom) {U : Type ℓU} (Univ : TarskiUniverse ℓEl U) where
  open TarskiUniverse Univ
  open Algebraic (PRESHEAFU C TU)
  private abstract
    -- The empty context
    PSH-TerminalObject : PresheafU C TU
    PSH-TerminalObject .F-ob x = Unit
    PSH-TerminalObject .F-hom _ x = x
    PSH-TerminalObject .F-id = refl
    PSH-TerminalObject .F-seq _ _ = refl

    PSH-Terminal : Terminal (PRESHEAFU C TU)
    PSH-Terminal .fst = PSH-TerminalObject
    PSH-Terminal .snd _ .fst .NatTrans.N-ob _ _ = isContrElUnit .fst
    PSH-Terminal .snd _ .fst .NatTrans.N-hom _ = refl
    PSH-Terminal .snd _ .snd η = makeNatTransPath (funExt λ I → funExt λ x → isContrElUnit .snd (N-ob η I x))

  -- the unit type
  Psh-UnitType : {Γ : PresheafU C TU} → Functor (∫U Γ) (UCat TU)
  Psh-UnitType = Constant _ _ Unit

  -- elements of A (terms) can be seen as natural transformations from the unit type to A
  private module _ (Γ : PresheafU C TU) (A : Functor (∫U Γ) (UCat TU)) where
    Psh-Tm : Type (ℓ-max (ℓ-max ℓob ℓhom) ℓEl)
    Psh-Tm = FUNCTOR (∫U Γ) (UCat TU) [ Psh-UnitType , A ]
    Psh-Tm-isSet : isSet (Psh-Tm)
    Psh-Tm-isSet = isSetNatTrans

  private
    []Tm : ∀ Γ Δ
      → (A : Functor (∫U Γ) (UCat TU))
      → (σ : NatTrans Δ Γ)
      → Psh-Tm Γ A
      → Psh-Tm Δ (A ∘F ∫U-hom σ)
    []Tm Γ Δ A σ M .N-ob x = M .N-ob (∫U-hom σ .F-ob x)
    []Tm Γ Δ A σ M .N-hom f = (M .N-hom) _

  Psh-CwF : CwF (ℓ-max (ℓ-max ℓob ℓhom) (ℓ-max ℓU ℓEl)) (ℓ-max (ℓ-max ℓob ℓhom) ℓEl)
  open CwF Psh-CwF
  Psh-CwF .CwF.⟨⟩ = PSH-Terminal

  Psh-CwF .CwF.Ty Γ = Functor (∫U Γ) (UCat TU)
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

  Psh-CwF .CwF._▹_ Γ A .F-ob I = Sigma (Γ .F-ob I) (λ x → A .F-ob (I , x))
  Psh-CwF .CwF._▹_ Γ A .F-hom {I} {J} f x = pairSigma (Γ .F-hom f (fstSigma x)) (A .F-hom (f , refl) (sndSigma x))
  Psh-CwF .CwF._▹_ Γ A .F-id {I} = funExt λ x →
    cong₂ pairSigma
      (funExt⁻ (Γ .F-id) (fstSigma x))
      (goal x ▷ funExt⁻ (A .F-id) (sndSigma x))
    ∙ ηSigma x
    where
      Elᴬ : El (Γ .F-ob I) → Type ℓEl
      Elᴬ z = El (A .F-ob (I , z))
      goal : ∀ x →
        PathP (λ i → Elᴬ (Γ .F-id i (fstSigma x)))
          (A .F-hom (id C , refl) (sndSigma x))
          (A .F-hom (∫U Γ .id) (sndSigma x))
      goal x =
        funExt⁻ (F-hom-PathP A (id C , refl) (id C , _) refl (λ i → I , Γ .F-id i (fstSigma x)) refl) (sndSigma x)
  Psh-CwF .CwF._▹_ Γ A .F-seq {I} {J} {K} f g = funExt λ x → cong₂ pairSigma
    (funExt⁻ (Γ .F-seq f g) (fstSigma x) ∙ cong (Γ .F-hom g) (sym (fstPairSigma _ _)))
    (compPathP' {B = Elᴬ}
      (goal x)
      (congP (λ i z → A .F-hom (g , refl) z) (symP (sndPairSigma _ _))))
    where
      Elᴬ : El (Γ .F-ob K) → Type ℓEl
      Elᴬ z = El (A .F-ob (K , z))
      goal' : ∀ x →
        PathP (λ i → Elᴬ (funExt⁻ (Γ .F-seq f g) (fstSigma x) i))
          (A .F-hom (g ⋆⟨ C ⟩ f , refl) (sndSigma x))
          (A .F-hom ((f , refl) ⋆⟨ ∫U Γ ⟩ (g , refl)) (sndSigma x))
      goal' x =
        funExt⁻ (F-hom-PathP A (seq' C g f , refl)
                  (seq' (∫U Γ) (f , refl) (g , refl)) refl (λ i → K , Γ .F-seq f g i (fstSigma x)) refl) (sndSigma x)
      goal : ∀ x →
        PathP (λ i → Elᴬ (funExt⁻ (Γ .F-seq f g) (fstSigma x) i))
          (A .F-hom (g ⋆⟨ C ⟩ f , refl) (sndSigma x))
          (A .F-hom (g , refl) (A .F-hom (f , refl) (sndSigma x)))
      goal x = goal' x ▷ funExt⁻ (A .F-seq (f , refl) (g , refl)) (sndSigma x)

  Psh-CwF .CwF.p .N-ob I x = fstSigma x
  Psh-CwF .CwF.p .N-hom f = funExt (λ _ → fstPairSigma _ _)

  Psh-CwF .CwF.q .N-ob x _ = sndSigma (x .snd)
  Psh-CwF .CwF.q {Γ} {A} .N-hom {x} {y} (f , p) = funExt λ _ →
    sym (fromPathP bigPathP)
    ∙ fromPathP (funExt⁻ (F-hom-PathP A (f , refl)
                  (∫U-hom (Psh-CwF .CwF.p {Γ} {A}) .F-hom (f , p))
                  refl (λ i → y .fst , qbase i) refl) (sndSigma (x .snd)))
    where
      Elᴬ : El (Γ .F-ob (y .fst)) → Type ℓEl
      Elᴬ z = El (A .F-ob (y .fst , z))
      qbase : Γ .F-hom f (fstSigma (x .snd)) ≡ fstSigma (y .snd)
      qbase = sym (fstPairSigma _ _) ∙ cong fstSigma p
      bigPathP : PathP (λ i → Elᴬ (qbase i))
                       (A .F-hom (f , refl) (sndSigma (x .snd))) (sndSigma (y .snd))
      bigPathP = compPathP' {B = Elᴬ}
                   (symP (sndPairSigma _ _)) (cong sndSigma p)

  Psh-CwF .CwF._⁺ σ .N-ob I x = pairSigma (σ .N-ob I (fstSigma x)) (sndSigma x)
  Psh-CwF .CwF._⁺ {Γ} {Δ} {A} σ .N-hom {I} {J} f = funExt λ x → cong₂ pairSigma
    (cong (σ .N-ob J) (fstPairSigma _ _) ∙ funExt⁻ (σ .N-hom f) (fstSigma x) ∙ cong (Γ .F-hom f) (sym (fstPairSigma _ _)))
    (compPathP' {B = Elᴬ}
      (sndPairSigma _ _)
      (compPathP' {B = Elᴬ}
        (snd≡ x)
        (congP (λ i z → A .F-hom (f , refl) z) (symP (sndPairSigma _ _)))))
    where
      Elᴬ : El (Γ .F-ob J) → Type ℓEl
      Elᴬ z = El (A .F-ob (J , z))
      snd≡ : ∀ x → PathP
                    (λ i → Elᴬ (funExt⁻ (σ .N-hom f) (fstSigma x) i))
                    (A .F-hom (f , _) (sndSigma x))
                    (A .F-hom (f , refl) (sndSigma x))
      snd≡ x = funExt⁻ (F-hom-PathP A (f , _) (f , refl) refl (λ i → J , funExt⁻ (σ .N-hom f) (fstSigma x) i) refl) (sndSigma x)

  Psh-CwF .CwF.⟨_⟩ M .N-ob I x = pairSigma x (M .N-ob (I , x) (isContrElUnit .fst))
  Psh-CwF .CwF.⟨_⟩ {Γ} {A} M .N-hom {I} {J} f = funExt λ x → cong₂ pairSigma
    (cong (Γ .F-hom f) (sym (fstPairSigma _ _)))
    ((funExt⁻ (M .N-hom (f , refl)) (isContrElUnit .fst)) ◁ congP (λ i z → A .F-hom (f , refl) z) (symP (sndPairSigma _ _)))

  Psh-CwF .CwF.⟨⟩∘ M σ = makeNatTransPath (funExt λ I → funExt λ x →
    cong₂ pairSigma (cong (σ .N-ob I) (sym (fstPairSigma _ _))) (symP (sndPairSigma _ _)))
  Psh-CwF .CwF.p⁺∘⟨q⟩≡id = makeNatTransPath (funExt λ I → funExt λ x →
    cong₂ pairSigma (cong fstSigma (fstPairSigma _ _)) (sndPairSigma _ _) ∙ ηSigma _)
  Psh-CwF .CwF.∘⁺ {Γ} {Δ} {Θ} {A} σ' σ =
    makeNatTransPathP (cong (Δ ▹_) ([][]Ty A σ' σ)) refl
      (funExt λ I → funExt λ w → cong₂ pairSigma (cong (σ .N-ob I) (sym (fstPairSigma _ _))) (symP (sndPairSigma _ _)))
  Psh-CwF .CwF.id⁺ {Γ} {A} =
    makeNatTransPathP (cong (Γ ▹_) ([id]Ty A)) refl (funExt λ I → funExt λ w → ηSigma _)
  Psh-CwF .CwF.p∘⁺ σ = makeNatTransPath (funExt λ I → funExt λ w → fstPairSigma _ _)
  Psh-CwF .CwF.[p][⁺]Ty {Γ} {Δ} B σ =
    Functor≡ (λ c → cong (B .F-ob) (ΣPathP (refl , fstPairSigma _ _)))
             (λ f → F-hom-PathP B _ _ (ΣPathP (refl , fstPairSigma _ _)) (ΣPathP (refl , fstPairSigma _ _)) refl)
  Psh-CwF .CwF.q[⁺]Tm {A = A} σ = makeNatTransPathP refl ([p][⁺]Ty _ σ)
    (λ i x u → sndPairSigma {B = λ v → A .F-ob (x .fst , v)} (σ .N-ob (x .fst) (fstSigma (x .snd))) (sndSigma (x .snd)) i)
  Psh-CwF .CwF.p∘⟨⟩≡id M = makeNatTransPath (funExt λ I → funExt λ z → fstPairSigma _ _)
  Psh-CwF .CwF.[p][⟨⟩]Ty B a =
    Functor≡ (λ c → cong (B .F-ob) (ΣPathP (refl , fstPairSigma _ _)))
             (λ f → F-hom-PathP B _ _ (ΣPathP (refl , fstPairSigma _ _)) (ΣPathP (refl , fstPairSigma _ _)) refl)
  Psh-CwF .CwF.q[⟨⟩]Tm {A = A} M = makeNatTransPathP refl ([p][⟨⟩]Ty A M)
    (λ i x u → (sndPairSigma {B = λ v → A .F-ob (x .fst , v)} (x .snd) (M .N-ob x (isContrElUnit .fst))
                  ▷ cong (M .N-ob x) (isContrElUnit .snd u)) i)

  -- The CwF of presheaves has a Σ-structure. It is defined pointwise using the
  -- universe's Sig:
  --
  -- ```
  -- (Σ A B) (I , ρ) = Sigma (A (I , ρ)) (λ x → B (I , (ρ , x)))
  -- ```
  --
  -- The non-computational parts (proofs) were generated using Claude and are
  -- very ugly, if not unreadable. A lot of them is just threading pairSigma and
  -- fstPairSigma deep into the terms. V-valued presheaves would not have this
  -- problem as these are definitional.
  open import ACwF.Sigma
  Psh-Σ-structure : Σ-Structure (PRESHEAFU C TU) Psh-CwF
  Psh-Σ-structure .Σ-Structure.ΣTy A B .F-ob (I , ρ) = Sigma (A .F-ob (I , ρ)) (λ x → B .F-ob (I , pairSigma ρ x))
  Psh-Σ-structure .Σ-Structure.ΣTy {Γ = Γ} A B .F-hom {x = X} {y = Y} (f , p) x =
    pairSigma (A .F-hom (f , p) (fstSigma x)) (B .F-hom (f , eqproof) (sndSigma x))
    where
      Elᴬ : El (Γ .F-ob (Y .fst)) → Type ℓEl
      Elᴬ z = El (A .F-ob (Y .fst , z))
      eqproof = cong₂ pairSigma (cong (Γ .F-hom f) (fstPairSigma _ _) ∙ p)
        (compPathP' {B = Elᴬ}
          (congP (λ i z → A .F-hom (f , refl) z) (sndPairSigma _ _))
          (funExt⁻ (F-hom-PathP A (f , refl) (f , p) refl (ΣPathP (refl , p)) refl) (fstSigma x)))
  Psh-Σ-structure .Σ-Structure.ΣTy {Γ = Γ} A B .F-id {I , ρ} = funExt λ x → SigmaPathP
    (fstPairSigma _ _ ∙ funExt⁻ (F-id-PathP A (funExt⁻ (Γ .F-id) _)) (fstSigma x))
    (compPathP' {B = λ z → El (B .F-ob (I , pairSigma ρ z))}
      (sndPairSigma _ _)
      (congP (λ i m → B .F-hom m (sndSigma x))
             (∫U-Hom-PathP (Γ ▹ A) _ (∫U (Γ ▹ A) .id) refl
                           (ΣPathP (refl , cong (pairSigma ρ) (funExt⁻ (F-id-PathP A (funExt⁻ (Γ .F-id) _)) (fstSigma x)))) refl)
        ▷ funExt⁻ (B .F-id) (sndSigma x)))
  Psh-Σ-structure .Σ-Structure.ΣTy {Γ = Γ} A B .F-seq {x = X} {y = Y} {z = Z} f g =
    funExt λ x → SigmaPathP
      (fstPairSigma _ _
        ∙ funExt⁻ (A .F-seq f g) (fstSigma x)
        ∙ cong (A .F-hom g) (sym (fstPairSigma _ _))
        ∙ sym (fstPairSigma _ _))
      (compPathP' {B = Bmot}
        (sndPairSigma _ _)
        (compPathP' {B = Bmot}
          (funExt⁻ (F-hom-PathP B _ ((f .fst , eqp f (fstSigma x)) ⋆⟨ ∫U (Γ ▹ A) ⟩ (g .fst , eqp g (A .F-hom f (fstSigma x)))) refl
                      (cong (λ v → Z .fst , pairSigma (Z .snd) v) (funExt⁻ (A .F-seq f g) (fstSigma x))) refl)
                   (sndSigma x)
            ▷ funExt⁻ (B .F-seq (f .fst , eqp f (fstSigma x)) (g .fst , eqp g (A .F-hom f (fstSigma x)))) (sndSigma x))
          (compPathP' {B = Bmot}
            (congP₂ (λ i m z → B .F-hom m z)
              (∫U-Hom-PathP (Γ ▹ A) (g .fst , eqp g (A .F-hom f (fstSigma x))) _
                (cong (λ v → Y .fst , pairSigma (Y .snd) v) (sym (fstPairSigma _ _)))
                (cong (λ v → Z .fst , pairSigma (Z .snd) (A .F-hom g v)) (sym (fstPairSigma _ _)))
                refl)
              (symP (sndPairSigma _ _)))
            (symP (sndPairSigma _ _)))))
    where
      Bmot : El (A .F-ob Z) → Type ℓEl
      Bmot v = El (B .F-ob (Z .fst , pairSigma (Z .snd) v))
      eqp : {O O' : ∫U Γ .ob} (m : ∫U Γ [ O , O' ]) (s : El (A .F-ob O))
          → (Γ ▹ A) .F-hom (m .fst) (pairSigma (O .snd) s) ≡ pairSigma (O' .snd) (A .F-hom m s)
      eqp {O} {O'} (m₀ , mp) s = cong₂ pairSigma
        (cong (Γ .F-hom m₀) (fstPairSigma _ _) ∙ mp)
        (compPathP' {B = λ v → El (A .F-ob (O' .fst , v))}
          (congP (λ i z → A .F-hom (m₀ , refl) z) (sndPairSigma _ _))
          (funExt⁻ (F-hom-PathP A (m₀ , refl) (m₀ , mp) refl (ΣPathP (refl , mp)) refl) s))

  Psh-Σ-structure .Σ-Structure.ΣTyNat {Γ = Γ} {Δ = Δ} A B σ = Functor≡
    (λ c → cong₂ Sigma refl (funExt λ v → cong (B .F-ob) (BObj c v)))
    (λ {c} {c'} f → funExtDep (λ {s₀} {s₁} p →
      congP₂ (λ i a b → pairSigma {B = λ v → B .F-ob (BObj c' v i)} a b)
        (cong (A .F-hom (∫U-hom σ .F-hom f)) (congP (λ i → fstSigma {B = λ v → B .F-ob (BObj c v i)}) p))
        (congP₂ (λ i m z → B .F-hom m z)
          (∫U-Hom-PathP (Γ ▹ A) _ _
            (λ i → BObj c (fstSigma (p i)) i)
            (λ i → BObj c' (A .F-hom (∫U-hom σ .F-hom f) (fstSigma (p i))) i)
            refl)
          (congP (λ i → sndSigma {B = λ v → B .F-ob (BObj c v i)}) p))))
    where
      BObj : (cc : ∫U Δ .ob) (v : El (A .F-ob (cc .fst , σ .N-ob (cc .fst) (cc .snd))))
           → Path (∫U (Γ ▹ A) .ob)
                  (cc .fst , pairSigma (σ .N-ob (cc .fst) (cc .snd)) v)
                  (cc .fst , (_⁺ {A = A} σ) .N-ob (cc .fst) (pairSigma {B = λ z → A .F-ob (cc .fst , σ .N-ob (cc .fst) z)} (cc .snd) v))
      BObj cc v = ΣPathP (refl , cong₂ pairSigma (cong (σ .N-ob (cc .fst)) (sym (fstPairSigma _ _))) (symP (sndPairSigma _ _)))

  Psh-Σ-structure .Σ-Structure.ΣTmIso {Γ = Γ} A B .Iso.fun M .fst .N-ob o u = fstSigma (M .N-ob o u)
  Psh-Σ-structure .Σ-Structure.ΣTmIso {Γ = Γ} A B .Iso.fun M .fst .N-hom f =
    funExt λ u → cong fstSigma (funExt⁻ (M .N-hom f) u) ∙ fstPairSigma _ _
  Psh-Σ-structure .Σ-Structure.ΣTmIso {Γ = Γ} A B .Iso.fun M .snd .N-ob o u = sndSigma (M .N-ob o (isContrElUnit .fst))
  Psh-Σ-structure .Σ-Structure.ΣTmIso {Γ = Γ} A B .Iso.fun M .snd .N-hom {x} {y} f =
    funExt λ u →
      let Mx = M .N-ob x (isContrElUnit .fst)
          mnhom = funExt⁻ (M .N-hom f) (isContrElUnit .fst)
          base = cong fstSigma mnhom ∙ fstPairSigma _ _
          bigPathP = compPathP' {B = λ w → El (B .F-ob (y .fst , pairSigma (y .snd) w))}
            (cong sndSigma mnhom) (sndPairSigma _ _)
          P3 = funExt⁻ (F-hom-PathP B _ _ refl (ΣPathP (refl , cong (pairSigma (y .snd)) base)) refl) (sndSigma Mx)
      in sym (fromPathP (symP bigPathP)) ∙ fromPathP (symP P3)
  Psh-Σ-structure .Σ-Structure.ΣTmIso {Γ = Γ} A B .Iso.inv (a , b) .N-ob o u =
    pairSigma (a .N-ob o (isContrElUnit .fst)) (b .N-ob o u)
  Psh-Σ-structure .Σ-Structure.ΣTmIso {Γ = Γ} A B .Iso.inv (a , b) .N-hom {x} {y} f =
    funExt λ u →
      let fst≡ = funExt⁻ (a .N-hom f) (isContrElUnit .fst) ∙ cong (A .F-hom f) (sym (fstPairSigma _ _))
      in cong₂ pairSigma fst≡
           (funExt⁻ (b .N-hom f) u ◁
             congP₂ (λ i m z → B .F-hom m z)
               (∫U-Hom-PathP (Γ ▹ A) _ _
                 (cong (λ w → x .fst , pairSigma (x .snd) w) (sym (fstPairSigma _ _)))
                 (cong (λ w → y .fst , pairSigma (y .snd) w) fst≡)
                 refl)
               (symP (sndPairSigma _ _)))
  Psh-Σ-structure .Σ-Structure.ΣTmIso {Γ = Γ} A B .Iso.sec (a , b) = ΣPathP (
    (makeNatTransPath (funExt λ o → funExt λ u → fstPairSigma _ _ ∙ cong (N-ob a o) (isContrElUnit .snd u)))
    , makeNatTransPathP refl
        (cong (λ a' → B [ ⟨ a' ⟩ ]Ty)
          (makeNatTransPath (funExt λ o → funExt λ u → fstPairSigma _ _ ∙ cong (N-ob a o) (isContrElUnit .snd u))))
        (λ i o u → compPathP' {B = λ v → El (B .F-ob (o .fst , pairSigma (o .snd) v))}
          (sndPairSigma (N-ob a o (isContrElUnit .fst)) (N-ob b o (isContrElUnit .fst)))
          (subst
            (λ p → PathP (λ j → El (B .F-ob (o .fst , pairSigma (o .snd) (p j))))
                         (N-ob b o (isContrElUnit .fst)) (N-ob b o u))
            (sym (cong (cong (N-ob a o))
              (isProp→isSet (isContr→isProp isContrElUnit) _ _ (isContrElUnit .snd (isContrElUnit .fst)) refl)))
            (cong (N-ob b o) (isContrElUnit .snd u)))
          i))
  Psh-Σ-structure .Σ-Structure.ΣTmIso {Γ = Γ} A B .Iso.ret M =
    makeNatTransPath (funExt λ o → funExt λ u → ηSigma _ ∙ cong (M .N-ob o) (isContrElUnit .snd u))

  Psh-Σ-structure .Σ-Structure.coerce A B x σ = Functor≡
    (λ c → cong (B .F-ob) (ΣPathP (refl , cong₂ pairSigma (cong (σ .N-ob (c .fst)) (sym (fstPairSigma _ _ ))) (symP (sndPairSigma _ _)))))
    (λ {c} {c'} f → F-hom-PathP B _ _
      (ΣPathP (refl , cong₂ pairSigma (cong (σ .N-ob (c .fst)) (sym (fstPairSigma _ _))) (symP (sndPairSigma _ _))))
      (ΣPathP (refl , cong₂ pairSigma (cong (σ .N-ob (c' .fst)) (sym (fstPairSigma _ _))) (symP (sndPairSigma _ _))))
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
                    (o .fst , pairSigma (σ .N-ob (o .fst) (o .snd)) v)
                    (o .fst , (_⁺ {A = A} σ) .N-ob (o .fst) (pairSigma (o .snd) v))
        bobj v = ΣPathP (refl , cong₂ pairSigma (cong (σ .N-ob (o .fst)) (sym (fstPairSigma _ _))) (symP (sndPairSigma _ _)))
        sndPath : PathP (λ j → El (B .F-ob (bobj av j))) (bσ .N-ob o u) (b' .N-ob o u)
        sndPath = subst (λ r → PathP (λ j → El (r j)) (bσ .N-ob o u) (b' .N-ob o u))
                        (isSetU _ _ (λ j → cee j .F-ob o) (λ j → B .F-ob (bobj av j)))
                        cand
      in congP (λ j z → pairSigma {B = λ v → B .F-ob (bobj v j)} av z) sndPath i)

  open import ACwF.Pi
  open import TarskiUniverse.Solver
  open import Utils.InternalCategory
  open [_]CodedCategory
  module _ (hasPiTU : hasPi TU) (hasEqTU : hasEq TU) (coded : [ TU ]CodedCategory C) where
    module _ {Γ : PresheafU C TU } {A : Functor (∫U Γ) (UCat TU)} where
      ▹ob : (x : ∫U Γ .ob) → (a : El (A .F-ob x)) → ∫U (Γ ▹ A) .ob
      ▹ob x a = (x .fst) , (pairSigma (x .snd) a)
      ▹hom : ∀ {y} {z} → (f : (∫U Γ) [ y , z ]) (a : El (A .F-ob y)) → ∫U (Γ ▹ A) [ ▹ob y a , ▹ob z (A .F-hom f a) ]
      ▹hom f a .fst = f .fst
      ▹hom {y} {z} f a .snd = cong₂ pairSigma
        (cong (Γ .F-hom (f .fst)) (fstPairSigma (y .snd) a) ∙ f .snd)
        (compPathP' {B = λ v → El (A .F-ob (z .fst , v))}
          (congP (λ i s → A .F-hom (f .fst , refl) s) (sndPairSigma (y .snd) a))
          (funExt⁻ (F-hom-PathP A (f .fst , refl) f refl (ΣPathP (refl , f .snd)) refl) a))

    module _ {Γ : PresheafU C TU } (A : Functor (∫U Γ) (UCat TU)) (B : Functor (∫U (Γ ▹ A)) (UCat TU)) (x : ∫U Γ .ob)  where
      Πdata : Type (ℓ-max (ℓ-max ℓob ℓhom) ℓEl)
      Πdata = ((y : ∫U Γ .ob) (f : ∫U Γ [ x , y ]) (a : El (A .F-ob y)) → El (B .F-ob (▹ob {Γ} {A} y a)))
      Πnat : Πdata → Type (ℓ-max (ℓ-max ℓob ℓhom) ℓEl)
      Πnat w = (y z : ∫U Γ .ob) (m : ∫U Γ [ x , y ]) (n : ∫U Γ [ y , z ]) (a : El (A .F-ob y))
        → B .F-hom (▹hom n a) (w y m a) ≡ w z (m ⋆⟨ ∫U Γ ⟩ n) (A .F-hom n a)

      isPropΠnat : (w : Πdata) → isProp (Πnat w)
      isPropΠnat w = isPropΠ5 λ _ _ _ _ _ → isSetEl _ _ _

      Πtype : Type (ℓ-max (ℓ-max ℓob ℓhom) ℓEl)
      Πtype = Σ Πdata Πnat
      Πcode : TU hasCodeFor Πtype
      Πcode = solveCode (coded .isSmallHom ◂ coded .isSmallOb ◂ hasPiTU ◂ hasEqTU ◂ hasSigmaTU ◂ ε)
      Πcode→type : El (Πcode .fst) → Πtype
      Πcode→type = Πcode .snd .fst
      Πtype→code : Πtype → El (Πcode .fst)
      Πtype→code = invEq (Πcode .snd)

    module _ {Γ : PresheafU C TU } {A : Functor (∫U Γ) (UCat TU)} {B : Functor (∫U (Γ ▹ A)) (UCat TU)} where
      restrict : {x x' : ∫U Γ .ob} → (f : ∫U Γ [ x , x' ]) → Πtype A B x → Πtype A B x'
      restrict h (w , nat) .fst y f a = w y (h ⋆⟨ ∫U Γ ⟩ f) a
      restrict h (w , nat) .snd y z m n a =
          nat y z (h ⋆⟨ ∫U Γ ⟩ m) n a
        ∙ cong (λ v → w z v (A .F-hom n a)) (∫U Γ .⋆Assoc h m n)

      restrict-id : {x : ∫U Γ .ob} (a : Πtype A B x) → restrict (∫U Γ .id) a ≡ a
      restrict-id a = Σ≡Prop (isPropΠnat A B _)
        (funExt λ y → funExt λ f → funExt λ v → cong (λ h → a .fst y h v) (∫U Γ .⋆IdL f))
      restrict-seq : {x x' x'' : ∫U Γ .ob} (f : ∫U Γ [ x , x' ]) (g : ∫U Γ [ x' , x'' ] ) (a : Πtype A B x)
        → restrict (f ⋆⟨ ∫U Γ ⟩ g) a ≡ restrict g (restrict f a)
      restrict-seq f g a = Σ≡Prop (isPropΠnat A B _)
        (funExt λ y → funExt λ h → funExt λ v → cong (λ k → a .fst y k v) (∫U Γ .⋆Assoc f g h))

    Psh-Π-structure : Π-Structure _ Psh-CwF

    Psh-Π-structure .Π-Structure.ΠTy A B .F-ob Iρ = Πcode A B Iρ .fst
    Psh-Π-structure .Π-Structure.ΠTy A B .F-hom f a = Πtype→code A B _ (restrict {A = A} {B = B} f (Πcode→type A B _ a))
    Psh-Π-structure .Π-Structure.ΠTy A B .F-id = funExt λ a →
        cong (Πtype→code A B _) (restrict-id {A = A} {B = B} _)
      ∙ retEq (Πcode A B _ .snd) a
    Psh-Π-structure .Π-Structure.ΠTy A B .F-seq f g = funExt λ a →
        cong (Πtype→code A B _) (restrict-seq {A = A} {B = B} f g _)
      ∙ cong (λ z → Πtype→code A B _ (restrict {A = A} {B = B} g z))
             (sym (secEq (Πcode A B _ .snd) _))

    Psh-Π-structure .Π-Structure.ΠTyNat A B σ = Functor≡ (λ x → {!!}) {!!}
    Psh-Π-structure .Π-Structure.ΠTmIso = {!!}
    Psh-Π-structure .Π-Structure.ΠTmIsoInvNat = {!!}
