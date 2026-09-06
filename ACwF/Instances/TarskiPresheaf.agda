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
        sndPath = reindexEl cand
      in congP (λ j z → pairSigma {B = λ v → B .F-ob (bobj v j)} av z) sndPath i)

  open import ACwF.Pi
  open import TarskiUniverse.Solver
  open import Utils.InternalCategory
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
      pi : ∫U Γ .ob → Type _
      pi x = indexed-Π {Γ} (x .fst) ((A ∘F κ Γ) ∘F ι x) (B ∘F κ▹ Γ A ∘F ∫ι x (A ∘F κ Γ))
      picode : (x : ∫U Γ .ob) → TU hasCodeFor (pi x)
      picode x = solveCode (coded .isSmallOb ◂ coded .isSmallHom ◂ hasSigmaTU ◂ hasPiTU ◂ hasEqTU ◂ ε)

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
        restrict : pi x → pi y
        restrict u = transport (λ i → indexed-Π {Γ} (y .fst) (PPath i) (QPath i))
                       (Π-precomp {Γ} _ _ Jφ u)

        -- β-rule for restrict, stated as a PathP over the coercion rather than a
        -- subst: U is a set, so the use site can reindex it onto whichever path it
        -- finds convenient.  This is the only place the transport is ever computed.
        restrictβ : (u : pi x) (s : Fib (y .fst) .ob)
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
      restrictId : {x : ∫U Γ .ob} (u : pi x) → restrict (∫U Γ .id) u ≡ u
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
              ap = reindexEl aP
              c : PathP (λ i → El (Qx .F-ob (e i , ap i)))
                        (u .fst (Jφ idx .F-ob s) a₀) (u .fst s a)
              c i = u .fst (e i) (ap i)
              c' : PathP (λ i → El (QPath idx i .F-ob (s , aP i)))
                         (u .fst (Jφ idx .F-ob s) a₀) (u .fst s a)
              c' = reindexEl c
              -- both routes from `u .fst (Jφ idx .F-ob s) a₀` meet here
              mid : El (Qx .F-ob (s , a))
              mid = transport (λ i → El (QPath idx i .F-ob (s , aP i)))
                              (u .fst (Jφ idx .F-ob s) a₀)

      -- Fib⋆ is functorial only up to ⋆Assoc, so composing two restrictions is
      -- again a transport question.  Both sides are routed back to one common
      -- starting element and compared there; U is a set, so the two routes may be
      -- reindexed onto a single path of codes.
      restrictSeq : {x y z : ∫U Γ .ob} (φ : ∫U Γ [ x , y ]) (ψ : ∫U Γ [ y , z ])
                    (u : pi x)
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
              dP = reindexEl (compPathP' {B = El} (compPathP' {B = El} cP bP) (symP aP))
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
              chainB = reindexEl (compPathP' {B = El}
                         (restrictβ φ u t cP)
                         (restrictβ ψ (restrict φ u) s bP))
              -- both routes out of `start` meet here
              mid : El (Qz .F-ob (s , a))
              mid = transport (λ i → El (famA i)) start

    Psh-Π-structure : Π-Structure _ Psh-CwF
    Psh-Π-structure .Π-Structure.ΠTy A B .F-ob x = picode A B x .fst
    Psh-Π-structure .Π-Structure.ΠTy {Γ} A B .F-hom {x} {y} φ e =
      invEq (picode A B y .snd) (restrict {Γ} A B {x} {y} φ (picode A B x .snd .fst e))
    Psh-Π-structure .Π-Structure.ΠTy {Γ} A B .F-id {x} = funExt λ e →
      cong (invEq (picode A B x .snd)) (restrictId {Γ} A B (picode A B x .snd .fst e))
      ∙ retEq (picode A B x .snd) e
    Psh-Π-structure .Π-Structure.ΠTy {Γ} A B .F-seq {x} {y} {z} φ ψ = funExt λ e →
      cong (invEq (picode A B z .snd))
           (restrictSeq {Γ} A B φ ψ (picode A B x .snd .fst e))
      ∙ cong (λ v → invEq (picode A B z .snd) (restrict {Γ} A B ψ v))
             (sym (secEq (picode A B y .snd)
                         (restrict {Γ} A B φ (picode A B x .snd .fst e))))
    Psh-Π-structure .Π-Structure.ΠTyNat = {!!}
    Psh-Π-structure .Π-Structure.ΠTmIso = {!!}
    Psh-Π-structure .Π-Structure.ΠTmIsoInvNat = {!!}
