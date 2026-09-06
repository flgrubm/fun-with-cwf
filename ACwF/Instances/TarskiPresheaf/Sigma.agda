{-# OPTIONS --lossy-unification #-}
module ACwF.Instances.TarskiPresheaf.Sigma where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Functions.FunExtEquiv
open import Cubical.Data.Sigma
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import TarskiUniverse.Base
open import TarskiUniverse.Properties
open import Utils.TarskiPresheaf
open import ACwF.Base
open import ACwF.Sigma
open import ACwF.Instances.TarskiPresheaf.Base

open Category
open Functor
open NatTrans

module _ {ℓob ℓhom ℓU ℓEl : Level} (C : Category ℓob ℓhom) {U : Type ℓU} (Univ : TarskiUniverse ℓEl U) where
  open TarskiUniverse Univ
  open Algebraic (PRESHEAFU C TU)
  open CwF (Psh-CwF C Univ)

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
  Psh-Σ-structure : Σ-Structure (PRESHEAFU C TU) (Psh-CwF C Univ)
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
        sndPath = ElPathP TU cand
      in congP (λ j z → pairSigma {B = λ v → B .F-ob (bobj v j)} av z) sndPath i)
