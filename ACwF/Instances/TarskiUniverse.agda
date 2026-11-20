module ACwF.Instances.TarskiUniverse where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Function
open import Cubical.Functions.FunExtEquiv
open import Cubical.Data.Sigma
open import Cubical.Data.Empty as ⊥ using (⊥)

open import Cubical.Categories.Category

open import ACwF.Base
open import ACwF.Sigma
open import ACwF.Pi
open import ACwF.Eq
open import ACwF.Unit
open import ACwF.Empty
open import ACwF.Quotient

open import TarskiUniverse.Base
open import TarskiUniverse.Properties
open import Utils.TarskiQuotient

open import Agda.Builtin.Unit

open Iso
open Category

module _ {ℓU ℓEl : Level} {U : Type ℓU} (Univ : TarskiUniverse ℓEl U) where

  open Algebraic
  open TarskiUniverse Univ

  module _ where
    open CwF

    UCwF : CwF (UCat TU) (ℓ-max ℓU ℓEl) ℓEl
    UCwF .⟨⟩ .fst          = Unit
    UCwF .⟨⟩ .snd _ .fst _ = isContrElUnit .fst
    UCwF .⟨⟩ .snd Γ .snd σ = funExt (λ x → isContrElUnit .snd (σ x))
    UCwF .Ty Γ             = El Γ → U
    UCwF .isSetTy Γ        = isSet→ isSetU
    UCwF ._[_]Ty A σ x     = A (σ x)
    UCwF .[id]Ty _         = refl
    UCwF .[][]Ty _ _ _     = refl
    UCwF .Tm Γ A           = (x : El Γ) → El (A x)
    UCwF .isSetTm _ A      = isSetΠ (λ x → isSetEl (A x))
    UCwF ._[_]Tm a σ x     = a (σ x)
    UCwF .[id]Tm _         = refl
    UCwF .[][]Tm _ _ _     = refl
    UCwF ._▹_              = Sigma
    UCwF .p                = fstSigma
    UCwF .q                = sndSigma
    UCwF ._⁺ σ s           = pairSigma (σ (fstSigma s)) (sndSigma s)
    UCwF .⟨_⟩ a x          = pairSigma x (a x)
    UCwF .⟨⟩∘ a σ          = funExt (λ x → cong₂ pairSigma (sym (cong σ (fstPairSigma x (a (σ x))))) (symP (sndPairSigma x (a (σ x)))))
    UCwF .p⁺∘⟨q⟩≡id        = funExt λ x → cong₂ pairSigma (cong fstSigma (fstPairSigma _ _)) (sndPairSigma _ _) ∙ ηSigma _
    UCwF .∘⁺ σ τ           = funExt λ x → cong₂ pairSigma (cong τ (sym (fstPairSigma _ _))) (symP (sndPairSigma _ _))
    UCwF .id⁺              = funExt λ x → ηSigma _
    UCwF .p∘⁺ σ            = funExt λ x → fstPairSigma _ _
    UCwF .[p][⁺]Ty B σ     = funExt λ x → cong B (fstPairSigma _ _)
    UCwF .q[⁺]Tm σ         = funExt λ x → sndPairSigma _ _
    UCwF .p∘⟨⟩≡id a        = funExt λ x → fstPairSigma _ _
    UCwF .[p][⟨⟩]Ty B a    = funExt λ x → cong B (fstPairSigma _ _)
    UCwF .q[⟨⟩]Tm a        = funExt λ x → sndPairSigma _ _

  module U-Σ
    where

    open Algebraic
    open CwF UCwF

    U-Σ-Structure : Σ-Structure (UCat TU) UCwF
    U-Σ-Structure .Σ-Structure.ΣTy A B x                      = Sigma (A x) λ y → B (pairSigma x y)
    U-Σ-Structure .Σ-Structure.ΣTyNat A B σ                   = funExt λ x → cong (Sigma (A (σ x))) (funExt λ y → cong B (cong₂ pairSigma (cong σ (sym (fstPairSigma _ _))) (symP (sndPairSigma _ _))))
    U-Σ-Structure .Σ-Structure.ΣTmIso A B                     = compIso (codomainIsoDep (λ _ → SigmaIso _ _)) Σ-Π-Iso
    U-Σ-Structure .Σ-Structure.coerce A B a σ                 = funExt λ x → cong B (cong₂ pairSigma (cong σ (sym (fstPairSigma _ _))) (symP (sndPairSigma _ _)))
    U-Σ-Structure .Σ-Structure.ΣTmIsoInvNat {Γ} {Δ} A B a b σ = funExt λ x → congP (λ _ z → uncurry pairSigma (a (σ x) , z)) (symP (toPathP (let
      -- don't look at this
      goal :
        transp (λ i → El (B (pairSigma (σ (fstPairSigma {B = λ v → A (σ v)} x (a (σ x)) i)) (sndPairSigma {B = λ v → A (σ v)} x (a (σ x)) i))))
        i0
        (transp (λ i → El (B (pairSigma (σ (fstPairSigma {B = λ v → A (σ v)} (transp (λ j → El Δ) i x) (a (σ (transp (λ j → El Δ) i x))) (~ i))) (sndPairSigma {B = λ v → A (σ v)} (transp (λ j → El Δ) i x) (a (σ (transp (λ j → El Δ) i x))) (~ i)))))
         i0
         (b (σ (transp (λ j → El Δ) i0 x))))
        ≡
          b (σ x)
      goal j = transp (λ i → El (B (pairSigma (σ (fstPairSigma {B = λ v → A (σ v)} x (a (σ x)) (i ∨ j))) (sndPairSigma {B = λ v → A (σ v)} x (a (σ x)) (i ∨ j)))))
        j
        (transp (λ i → El (B (pairSigma (σ (fstPairSigma {B = λ v → A (σ v)} (transp (λ _ → El Δ) (i ∨ j) x) (a (σ (transp (λ _ → El Δ) (i ∨ j) x))) (~ i ∨ j))) (sndPairSigma {B = λ v → A (σ v)} (transp (λ j → El Δ) (i ∨ j) x) (a (σ (transp (λ _ → El Δ) (i ∨ j) x))) (~ i ∨ j)))))
          j
         (b (σ (transp (λ _ → El Δ) j x))))
      in goal)))

  module U-Π (TU-Pi : hasPi TU) where
    open hasPi TU-Pi
    open Algebraic
    open CwF UCwF

    U-Π-Structure : Π-Structure (UCat TU) UCwF
    U-Π-Structure .Π-Structure.ΠTy A B x                = Pi (A x) (λ y → B (pairSigma x y))
    U-Π-Structure .Π-Structure.ΠTyNat A B σ             = funExt (λ x → cong (Pi (A (σ x))) (funExt (λ y → cong B (cong₂ pairSigma (cong σ (sym (fstPairSigma x y))) (symP (sndPairSigma x y))))))
    U-Π-Structure .Π-Structure.ΠTmIso {Γ} A B           =
      ((a : El Γ) → El (Pi (A a) (λ y → B (pairSigma a y))))           Iso⟨ codomainIsoDep (λ x → PiIso (A x) (λ y → B (pairSigma x y))) ⟩
      (∀ a b → El (B (pairSigma a b)))                                 Iso⟨ invIso curryIso ⟩
      (((a , b) : Σ (El Γ) (λ z → El (A z))) → El (B (pairSigma a b))) Iso⟨ invIso (domIsoDep (invIso (SigmaIso _ _))) ⟩
      (((x : El (Sigma Γ A)) → El (B x)))                              ∎Iso
    U-Π-Structure .Π-Structure.ΠTmIsoInvNat A B M σ i x =
      lamPi
        (λ y → M (pairSigma (σ (fstPairSigma x y (~ i))) (sndPairSigma {B = A [ σ ]Ty} x y (~ i))))

  module U-Eq (TU-Eq : hasEq TU) where
    open hasEq TU-Eq
    open Algebraic
    open CwF UCwF

    U-Eq-Structure : Eq-Structure UCwF
    U-Eq-Structure .Eq-Structure.EqTy A a b x            = Eq (A x) (a x) (b x)
    U-Eq-Structure .Eq-Structure.EqTyNat _ _ _ _         = refl
    U-Eq-Structure .Eq-Structure.EqTmIso {Γ} A a b       =
      ((x : El Γ) → El (Eq (A x) (a x) (b x))) Iso⟨ codomainIsoDep (λ x → EqIso (A x) (a x) (b x)) ⟩
      ((x : El Γ) → a x ≡ b x)                 Iso⟨ funExtIso ⟩
      (a ≡ b)                                  ∎Iso
    U-Eq-Structure .Eq-Structure.EqTmIsoInvNat _ _ _ _ _ = refl

  module U-Unit where
    U-Unit-Structure : Unit-Structure UCwF
    U-Unit-Structure .Unit-Structure.UnitTy _             = Unit
    U-Unit-Structure .Unit-Structure.UnitTyNat _          = refl
    U-Unit-Structure .Unit-Structure.UnitTmIso .fun _     = tt
    U-Unit-Structure .Unit-Structure.UnitTmIso .inv _ _   = isContrElUnit .fst
    U-Unit-Structure .Unit-Structure.UnitTmIso .sec _     = refl
    U-Unit-Structure .Unit-Structure.UnitTmIso .ret a i x = isContrElUnit .snd (a x) i
    U-Unit-Structure .Unit-Structure.UnitTmIsoInvNat _ _  = refl

  module U-⊥ (hasEmptyTU : hasEmpty TU) where
    open hasEmpty hasEmptyTU
    U-⊥-Structure : ⊥-Structure UCwF
    U-⊥-Structure .⊥-Structure.⊥Ty _         = Empty
    U-⊥-Structure .⊥-Structure.⊥TyNat _      = refl
    U-⊥-Structure .⊥-Structure.⊥-elim _ x    = ⊥.rec (EmptyIso .fun (sndSigma x))
    U-⊥-Structure .⊥-Structure.⊥-elimNat _ _ = funExt λ x → ⊥.rec (EmptyIso .fun (sndSigma x))

  -- | Quotients, fibrewise: `QTy A R x` is the code for the quotient of
  -- `A x` by `R` at `x`.  Two variables over `x` are re-paired into an
  -- element of `Γ ▹ A ▹ A [ p ]Ty` by `pair²` (Utils.TarskiQuotient), and
  -- `σ ⁺²` re-pairs, so that the relation of a substituted quotient is `R`
  -- at a re-paired triple.  Elimination is `isEquivPrecompCls`.
  module U-Quot (TU-Quot : hasQuotient TU) where
    open hasQuotient TU-Quot
    open Algebraic
    open CwF UCwF
    open Fibrewise Univ

    private variable
      Γ Δ : U

    private
      module QF {Γ : U} {A : Ty Γ} (R : Ty (Γ ▹ A ▹ A [ p ]Ty)) = QuotRel TU-Quot A R

    U-QTy : (A : Ty Γ) (R : Ty (Γ ▹ A ▹ A [ p ]Ty))
          → -------------------------------------------
            Ty Γ
    U-QTy A R = QF.Q R

    -- re-pair the three components, with `σ` applied to the first
    U-⁺² : {A : Ty Γ} (σ : El Δ → El Γ)
         → ------------------------------------------------------------
           El (Δ ▹ A [ σ ]Ty ▹ A [ σ ]Ty [ p ]Ty) → El (Γ ▹ A ▹ A [ p ]Ty)
    U-⁺² {A = A} σ w = pair² A (σ (t .fst) , t .snd)
      where t = unpair² (λ x → A (σ x)) w

    -- `(σ ⁺) ⁺` and `σ ⁺²` differ only in the third component, which `σ ⁺²`
    -- moves along the β-law of the inner pair
    U-⁺²≡ : {A : Ty Γ} (σ : El Δ → El Γ)
          → -----------------------------------------------------------------------------
            PathP (λ i → El (Δ ▹ A [ σ ]Ty ▹ [p][⁺]Ty {A = A} A σ i) → El (Γ ▹ A ▹ A [ p ]Ty))
                  (_⁺ {A = A [ p ]Ty} (_⁺ {A = A} σ)) (U-⁺² σ)
    U-⁺²≡ {A = A} σ i w = pairSigma (pairSigma (σ x) a) (transp (λ j → El (A (β (i ∧ ~ j)))) (~ i) (sndSigma w))
      where
        x = fstSigma (fstSigma w)
        a = sndSigma (fstSigma w)
        β : fstSigma (pairSigma {B = A} (σ x) a) ≡ σ x
        β = fstPairSigma (σ x) a

    -- the relations agree at each pair of elements: unpairing a re-paired
    -- triple gives it back
    U-QTyNat : (A : Ty Γ) (R : Ty (Γ ▹ A ▹ A [ p ]Ty)) (σ : El Δ → El Γ)
             → -------------------------------------------------------------
               U-QTy A R [ σ ]Ty ≡ U-QTy (A [ σ ]Ty) (R [ U-⁺² σ ]Ty)
    U-QTyNat A R σ = funExt λ x → cong (Quot (A (σ x))) (funExt λ a → funExt λ b →
      cong (λ t → R (pair² A (σ (t .fst) , t .snd)))
           (sym (unpair²-pair² (λ x → A (σ x)) (x , a , b))))

    -- a class lies over `U-QTyNat`
    U-classQuotNat : (A : Ty Γ) (R : Ty (Γ ▹ A ▹ A [ p ]Ty)) (σ : El Δ → El Γ) (a : Tm Δ (A [ σ ]Ty))
                   → ---------------------------------------------------------------------------------
                     PathP (λ i → Tm Δ (U-QTyNat A R σ i)) (λ x → classQuot (a x)) (λ x → classQuot (a x))
    U-classQuotNat A R σ a i x = classQuot (a x)

    -- `q [ classSub ]Tm` is the second component of a canonical pair
    U-q[classSub] : {A : Ty Γ} {R : Ty (Γ ▹ A ▹ A [ p ]Ty)}
                  → -----------------------------------------------------------------------------------
                    PathP (λ i → Tm (Γ ▹ A) (λ w → U-QTy A R (fstPairSigma {B = U-QTy A R} (fstSigma w) (classQuot (sndSigma w)) i)))
                          (q [ QF.cls R ]Tm) (λ w → classQuot (sndSigma w))
    U-q[classSub] {R = R} i w = sndPairSigma {B = U-QTy _ R} (fstSigma w) (classQuot (sndSigma w)) i

    -- the class of the first variable of a related pair is that of the second
    U-classSubSound : {A : Ty Γ} {R : Ty (Γ ▹ A ▹ A [ p ]Ty)}
                    → ------------------------------------------------------------------
                      Path (El (Γ ▹ A ▹ A [ p ]Ty ▹ R) → El (Γ ▹ U-QTy A R))
                           (λ z → QF.cls R (QF.fstVar R z)) (λ z → QF.cls R (QF.sndVar R z))
    U-classSubSound {R = R} = funExt (QF.cls-sound R)

    U-Quot-Structure : Quot-Structure UCwF
    U-Quot-Structure .Quot-Structure.QTy                    = U-QTy
    U-Quot-Structure .Quot-Structure._⁺²                    = U-⁺²
    U-Quot-Structure .Quot-Structure.⁺²≡                    = U-⁺²≡
    U-Quot-Structure .Quot-Structure.QTyNat                 = U-QTyNat
    U-Quot-Structure .Quot-Structure.classTm a x            = classQuot (a x)
    U-Quot-Structure .Quot-Structure.classTmNat {A = A} {R = R} a σ = U-classQuotNat A R σ (a [ σ ]Tm)
    U-Quot-Structure .Quot-Structure.classSub {R = R}       = QF.cls R
    U-Quot-Structure .Quot-Structure.p∘classSub             = funExt λ w → fstPairSigma _ _
    U-Quot-Structure .Quot-Structure.q[classSub] {A = A} {R = R} =
      reindex (U-q[classSub] {A = A} {R = R} ∙Tm U-classQuotNat A R p q)
    U-Quot-Structure .Quot-Structure.classSubSound          = U-classSubSound
    U-Quot-Structure .Quot-Structure.isEquivQuotCases A R P =
      QF.isEquivPrecompCls R P _ (λ _ → isOfHLevelPathP' 1 (isSetTm _ _) _ _)
        (λ m r → QF.toRespects R P m (λ z i → reindex {e' = λ i z → P (U-classSubSound i z)} r i z)) _ (λ _ → refl)
