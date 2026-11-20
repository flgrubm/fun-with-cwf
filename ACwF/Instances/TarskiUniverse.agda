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
open import ACwF.Universe

open import TarskiUniverse.Base
open import TarskiUniverse.Properties

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

  -- | An internal universe of the Tarski universe is a universe in the CwF
  -- of families: the codes are the constant family `UnivCode`, and the
  -- family over the extension by codes decodes the second component.
  -- Extending the context by codes goes through `pairSigma`, so a code `c`
  -- is seen by `El c` as `codeAt c` (its round trip through the pair),
  -- equal to `c` by `sndPairSigma`.
  module U-Univ (𝒰 : hasUniverse TU) where
    open hasUniverse 𝒰 renaming (Univ to UnivCode)
    open Algebraic
    open CwF UCwF

    private variable
      Δ Γ : U

    -- `σ ⁺` is built from `pairSigma`: pushing a pair through `σ` and
    -- re-pairing gives the pair back
    pairσ : {A : El Γ → U} (σ : El Δ → El Γ) (x : El Δ) (y : El (A (σ x)))
          → --------------------------------------------------------------------
            pairSigma {B = A} (σ x) y
          ≡ pairSigma {B = A} (σ (fstSigma (pairSigma {B = λ v → A (σ v)} x y)))
                              (sndSigma (pairSigma {B = λ v → A (σ v)} x y))
    pairσ {A = A} σ x y =
      cong₂ (pairSigma {B = A}) (cong σ (sym (fstPairSigma {B = λ v → A (σ v)} x y)))
                                (symP (sndPairSigma {B = λ v → A (σ v)} x y))

    -- the code of `c` at `x`, read back from the context extension
    codeAt : ((x : El Γ) → El UnivCode) → (x : El Γ) → El UnivCode
    codeAt c x = sndSigma (pairSigma {B = λ _ → UnivCode} x (c x))

    -- reading a code back from the context extension does not change it
    codeβ : (x : El Γ) (c : El UnivCode)
          → ------------------------------------------------------------
            sndSigma (pairSigma {B = λ _ → UnivCode} x c) ≡ c
    codeβ x c = sndPairSigma {B = λ _ → UnivCode} x c

    -- codes related along σ are related after the round trip
    codeAtNat : (σ : El Δ → El Γ) {c : (x : El Γ) → El UnivCode} {c' : (x : El Δ) → El UnivCode}
              → (λ x → c (σ x)) ≡ c' → (x : El Δ)
              → ----------------------------------------------
                codeAt c (σ x) ≡ codeAt c' x
    codeAtNat σ e x = codeβ (σ x) _ ∙∙ funExt⁻ e x ∙∙ sym (codeβ x _)

    U-Univ-Structure : Univ-Structure UCwF
    U-Univ-Structure .Univ-Structure.UTy _       = UnivCode
    U-Univ-Structure .Univ-Structure.UTyNat _    = refl
    U-Univ-Structure .Univ-Structure.ElTy s      = decode (sndSigma s)
    U-Univ-Structure .Univ-Structure.ElTyNat σ   = funExt λ s → cong decode (codeβ (σ (fstSigma s)) (sndSigma s))
    U-Univ-Structure .Univ-Structure.ElNat σ {c} {c'} e i x = decode (codeAtNat σ {c} {c'} e x i)

    open Univ-Structure U-Univ-Structure renaming (El to ElU)

    -- | A code former applied pointwise (to the code at `x` and the family
    -- over it) is natural: first move the family along `d [ σ ⁺ ] ≡ d₀`
    -- (through `pairσ`), then code and family together along `codeAtNat`
    -- and the family's `PathP` over `ElNat σ e`.
    pointwiseUNat : (F : (c : El UnivCode) → (El (decode c) → El UnivCode) → El UnivCode)
                    (σ : El Δ → El Γ) {c : Tm Γ UTy} {c' : Tm Δ UTy} (e : c [ σ ]U≈ c')
                    {d : Tm (Γ ▹ ElU c) UTy} {d' : Tm (Δ ▹ ElU c') UTy}
                  → _[_]Fam≈_ UCwF U-Univ-Structure d (σ , e) d'
                  → -----------------------------------------------------------------------------
                    Path (Tm Δ UTy) (λ x → F (codeAt c (σ x)) (λ y → d (pairSigma {B = ElU c} (σ x) y)))
                                    (λ x → F (codeAt c' x) (λ y → d' (pairSigma {B = ElU c'} x y)))
    pointwiseUNat {Δ = Δ} F σ {c} {c'} e {d} (d₀ , e₁ , e₂) =
        (λ i x → F (codeAt c (σ x)) (λ y → famStep x y i))
      ∙ (λ i x → F (codeAtNat σ {c} {c'} e x i) (λ y → e₂ i (pairSigma {B = ElNat σ {c} {c'} e i} x y)))
      where
        famStep : (x : El Δ) (y : El (ElU c (σ x)))
                → d (pairSigma {B = ElU c} (σ x) y) ≡ d₀ (pairSigma {B = ElU c [ σ ]Ty} x y)
        famStep x y = cong d (pairσ {A = ElU c} σ x y) ∙ funExt⁻ e₁ (pairSigma {B = ElU c [ σ ]Ty} x y)

    module U-Univ-Π (TU-Pi : hasPi TU) (𝒰-Pi : hasUniversePi TU 𝒰 TU-Pi) where
      open hasPi TU-Pi
      open hasUniversePi 𝒰-Pi
      open U-Π TU-Pi

      -- `piU` decodes to the Π of the decodings, after the round trips
      El-piU-at : (c : Tm Γ UTy) (d : Tm (Γ ▹ ElU c) UTy) (x : El Γ)
                → ------------------------------------------------------------------------------
                  decode (codeAt (λ x → piU (codeAt c x) (λ y → d (pairSigma {B = ElU c} x y))) x)
                ≡ Pi (decode (codeAt c x)) (λ y → decode (codeAt {Γ = Γ ▹ ElU c} d (pairSigma {B = ElU c} x y)))
      El-piU-at {Γ} c d x =
          cong decode (codeβ x _)
        ∙∙ decode-piU (codeAt c x) (λ y → d (pairSigma {B = ElU c} x y))
        ∙∙ cong (Pi (decode (codeAt c x)))
                (funExt λ y → cong decode (sym (codeβ {Γ = Γ ▹ ElU c} (pairSigma {B = ElU c} x y) _)))

      U-Univ-Π-Structure : Univ-Π-Structure UCwF U-Univ-Structure U-Π-Structure
      U-Univ-Π-Structure .Univ-Π-Structure.piU c d x                   = piU (codeAt c x) (λ y → d (pairSigma {B = ElU c} x y))
      U-Univ-Π-Structure .Univ-Π-Structure.El-piU c d                  = funExt (El-piU-at c d)
      U-Univ-Π-Structure .Univ-Π-Structure.piUNat σ {c} {c'} e {d} {d'} = pointwiseUNat piU σ {c} {c'} e {d} {d'}

    module U-Univ-Σ (𝒰-Sigma : hasUniverseSigma TU 𝒰 hasSigmaTU) where
      open hasUniverseSigma 𝒰-Sigma
      open U-Σ

      -- `sigU` decodes to the Σ of the decodings, after the round trips
      El-sigU-at : (c : Tm Γ UTy) (d : Tm (Γ ▹ ElU c) UTy) (x : El Γ)
                 → ------------------------------------------------------------------------------
                   decode (codeAt (λ x → sigU (codeAt c x) (λ y → d (pairSigma {B = ElU c} x y))) x)
                 ≡ Sigma (decode (codeAt c x)) (λ y → decode (codeAt {Γ = Γ ▹ ElU c} d (pairSigma {B = ElU c} x y)))
      El-sigU-at {Γ} c d x =
          cong decode (codeβ x _)
        ∙∙ decode-sigU (codeAt c x) (λ y → d (pairSigma {B = ElU c} x y))
        ∙∙ cong (Sigma (decode (codeAt c x)))
                (funExt λ y → cong decode (sym (codeβ {Γ = Γ ▹ ElU c} (pairSigma {B = ElU c} x y) _)))

      U-Univ-Σ-Structure : Univ-Σ-Structure UCwF U-Univ-Structure U-Σ-Structure
      U-Univ-Σ-Structure .Univ-Σ-Structure.sigU c d x                   = sigU (codeAt c x) (λ y → d (pairSigma {B = ElU c} x y))
      U-Univ-Σ-Structure .Univ-Σ-Structure.El-sigU c d                  = funExt (El-sigU-at c d)
      U-Univ-Σ-Structure .Univ-Σ-Structure.sigUNat σ {c} {c'} e {d} {d'} = pointwiseUNat sigU σ {c} {c'} e {d} {d'}
