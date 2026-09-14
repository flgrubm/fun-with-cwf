module TarskiUniverse.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function

open import Cubical.Data.Sigma
open import Cubical.Data.Unit hiding (Unit)
open import Cubical.HITs.PropositionalTruncation

-- A "bare Tarski universe" is a set U of codes with a set-valued
-- decoding function El.  We parameterize by U to make it easier to
-- transport between equal types
record BareTarskiUniverse {ℓU : Level} (ℓEl : Level) (U : Type ℓU) : Type (ℓ-suc (ℓ-max ℓU ℓEl)) where
  field
    isSetU : isSet U

    El : U → Type ℓEl
    isSetEl : (Γ : U) → isSet (El Γ)

-- Structures on Tarski universes
module _ {ℓU ℓEl : Level} {U : Type ℓU} (TU : BareTarskiUniverse ℓEl U) where
  open Iso
  open BareTarskiUniverse TU

  record hasUnit : Type (ℓ-max ℓU ℓEl) where
    field
      Unit : U
      isContrElUnit : isContr (El Unit)

    ElUnit≡Unit* : El Unit ≡ Unit*
    ElUnit≡Unit* = isContr→≡Unit* isContrElUnit

  record hasSigma : Type (ℓ-max ℓU ℓEl) where
    field
      Sigma    : (A : U) → (El A → U) → U
      SigmaIso : (A : U) (B : El A → U)
               → Iso (El (Sigma A B)) (Σ[ x ∈ El A ] El (B x))

    fstSigma : {A : U} {B : El A → U} → El (Sigma A B) → El A
    fstSigma p = SigmaIso _ _ .fun p .fst

    sndSigma : {A : U} {B : El A → U} (p : El (Sigma A B)) → El (B (fstSigma p))
    sndSigma p = SigmaIso _ _ .fun p .snd

    pairSigma : {A : U} {B : El A → U} (x : El A) (y : El (B x)) → El (Sigma A B)
    pairSigma x y = SigmaIso _ _ .inv (x , y)

    ηSigma : {A : U} {B : El A → U} (p : El (Sigma A B))
         → pairSigma (fstSigma p) (sndSigma p) ≡ p
    ηSigma p = SigmaIso _ _ .ret p

    fstPairSigma : {A : U} {B : El A → U} (x : El A) (y : El (B x))
               → fstSigma (pairSigma {B = B} x y) ≡ x
    fstPairSigma x y = cong fst (SigmaIso _ _ .sec (x , y))

    sndPairSigma : {A : U} {B : El A → U} (x : El A) (y : El (B x))
               → PathP (λ i → El (B (fstPairSigma {B = B} x y i))) (sndSigma (pairSigma {B = B} x y)) y
    sndPairSigma x y = cong snd (SigmaIso _ _ .sec (x , y))

    SigmaPathP : ∀ {A} {B} → {x y : El (Sigma A B)}
                 (fst≡ : fstSigma x ≡ fstSigma y)
               → PathP (λ i → El (B (fst≡ i))) (sndSigma x) (sndSigma y) → x ≡ y
    SigmaPathP {x = x} {y = y} fst≡ snd≡ =
      sym (ηSigma x) ∙∙ cong (uncurry pairSigma) (ΣPathP (fst≡ , snd≡)) ∙∙ ηSigma y

  record hasPi : Type (ℓ-max ℓU ℓEl) where
    field
      Pi : (A : U) (B : El A → U) → U
      PiIso : (A : U) (B : El A → U)
            → Iso (El (Pi A B)) ((x : El A) → El (B x))

    appPi : {A : U} {B : El A → U} (f : El (Pi A B)) (x : El A) → El (B x)
    appPi = PiIso _ _ .fun

    lamPi : {A : U} {B : El A → U} → ((x : El A) → El (B x)) → El (Pi A B)
    lamPi = PiIso _ _ .inv

    βPi : {A : U} {B : El A → U} (f : (x : El A) → El (B x)) → appPi (lamPi f) ≡ f
    βPi = PiIso _ _ .sec

    ηPi : {A : U} {B : El A → U} (f : El (Pi A B)) → lamPi (appPi f) ≡ f
    ηPi = PiIso _ _ .ret

  record hasEq : Type (ℓ-max ℓU ℓEl) where
    field
      Eq : (A : U) → (a b : El A) → U
      EqIso : ∀ A a b → Iso (El (Eq A a b)) (a ≡ b)

    eqIntro : ∀ {A} {a} {b} → a ≡ b → El (Eq A a b)
    eqIntro = EqIso _ _ _ .Iso.inv

    eqElim : ∀ {A} {a} {b} → El (Eq A a b) → a ≡ b
    eqElim = EqIso _ _ _ .Iso.fun

-- As we are only interested in Tarski universes with Unit and Sigma
-- we use the name "Tarski universe" for these universes
-- record TarskiUniverse {ℓU : Level} (ℓEl : Level) (U : Type ℓU) : Type (ℓ-max (ℓ-suc ℓU) (ℓ-suc ℓEl)) where
--   field
--     TU         : BareTarskiUniverse ℓEl U
--     hasUnitTU  : hasUnit TU
--     hasSigmaTU : hasSigma TU

--   open BareTarskiUniverse TU public
--   open hasUnit hasUnitTU public
--   open hasSigma hasSigmaTU public

TarskiUniverse : {ℓU : Level} (ℓEl : Level) (U : Type ℓU) → Type (ℓ-suc (ℓ-max ℓU ℓEl))
TarskiUniverse ℓEl U = Σ[ TU ∈ BareTarskiUniverse ℓEl U ] hasUnit TU × hasSigma TU

isTarskiUniverse : {ℓU : Level} (ℓEl : Level) (U : Type ℓU) → Type (ℓ-suc (ℓ-max ℓU ℓEl))
isTarskiUniverse ℓEl U = ∥ TarskiUniverse ℓEl U ∥₁
