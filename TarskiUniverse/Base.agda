module TarskiUniverse.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism

record TarskiUniverse (ℓU ℓEl : Level) : Type (ℓ-suc (ℓ-max ℓU ℓEl)) where
  field
    U : Type ℓU
    isSetU : isSet U

    El : U → Type ℓEl
    isSetEl : (Γ : U) → isSet (El Γ)

    -- TODO: rename? Maybe state that it decodes to Builtin.Unit instead?
    Unit : U
    isContrElUnit : isContr (El Unit)

    Sig : (A : U) → (El A → U) → U
    SigIso : (A : U) (B : El A → U)
           → Iso (El (Sig A B)) (Σ[ x ∈ El A ] El (B x))

    Pi : (A : U) (B : El A → U) → U
    PiIso : (A : U) (B : El A → U)
          → Iso (El (Pi A B)) ((x : El A) → El (B x))

  open Iso

  fstSig : {A : U} {B : El A → U} → El (Sig A B) → El A
  fstSig p = SigIso _ _ .fun p .fst

  sndSig : {A : U} {B : El A → U} (p : El (Sig A B)) → El (B (fstSig p))
  sndSig p = SigIso _ _ .fun p .snd

  pairSig : {A : U} {B : El A → U} (x : El A) (y : El (B x)) → El (Sig A B)
  pairSig x y = SigIso _ _ .inv (x , y)

  ηSig : {A : U} {B : El A → U} (p : El (Sig A B))
       → pairSig (fstSig p) (sndSig p) ≡ p
  ηSig p = SigIso _ _ .ret p

  fstPairSig : {A : U} {B : El A → U} (x : El A) (y : El (B x))
             → fstSig (pairSig {B = B} x y) ≡ x
  fstPairSig x y = cong fst (SigIso _ _ .sec (x , y))

  sndPairSig : {A : U} {B : El A → U} (x : El A) (y : El (B x))
             → PathP (λ i → El (B (fstPairSig {B = B} x y i))) (sndSig (pairSig {B = B} x y)) y
  sndPairSig x y = cong snd (SigIso _ _ .sec (x , y))

  appPi : {A : U} {B : El A → U} (f : El (Pi A B)) (x : El A) → El (B x)
  appPi = PiIso _ _ .fun

  lamPi : {A : U} {B : El A → U} → ((x : El A) → El (B x)) → El (Pi A B)
  lamPi = PiIso _ _ .inv

  βPi : {A : U} {B : El A → U} (f : (x : El A) → El (B x)) → appPi (lamPi f) ≡ f
  βPi = PiIso _ _ .sec

  ηPi : {A : U} {B : El A → U} (f : El (Pi A B)) → lamPi (appPi f) ≡ f
  ηPi = PiIso _ _ .ret
