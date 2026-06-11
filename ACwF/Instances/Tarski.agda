{-# OPTIONS --lossy-unification #-}
module ACwF.Instances.Tarski where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function

open import Cubical.Functions.FunExtEquiv

open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Limits.Terminal

open import ACwF.Base
open import ACwF.Sigma

open import Agda.Builtin.Unit

open Iso
open Category

module _ {ℓU ℓEl : Level}
         (U : Type ℓU)
         (isSetU : isSet U)
         (El : U → Type ℓEl)
         (isSetEl : (Γ : U) → isSet (El Γ))
         (Unit : U)
         (isTerminalUnit : isContr (El Unit))
         (Sig : (A : U) → (El A → U) → U)
         -- (SigIso : (A : U) (B : El A → U) → Iso (El (Sig A B)) (Σ[ x ∈ El A ] El (B x)))
         (fstSig : {A : U} {B : El A → U} → El (Sig A B) → El A)
         (sndSig : {A : U} {B : El A → U} (p : El (Sig A B)) → El (B (fstSig p)))
         (pairSig : {A : U} {B : El A → U} (x : El A) → (El (B x)) → El (Sig A B))
         (ηSig : {A : U} {B : El A → U} (p : El (Sig A B)) → pairSig (fstSig p) (sndSig p) ≡ p)
         (fstPairSig : {A : U} {B : El A → U} (x : El A) (y : El (B x)) → fstSig (pairSig {B = B} x y) ≡ x)
         (sndPairSig : {A : U} {B : El A → U} (x : El A) (y : El (B x)) → PathP (λ i → El (B (fstPairSig {B = B} x y i))) (sndSig (pairSig {B = B} x y)) y)
  where

  PairIso : {A : U} {B : El A → U} → Iso (El (Sig A B)) (Σ[ x ∈ El A ] El (B x))
  PairIso .fun p .fst = fstSig p
  PairIso .fun p .snd = sndSig p
  PairIso .inv = uncurry pairSig
  PairIso .sec (x , y) = ΣPathP ((fstPairSig x y) , sndPairSig x y)
  PairIso .ret = ηSig
  
  UCat : Category ℓU ℓEl
  UCat .ob = U
  UCat .Hom[_,_] Δ Γ = El Δ → El Γ
  UCat .id x = x
  UCat ._⋆_ f g x = g (f x)
  UCat .⋆IdL _ = refl
  UCat .⋆IdR _ = refl
  UCat .⋆Assoc _ _ _ = refl
  UCat .isSetHom {y = y} = isSet→ (isSetEl y)

  open Algebraic

  module _ where
    open CwF

    UCwF : CwF UCat (ℓ-max ℓU ℓEl) ℓEl
    UCwF .⟨⟩ .fst = Unit
    UCwF .⟨⟩ .snd _ .fst _ = isTerminalUnit .fst
    UCwF .⟨⟩ .snd Γ .snd σ = funExt (λ x → isTerminalUnit .snd (σ x))
    UCwF .Ty Γ = El Γ → U
    UCwF .isSetTy Γ = isSet→ isSetU
    UCwF ._[_]Ty A σ x = A (σ x)
    UCwF .[id]Ty _ = refl
    UCwF .[][]Ty _ _ _ = refl
    UCwF .Tm Γ A = (x : El Γ) → El (A x)
    UCwF .isSetTm _ A = isSetΠ (λ x → isSetEl (A x))
    UCwF ._[_]Tm a σ x = a (σ x)
    UCwF .[id]Tm _ = refl
    UCwF .[][]Tm _ _ _ = refl
    UCwF ._⋆_ = Sig
    UCwF .p = fstSig
    UCwF .q = sndSig
    UCwF ._⁺ σ s = pairSig (σ (fstSig s)) (sndSig s)
    UCwF .⟨_⟩ a x = pairSig x (a x)
    UCwF .⟨⟩∘ {Γ = Γ} {Δ = Δ} {A = A} a σ = funExt (λ x → cong₂ pairSig (sym (cong σ (fstPairSig x (a (σ x))))) (symP (sndPairSig x (a (σ x)))))
    --  funExt (λ x → ?)cong₂ pairSig (cong σ (sym (fstPairSig x _))) (symP {!sndPairSig!})) -- funExt (λ x → cong (λ m → SigIso Γ A .inv (σ (m .fst) , m .snd)) (sym (SigIso Δ (λ y → A (σ y)) .sec (x , a (σ x)))))
--     UCwF .p⁺∘⟨q⟩≡id {Γ = Γ} {A = A} =
--       funExt (λ x → cong (λ m → SigIso Γ A .inv m)
--                          (cong (λ m → SigIso Γ A .fun (m .fst) .fst , m .snd) (SigIso (Sig Γ A) (λ x₁ → A (fun (SigIso Γ A) x₁ .fst)) .sec (x , fun (SigIso Γ A) x .snd)))
--                          ∙ SigIso Γ A .ret x)
--     UCwF .∘⁺ {Γ = Γ} {Θ = Θ} {Δ = Δ} {A = A} σ τ =
--       funExt (λ x → cong (λ m → SigIso Γ A .inv ((τ (m .fst)) , (m .snd)))
--                          (sym (SigIso Δ (λ y → A (τ y)) .sec
--                                 (σ (fun (SigIso Θ (λ x₁ → A (τ (σ x₁)))) x .fst) , fun (SigIso Θ (λ x₁ → A (τ (σ x₁)))) x .snd))))
--     UCwF .id⁺ {Γ = Γ} {A = A} = funExt (λ x → SigIso Γ A .ret x)
--     UCwF .p∘⁺ {Γ = Γ} {Δ = Δ} {A = A} σ = funExt (λ x → cong fst (SigIso Γ A .sec (σ (fun (SigIso Δ ((UCwF [ A ]Ty) σ)) x .fst) ,
--                                                                                    fun (SigIso Δ ((UCwF [ A ]Ty) σ)) x .snd)))
--     UCwF .[p][⁺]Ty {Γ = Γ} {Δ = Δ} {A = A} B σ = 
--       funExt (λ x → cong (λ m → B (m .fst))
--                          (SigIso Γ A .sec (σ (fun (SigIso Δ (UCwF ._[_]Ty A σ)) x .fst)
--                                            ,
--                                            fun (SigIso Δ (UCwF ._[_]Ty A σ)) x .snd)))
--     UCwF .q[⁺]Tm {Γ = Γ} {Δ = Δ} {A = A} σ = funExt (λ x → symP (toPathP ({!!} ∙ sym (cong (λ m → m .snd .snd) {!SigIso Γ A .sec !}))))
--     UCwF .p∘⟨⟩≡id {Γ = Γ} {A = A} a = funExt (λ x → cong fst (SigIso Γ A .sec (x , a x)))
--     UCwF .[p][⟨⟩]Ty {Γ = Γ} {A = A} B a = funExt (λ x → cong (λ m → B (m .fst)) (SigIso Γ A .sec (x , a x)))
--     UCwF .q[⟨⟩]Tm = {!!}

--   open Algebraic
--   open CwF UCwF

--   U-Σ-Structure : Σ-Structure UCat UCwF
--   U-Σ-Structure .Σ-Structure.ΣTy {Γ = Γ} A B x = Sig (A x) λ y → B (SigIso Γ A .inv (x , y))
--   U-Σ-Structure .Σ-Structure.ΣTyNat {Γ = Γ} {Δ = Δ} A B σ =
--     funExt (λ x → cong (Sig (A (σ x)))
--                        (funExt (λ y → cong (λ m → B (SigIso Γ A .inv (σ (m .fst) , m .snd)))
--                                            (sym (SigIso Δ (λ y → A (σ y)) .sec (x , y))))))
--   U-Σ-Structure .Σ-Structure.ΣTmIso {Γ = Γ} A B = compIso (codomainIsoDep (λ x → SigIso (A x) (λ y → B (inv (SigIso Γ A) (x , y))))) Σ-Π-Iso
--   U-Σ-Structure .Σ-Structure.coerce {Γ = Γ} {Δ = Δ} A B a σ =
--     funExt (λ x → cong (λ m → B (SigIso Γ A .inv (σ (m .fst) , m .snd)))
--                        (sym (SigIso Δ (λ y → A (σ y)) .sec (x , a (σ x)))))
--   U-Σ-Structure .Σ-Structure.ΣTmIsoInvNat {Γ = Γ} A B a b σ = funExt (λ x →
--     let
--       goal : PathP
--               (λ z →
--                  El
--                  (funExt
--                   (λ x₁ i →
--                      Sig (A (σ x₁))
--                      (funExt
--                       (λ y i₁ →
--                          B
--                          (inv (SigIso Γ A)
--                           (σ (sec (SigIso _ (λ y₁ → A (σ y₁))) (x₁ , y) (~ i₁) .fst) ,
--                            sec (SigIso _ (λ y₁ → A (σ y₁))) (x₁ , y) (~ i₁) .snd)))
--                       i))
--                   z x))
--               (inv (SigIso (A (σ x)) (λ y → B (inv (SigIso Γ A) (σ x , y))))
--                (a (σ x) , b (σ x)))
--               (inv
--                (SigIso (A (σ x))
--                 (λ y →
--                    B
--                    (inv (SigIso Γ A)
--                     (σ
--                      (fun (SigIso _ (λ x₁ → A (σ x₁)))
--                       (inv (SigIso _ (λ x₁ → A (σ x₁))) (x , y)) .fst)
--                      ,
--                      fun (SigIso _ (λ x₁ → A (σ x₁)))
--                      (inv (SigIso _ (λ x₁ → A (σ x₁))) (x , y)) .snd))))
--                (a (σ x) ,
--                 subst (λ A₁ → (x₁ : El _) → El (A₁ x₁))
--                 (funExt
--                  (λ x₁ i →
--                     B
--                     (inv (SigIso Γ A)
--                      (σ (sec (SigIso _ (λ y → A (σ y))) (x₁ , a (σ x₁)) (~ i) .fst) ,
--                       sec (SigIso _ (λ y → A (σ y))) (x₁ , a (σ x₁)) (~ i) .snd))))
--                 (λ x₁ → b (σ x₁)) x))
--       goal = {!!}
--     in goal)


-- --   V-Σ-Structure : Σ-Structure-CwF VCat VCwF
-- --   V-Σ-Structure .Σ-Structure-CwF.ΣTy A B x = Σ⁰ (A x) (λ y → B (x , y))
-- --   V-Σ-Structure .Σ-Structure-CwF.ΣTyNat A B σ = refl
-- --   V-Σ-Structure .Σ-Structure-CwF.ΣTmIso A B = Σ-Π-Iso
-- --   V-Σ-Structure .Σ-Structure-CwF.coerce A B a σ = refl
-- --   V-Σ-Structure .Σ-Structure-CwF.ΣTmIsoInvNat {Δ = Δ} _ _ _ b σ =
-- --     funExt λ x → ΣPathP (
-- --       refl ,
-- --       sym ((cong (λ M → M x)) (substRefl {B = Tm Δ} ((λ x₁ → b (σ x₁))))))
