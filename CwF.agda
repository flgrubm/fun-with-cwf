{-# OPTIONS --lossy-unification #-}

module CwF where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Isomorphism

open import Cubical.Functions.FunExtEquiv

open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Limits.Terminal

private
  variable
    ℓ ℓ' : Level

-- module V_Categorical_CwF {ℓ : Level} where

--   open import Cubical.Data.IterativeSets.Base renaming (V⁰ to V ; El⁰ to El ; isSetEl⁰ to isSetEl)
--   open import Cubical.Data.IterativeSets.Sigma
--   open import Cubical.Data.IterativeSets.Unit
--   open import Agda.Builtin.Unit

--   open Category renaming (_⋆_ to _⋆C_)

--   VCat : Category (ℓ-suc ℓ) ℓ
--   VCat .ob       = V
--   VCat .Hom[_,_] = λ Δ Γ → El Δ → El Γ
--   VCat .id       = λ x → x
--   VCat ._⋆C_     = λ f g x → g (f x)
--   VCat .⋆IdL     = λ _ → refl
--   VCat .⋆IdR     = λ _ → refl
--   VCat .⋆Assoc   = λ _ _ _ → refl
--   VCat .isSetHom {y = y} = isSet→ (isSetEl y)

--   open Categorical
--   open CwF
--   open Iso
--   open Functor

--   VCwF : CwF VCat (ℓ-suc ℓ) ℓ
--   VCwF .emptyContext    = unit⁰ , λ _ → (λ _ → lift tt) , λ _ _ _ → lift tt
--   VCwF .Ty .F-ob Γ .fst = El Γ → V {ℓ}
--   VCwF .Ty .F-ob Γ .snd = isSet→ isSetV⁰
--   VCwF .Ty .F-hom σ A x = A (σ x)
--   VCwF .Ty .F-id        = refl
--   VCwF .Ty .F-seq _ _   = refl
--   VCwF .Tm .F-ob (Γ , A) .fst = (x : El Γ) → El (A x)
--   VCwF .Tm .F-ob (Γ , A) .snd = isSetΠ (λ _ → isSetEl _)
--   VCwF .Tm .F-hom σ a x      = subst El (funExt⁻ (σ .snd) x) (a (σ .fst x)) -- TODO: why do we need a subst here?
--   VCwF .Tm .F-id             = funExt₂ (λ _ _ → transportRefl _)
--   VCwF .Tm .F-seq σ τ        = funExt₂ (λ _ _ → substComposite El _ _ _)
--   VCwF .ctxExt .F-ob (Γ , A) = Σ⁰ Γ A
--   VCwF .ctxExt .F-hom σ (x , a) .fst = σ .fst x
--   VCwF .ctxExt .F-hom σ (x , a) .snd = subst⁻ El (funExt⁻ (σ .snd) x) a
--   VCwF .ctxExt .F-id = funExt (λ x → ΣPathP (refl , transportRefl _))
--   VCwF .ctxExt .F-seq σ τ  =
--     funExt (λ x → ΣPathP ( refl
--                          , cong (λ p → subst El p (x .snd)) (isSetV⁰ _ _ _ _)
--                          ∙ substComposite El _ _ _))
--   VCwF .ctxExtIso A        = Σ-Π-Iso
--   VCwF .coerceFun A σ τ    = refl -- yay!
--   VCwF .ctxExtIsoFunNat A σ τ = ΣPathP (refl , (funExt (λ x → sym (transportRefl _))))
--   VCwF .ctxExtIsoFunNatWithoutCoerceFun A σ τ = ΣPathP (refl , (funExt (λ x → sym (transportRefl _))))
--   VCwF .coerceInv A σ τ    = refl -- yay!
--   VCwF .ctxExtIsoInvNat A σ a τ = funExt (λ x → ΣPathP (refl , (sym (transportRefl _))))
--   VCwF .ctxExtIsoInvNatWithoutCoerceInv A σ a τ = funExt (λ x → ΣPathP (refl , (sym (transportRefl _))))

--   open import Cubical.Foundations.Path

--   open Σ-Structure-CwF

--   -- help : (A : Ty[ Γ ]) (a : Tm[ Γ , A ]) (B : Ty[ Γ ⋆ A ]) (σ : Δ ⟶ Γ) → (VCwF [
--   --      (VCwF [ B ]Ty) (λ x → x , (VCwF [ a ]Tm) (λ x₁ → x₁) x) ]Ty)
--   --     σ
--   --     ≡
--   --     (VCwF [ (VCwF [ B ]Ty) (ctxExt VCwF .F-hom (σ , refl)) ]Ty)
--   --     (λ x → x , (VCwF [ (VCwF [ a ]Tm) σ ]Tm) (λ x₁ → x₁) x)
--   -- help = {!!}

--   goal : Σ-Structure-CwF VCat VCwF
--   goal .ΣTy A B x = Σ⁰ (A x) (λ y → B (x , y))
--   goal .ΣTyNat A B σ = funExt (λ x → cong (Σ⁰ (A (σ x))) (funExt (λ y → cong B (ΣPathP (refl , sym (transportRefl _))))))
--   goal .ΣTmIso A B .fun x .fst ρ = x ρ .fst
--   goal .ΣTmIso A B .fun x .snd ρ = subst (λ p → El (B (ρ , p))) (sym (transportRefl _)) (x ρ .snd)
--   goal .ΣTmIso A B .inv (x , y) ρ .fst = x ρ
--   goal .ΣTmIso A B .inv (x , y) ρ .snd = subst (λ p → El (B (ρ , p))) (transportRefl _) (y ρ)
--   goal .ΣTmIso A B .sec x = ΣPathP (refl , (funExt (λ ρ → subst⁻Subst (λ p → El (B (ρ , p))) (transportRefl _) _)))
--   goal .ΣTmIso A B .ret x = funExt (λ ρ → ΣPathP (refl , (substSubst⁻ (λ p → El (B (ρ , p))) (transportRefl _) _)))
--   goal .coerceFun = {!!}
--   goal .ΣTmIsoFunNat A B a σ = ΣPathP (funExt (λ ρ → transportRefl _ ∙ {!!}) , {!!})
--   goal .coerceInv A B a σ = funExt (λ ρ → cong B (ΣPathP (refl , cong (transport (λ _ → El (A (σ ρ)))) (sym (λ i → transp (λ _ → El (A (σ ρ))) i (transp (λ _ → El (A (σ ρ))) i (a (σ ρ))))))))
--   goal .ΣTmIsoInvNat {Δ = Δ} A B a b σ = funExt (λ ρ → ΣPathP (refl , symP (toPathP
--     let goal : transp (λ i → El (B (σ ρ , transp (λ _ → El (A (σ ρ))) i (transp (λ _ → El (A (σ ρ))) i0 (a (σ ρ))))))
--                       i0
--                       (transp (λ i → El (B (ctxExt VCwF .F-hom (σ , (λ _ x → A (σ x))) (ρ , transp (λ _ → El (A (σ ρ))) i (transp (λ _ → El (A (σ ρ))) i0 (a (σ ρ)))))))
--                               i0
--                               (subst Tm[ VCwF , Δ ] (goal .coerceInv A B a σ) ((VCwF [ b ]Tm) σ) ρ))
--              ≡ transp (λ i → El (B (σ ρ , transp (λ _ → El (A (σ ρ))) (~ i) (a (σ ρ)))))
--                       i0
--                       (transp (λ i → El (B (σ ρ , transp (λ _ → El (A (σ ρ))) i (a (σ ρ))))) i0 (b (σ ρ)))
--         goal = {!!}
--     in goal))) -- {!!})))




-- {-    let foo : (ρ : El Δ) → {!!}
--         foo ρ = {!!}
--     in funExt (λ ρ → ΣPathP (refl , symP (toPathP (fromPathP (
--     let foo : PathP (λ k → El (B (σ ρ , transportRefl (transp (λ _ → El (A (σ ρ))) i0 (a (σ ρ))) k)))
--                     (transp (λ i → El (B (σ ρ , transp (λ _ → El (A (σ ρ))) (~ i) (transp (λ _ → El (A (σ ρ))) i0 (a (σ ρ)))))) i0 (b (σ ρ)))
--                     (b (σ ρ))
--         foo = symP (toPathP refl)

--         prf = (funExt (λ ρ₁ → Σ≡Prop isPropIsIterativeSet (λ i → fst (B (ΣPathP ((λ _ → σ ρ₁) , (λ i₁ → transport (λ _ → El (A (σ ρ₁))) ((transportRefl (transport refl (a (σ ρ₁))) ∙ transportRefl (a (σ ρ₁))) (~ i₁))))  i)))))
--         prf2 = (subst Tm[ VCwF , Δ ] prf (((VCwF [ b ]Tm) σ)) ρ)

--         goal : transport (λ i →  El (B (σ ρ , transp (λ _ → El (A (σ ρ))) i (transport (λ _ → El (A (σ ρ))) (a (σ ρ))))))
--                 (subst (λ p → El (B (ctxExt VCwF .F-hom (σ , (λ _ x → A (σ x))) (ρ , p))))
--                        (transportRefl ((VCwF [ a ]Tm) σ ρ))
--                        prf2)
--              ≡ b (σ ρ)
--         goal = {!!}
--     in toPathP goal) ∙ sym (subst⁻Subst (λ p → El (B (σ ρ , p))) (transportRefl _) (b (σ ρ)))))))
-- -}

-- module Categorical_from_Algebraic {ℓOb ℓHom ℓTy ℓTm : Level}
--                                   (C : Category ℓOb ℓHom)
--                                   (CwFA : Algebraic.CwF C ℓTy ℓTm) where

--    open Category renaming (_⋆_ to _⋆C_)

--    open Algebraic.CwF
--    open Categorical.CwF
--    open Functor

--    goalCwF : Categorical.CwF C ℓTy ℓTm
--    goalCwF .emptyContext = ⟨⟩ CwFA
--    goalCwF .Ty .F-ob Γ .fst = Ty CwFA Γ
--    goalCwF .Ty .F-ob Γ .snd = isSetTy CwFA Γ
--    goalCwF .Ty .F-hom σ A = Algebraic.CwF._[_]Ty CwFA A σ
--    goalCwF .Ty .F-id = funExt (λ A → [id]Ty CwFA A)
--    goalCwF .Ty .F-seq σ' σ = funExt (λ A → [][]Ty CwFA A σ σ')
--    goalCwF .Tm .F-ob (Γ , A) .fst = Tm CwFA Γ A
--    goalCwF .Tm .F-ob (Γ , A) .snd = isSetTm CwFA Γ A
--    goalCwF .Tm .F-hom (σ , p) a = {!!}
--    goalCwF .Tm .F-id = {!!}
--    goalCwF .Tm .F-seq = {!!}
--    goalCwF .ctxExt = {!!}
--    goalCwF .ctxExtIso = {!!}
--    goalCwF .coerceFun = {!!}
--    goalCwF .ctxExtIsoFunNat = {!!}
--    goalCwF .ctxExtIsoFunNatWithoutCoerceFun = {!!}
--    goalCwF .coerceInv = {!!}
--    goalCwF .ctxExtIsoInvNat = {!!}
--    goalCwF .ctxExtIsoInvNatWithoutCoerceInv = {!!}
