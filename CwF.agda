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

-- module V_Algebraic_CwF {ℓ : Level} where

--   open import Cubical.Data.IterativeSets.Base renaming (V⁰ to V ; El⁰ to El ; isSetEl⁰ to isSetEl)
--   open import Cubical.Data.IterativeSets.Sigma
--   open import Cubical.Data.IterativeSets.Pi
--   open import Cubical.Data.IterativeSets.Unit
--   open import Agda.Builtin.Unit

--   open Category

--   VCat : Category (ℓ-suc ℓ) ℓ
--   VCat .ob       = V
--   VCat .Hom[_,_] = λ Δ Γ → El Δ → El Γ
--   VCat .id       = λ x → x
--   VCat ._⋆_      = λ f g x → g (f x)
--   VCat .⋆IdL     = λ _ → refl
--   VCat .⋆IdR     = λ _ → refl
--   VCat .⋆Assoc   = λ _ _ _ → refl
--   VCat .isSetHom {y = y} = isSet→ (isSetEl y)

--   open Algebraic
--   open CwF
--   open Iso

--   VCwF : CwF VCat (ℓ-suc ℓ) ℓ
--   VCwF .⟨⟩                 = unit⁰ , λ _ → (λ _ → lift tt) , λ _ _ _ → lift tt
--   VCwF .Ty Γ               = El Γ → V {ℓ}
--   VCwF .isSetTy Γ          = isSet→ isSetV⁰
--   VCwF ._[_]Ty A σ x       = A (σ x)
--   VCwF .[id]Ty _           = refl
--   VCwF .[][]Ty _ _ _       = refl
--   VCwF .Tm Γ A             = (x : El Γ) → El (A x)
--   VCwF .isSetTm Γ A        = isSetΠ (λ _ → isSetEl _)
--   VCwF ._[_]Tm a σ x       = a (σ x)
--   VCwF .[id]Tm _           = refl
--   VCwF .[][]Tm _ _ _       = refl
--   VCwF ._⋆_                = Σ⁰
--   VCwF .p                  = fst
--   VCwF .q                  = snd
--   VCwF .⟨_,_⟩ σ a x .fst   = σ x
--   VCwF .⟨_,_⟩ σ a x .snd   = a x
--   VCwF .p⟨⟩ σ a            = refl
--   VCwF .coerce σ a         = refl
--   VCwF .q⟨⟩ σ a            = refl
--   VCwF .⟨⟩∘ σ' σ a pa' i x = σ (σ' x) , pa' (~ i) x
--   VCwF .⟨p,q⟩ _            = refl

-- TODO move to different file
-- -- Now we define a more categorical version
open import Cubical.Categories.Presheaf
open import Cubical.Categories.Functor
import Cubical.Categories.Instances.Elements as Els
open Els.Contravariant
-- open import Cubical.Categories.Instances.BinProduct
-- open import Cubical.Categories.Functors.HomFunctor

module Categorical {ℓOb ℓHom : Level} (C : Category ℓOb ℓHom) where

  open Category C hiding (_⋆_)
  open Functor
  open Iso

  Ctx = Category.ob C

  _⟶_ : (Δ Γ : Ctx) → Type ℓHom
  Δ ⟶ Γ = C [ Δ , Γ ]

  infix 20 _⟶_

  private variable
    Θ Δ Γ : Ctx

  -- More categorical definition of CwF
  record CwF (ℓTy ℓTm : Level) :
             Type (ℓ-suc (ℓ-max ℓOb (ℓ-max ℓHom (ℓ-max ℓTy  ℓTm)))) where
    field
      emptyContext : Terminal C

      Ty : Presheaf C ℓTy

      Tm : Presheaf (∫ Ty) ℓTm

      ctxExt : Functor (∫ Ty) C

    -- Some nicer notations
    Ty[_] : (Γ : Ctx) → Type ℓTy
    Ty[ Γ ] = Ty .F-ob Γ .fst

    _[_]Ty : (A : Ty[ Γ ]) (σ : Δ ⟶ Γ) → Ty[ Δ ]
    A [ σ ]Ty = Ty .F-hom σ A

    Tm[_,_] : (Γ : Ctx) (A : Ty[ Γ ]) → Type ℓTm
    Tm[ Γ , A ] = Tm .F-ob (Γ , A) .fst

    _[_]Tm : {A : Ty[ Γ ]} (a : Tm[ Γ , A ]) (σ : Δ ⟶ Γ) → Tm[ Δ , A [ σ ]Ty ]
    a [ σ ]Tm = Tm .F-hom (σ , refl) a

    _⋆_ : (Γ : Ctx) (A : Ty[ Γ ]) → Ctx
    Γ ⋆ A = ctxExt .F-ob (Γ , A)

    infix  40 _[_]Ty
    infix  40 _[_]Tm
    infixl 30 _⋆_

    field
      ctxExtIso : (A : Ty[ Γ ])
                → Iso (Δ ⟶ Γ ⋆ A) (Σ[ σ ∈ Δ ⟶ Γ ] Tm[ Δ , A [ σ ]Ty ])


    -- TODO: what is a good name for this?
    drop : (A : Ty[ Γ ]) (τ : Δ ⟶ Γ ⋆ A) → Δ ⟶ Γ
    drop A τ = ctxExtIso A .fun τ .fst

    field
      -- This is redundant and doesn't seem to make instantiation easier...
      coerceFun : (A : Ty[ Γ ]) (σ : Δ ⟶ Γ ⋆ A) (τ : Θ ⟶ Δ)
                → A [ drop A σ ]Ty [ τ ]Ty ≡ A [ drop A σ ∘ τ ]Ty

      ctxExtIsoFunNat : (A : Ty[ Γ ]) (σ : Δ ⟶ Γ ⋆ A) (τ : Θ ⟶ Δ)
                      → ctxExtIso A .fun (σ ∘ τ)
                      ≡ ( drop A σ ∘ τ
                        , Tm .F-hom (τ , coerceFun A σ τ) (ctxExtIso A .fun σ .snd))

      -- We can also do it this way...
      ctxExtIsoFunNatWithoutCoerceFun :
                         (A : Ty[ Γ ]) (σ : Δ ⟶ Γ ⋆ A) (τ : Θ ⟶ Δ)
                      →  ctxExtIso A .fun (σ ∘ τ)
                      ≡ ( drop A σ ∘ τ
                        , Tm .F-hom (τ , sym (funExt⁻ (Ty .F-seq (drop A σ) τ) A)) (ctxExtIso A .fun σ .snd))

      -- Stating naturality for the inverse is closer to the algebraic version, so we do it as well even though it is redundant...
      coerceInv : (A : Ty[ Γ ]) (σ : Δ ⟶ Γ) (τ : Θ ⟶ Δ)
                → A [ σ ]Ty [ τ ]Ty ≡ A [ σ ∘ τ ]Ty

      ctxExtIsoInvNat : (A : Ty[ Γ ]) (σ : Δ ⟶ Γ) (a : Tm[ Δ , A [ σ ]Ty ]) (τ : Θ ⟶ Δ)
                      → ctxExtIso A .inv (σ , a) ∘ τ
                      ≡ ctxExtIso A .inv (σ ∘ τ , Tm .F-hom (τ , coerceInv A σ τ) a)

      ctxExtIsoInvNatWithoutCoerceInv :
                        (A : Ty[ Γ ]) (σ : Δ ⟶ Γ) (a : Tm[ Δ , A [ σ ]Ty ]) (τ : Θ ⟶ Δ)
                      → ctxExtIso A .inv (σ , a) ∘ τ
                      ≡ ctxExtIso A .inv (σ ∘ τ , Tm .F-hom (τ , sym (funExt⁻ (Ty .F-seq σ τ) A)) a)


  record Σ-Structure-CwF {ℓTy ℓTm : Level} (cwf : CwF ℓTy ℓTm) :
         Type (ℓ-suc (ℓ-max ℓOb (ℓ-max ℓHom (ℓ-max ℓTm ℓTy)))) where

    open CwF cwf

    field
      ΣTy : (A : Ty[ Γ ]) (B : Ty[ Γ ⋆ A ]) → Ty[ Γ ]

      ΣTyNat : (A : Ty[ Γ ]) (B : Ty[ Γ ⋆ A ]) (σ : Δ ⟶ Γ)
             → (ΣTy A B) [ σ ]Ty ≡ ΣTy (A [ σ ]Ty) (B [ ctxExt .F-hom (σ , refl) ]Ty)

      ΣTmIso : (A : Ty[ Γ ]) (B : Ty[ Γ ⋆ A ])
             → Iso (Tm[ Γ , ΣTy A B ])
                   (Σ[ a ∈ Tm[ Γ , A ] ] Tm[ Γ , B [ ctxExtIso A .inv (id , (a [ id ]Tm)) ]Ty ])

      coerceFun : (A : Ty[ Γ ])
                  (B : Ty[ Γ ⋆ A ])
                  (a : Tm[ Γ , ΣTy A B ])
                  (σ : Δ ⟶ Γ)
                → (B [ ctxExtIso A .inv (id , ΣTmIso A B .fun a .fst [ id ]Tm) ]Ty) [ σ ]Ty
                ≡ (B [ ctxExt .F-hom (σ , refl) ]Ty) [ ctxExtIso (A [ σ ]Ty) .inv (id , (ΣTmIso A B .fun a .fst [ σ ]Tm) [ id ]Tm) ]Ty

      ΣTmIsoFunNat : (A : Ty[ Γ ])
                     (B : Ty[ Γ ⋆ A ])
                     (a : Tm[ Γ , ΣTy A B ])
                     (σ : Δ ⟶ Γ)
                   → ( (ΣTmIso A B .fun a .fst) [ σ ]Tm
                     , subst (λ x → Tm[ Δ , x ]) (coerceFun A B a σ) ((ΣTmIso A B .fun a .snd) [ σ ]Tm)  )
                   ≡ ΣTmIso (A [ σ ]Ty) (B [ ctxExt .F-hom (σ , refl) ]Ty) .fun
                            (subst (λ x → Tm[ Δ , x ]) (ΣTyNat A B σ) (a [ σ ]Tm))

      -- The inverse could be nicer? Fording could help even more...

      coerceInv : (A : Ty[ Γ ])
                  (B : Ty[ Γ ⋆ A ])
                  (a : Tm[ Γ , A ])
                  (σ : Δ ⟶ Γ)
                → (B [ inv (ctxExtIso A) (id , a [ id ]Tm) ]Ty) [ σ ]Ty
                ≡ (B [ ctxExt .F-hom (σ , refl) ]Ty) [ inv (ctxExtIso (A [ σ ]Ty)) (id , (a [ σ ]Tm) [ id ]Tm) ]Ty

      ΣTmIsoInvNat : (A : Ty[ Γ ])
                     (B : Ty[ Γ ⋆ A ])
                     (a : Tm[ Γ , A ])
                     (b : Tm[ Γ , B [ ctxExtIso A .inv (id , (a [ id ]Tm)) ]Ty ])
                     (σ : Δ ⟶ Γ)
                   → PathP (λ i → Tm[ Δ , ΣTyNat A B σ i ])
                           (ΣTmIso A B .inv (a , b) [ σ ]Tm)
                           (ΣTmIso (A [ σ ]Ty) (B [ ctxExt .F-hom (σ , refl) ]Ty) .inv
                             (a [ σ ]Tm , subst (λ x → Tm[ Δ , x ]) (coerceInv A B a σ) (b [ σ ]Tm)))


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
