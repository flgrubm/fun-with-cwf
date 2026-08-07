{-# OPTIONS --lossy-unification #-}
module ACwF-CCwF where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Presheaf
open import Cubical.Categories.Instances.Elements as Els
open import Cubical.Categories.Instances.Sets
open Els.Contravariant

open import ACwF.Base
open import ACwF.FromCCwF
open import CCwF.Base
open import CCwF.FromACwF

module _ {ℓOb ℓHom : Level} {ℓTy ℓTm : Level} {Ctx : Category ℓOb ℓHom} where

  -- | The round trip `CCwF→ACwF ∘ ACwF→CCwF` now returns the empty context,
  --   types, terms, context extension, projection and generic variable *on the
  --   nose* — `CCwF→ACwF` reads `p` and `q` straight off the CCwF record's
  --   fields rather than recovering them from `ctxExtIso .fun id`.
  --
  --   Only three things move, and only the last two are non-trivial:
  --     * term substitution acquires a `transport refl`, from `_[_]Tm` being
  --       `Tm ⟪ σ , refl ⟫` (discharged by `substRefl` at the use site);
  --     * `RT.⟨ a ⟩` is `invEq (⟨p,q⟩equiv A) (id , a [ id ]Tm)`;
  --     * `RT._⁺ σ` is `invEq (⟨p,q⟩equiv A) (σ ∘ p , coe (q))`.
  --
  --   Both remaining lemmas are therefore the same problem: characterise that
  --   inverse.  `invEq e y ≡ x` follows from `y ≡ equivFun e x` by
  --   `cong (invEq e) ∙ retEq e x`, and `equivFun` is `⟨p,q⟩`, whose two
  --   components are computed by `p∘⟨⟩≡id`/`q[⟨⟩]Tm` and `p∘⁺`/`q[⁺]Tm`.
  private
    module RoundTrip (Cw : Algebraic.CwF Ctx ℓTy ℓTm) where

      open Category Ctx
      open Algebraic.CwF Cw

      module X = Categorical.CwF (ACwF→CCwF Ctx Cw)
      module RT = Algebraic.CwF (CCwF→ACwF Ctx (ACwF→CCwF Ctx Cw))

      -- `ACwF→CCwF Cw`'s context-extension equivalence, spelled in `Cw`'s own
      -- vocabulary: `X.Ty[ Γ ]` *is* `Ty Γ` and `X.Tm[ Δ , T ]` *is* `Tm Δ T`.
      Xeq : {Γ Δ : ob} (A : Ty Γ)
          → Ctx [ Δ , Γ ▹ A ] ≃ (Σ[ σ ∈ Ctx [ Δ , Γ ] ] Tm Δ (A [ σ ]Ty))
      Xeq A = X.⟨p,q⟩ A , X.ctxExtRepr A

      invChar : {Γ Δ : ob} (A : Ty Γ)
                (y : Σ[ σ ∈ Ctx [ Δ , Γ ] ] Tm Δ (A [ σ ]Ty))
                (τ : Ctx [ Δ , Γ ▹ A ])
              → y ≡ X.⟨p,q⟩ A τ → invEq (Xeq A) y ≡ τ
      invChar A y τ h = cong (invEq (Xeq A)) h ∙ retEq (Xeq A) τ

      -- | `RT.⟨ a ⟩` classifies `(id , a [ id ]Tm)`, and `⟨ a ⟩` classifies the
      --   same pair: `p ∘ ⟨ a ⟩ ≡ id` and `q [ ⟨ a ⟩ ]Tm ≡ a`.  The term half
      --   travels `a [ id ]Tm → a → q [ ⟨ a ⟩ ]Tm → …` and then back through
      --   the two coercions `X.⟨p,q⟩` applies.
      extPath : {Γ : ob} {A : Ty Γ} (a : Tm Γ A) → RT.⟨ a ⟩ ≡ ⟨ a ⟩
      extPath {Γ} {A} a =
        invChar A (id , X._[_]Tm a id) ⟨ a ⟩ (ΣPathP (sym (p∘⟨⟩≡id a) , sndP))
        where
          sndP : PathP (λ i → Tm Γ (A [ sym (p∘⟨⟩≡id a) i ]Ty))
                       (X._[_]Tm a id) (X.⟨p,q⟩ A ⟨ a ⟩ .snd)
          sndP = reindex
            ( substRefl {B = Tm Γ} (a [ id ]Tm)
            ◁ ( [id]Tm a
            ∙Tm symP (q[⟨⟩]Tm a)
            ∙Tm ( sym (substRefl {B = Tm Γ} (q [ ⟨ a ⟩ ]Tm))
                ◁ subst-filler (Tm Γ) (sym ([][]Ty A ⟨ a ⟩ p))
                               (subst (Tm Γ) refl (q [ ⟨ a ⟩ ]Tm)))))

      -- | Same shape one level up: `σ ⁺` classifies `(σ ∘ p , q)` too, by
      --   `p∘⁺` and `q[⁺]Tm`.
      wkPath : {Γ Δ : ob} {A : Ty Γ} (σ : Ctx [ Δ , Γ ]) → RT._⁺ {A = A} σ ≡ σ ⁺
      wkPath {Γ} {Δ} {A} σ =
        invChar A (σ ∘ p , t) (σ ⁺) (ΣPathP (sym (p∘⁺ σ) , sndP))
        where
          D : ob
          D = Δ ▹ A [ σ ]Ty

          -- `q` re-typed as a term of `A [ σ ∘ p ]Ty`
          t : Tm D (A [ σ ∘ p ]Ty)
          t = subst (Tm D) (sym ([][]Ty A p σ)) q

          sndP : PathP (λ i → Tm D (A [ sym (p∘⁺ σ) i ]Ty))
                       t (X.⟨p,q⟩ A (σ ⁺) .snd)
          sndP = reindex
            ( symP (subst-filler (Tm D) (sym ([][]Ty A p σ)) q)
            ∙Tm symP (q[⁺]Tm σ)
            ∙Tm ( sym (substRefl {B = Tm D} (q [ σ ⁺ ]Tm))
                ◁ subst-filler (Tm D) (sym ([][]Ty A (σ ⁺) p))
                               (subst (Tm D) refl (q [ σ ⁺ ]Tm))))

  ACwF-Iso-CCwF : Iso (Algebraic.CwF Ctx ℓTy ℓTm) (Categorical.CwF Ctx ℓTy ℓTm)
  ACwF-Iso-CCwF .Iso.fun = ACwF→CCwF Ctx
  ACwF-Iso-CCwF .Iso.inv = CCwF→ACwF Ctx
  ACwF-Iso-CCwF .Iso.sec Cw =
    Categorical.makeCCwFPath Ctx RT Cw
    refl  -- emptyContext≡
    Ty≡
    Tm≡
    refl  -- ▹≡
    refl  -- p≡
    refl  -- q≡
    where
      open Category
      open Functor
      RT : Categorical.CwF Ctx ℓTy ℓTm
      RT = ACwF→CCwF Ctx (CCwF→ACwF Ctx Cw)
      Ty≡ = (Functor≡ (λ c → refl) (λ f → refl))
      Tm≡ : PathP (λ i → Presheaf (∫ (Ty≡ i)) ℓTm)
                  (RT .Categorical.CwF.Tm) (Cw .Categorical.CwF.Tm)
      -- `RT.Tm ⟪ σ , prf ⟫ t` is `subst _ prf (Cw.Tm ⟪ σ , refl ⟫ t)`: the two
      -- ∫-morphisms differ only in their *source*, by `prf`.
      TmHom : {x y : (∫ (Ty≡ i0)) .ob} (f : ((∫ (Ty≡ i0)) ^op) [ x , y ])
            → RT .Categorical.CwF.Tm .F-hom f ≡ Cw .Categorical.CwF.Tm .F-hom f
      TmHom {Γ , A} {Δ , B} (σ , prf) = funExt λ t →
        fromPathP (congP (λ i g → Cw .Categorical.CwF.Tm .F-hom g t)
          (ElementHomPathP (Cw .Categorical.CwF.Ty) (σ , refl) (σ , prf)
                           (λ i → Δ , prf i) refl refl))

      -- the proof looks like that of Functor≡, but its a PathP
      Tm≡ i .F-ob x = Cw .Categorical.CwF.Tm .F-ob x
      Tm≡ i .F-hom f = TmHom f i
      Tm≡ i .F-id {x} =
        isProp→PathP
          (λ j → (SET ℓTm) .isSetHom
                   (Tm≡ j .F-hom (((∫ (Ty≡ j)) ^op) .id {x}))
                   ((SET ℓTm) .id))
          (RT .Categorical.CwF.Tm .F-id) (Cw .Categorical.CwF.Tm .F-id) i
      Tm≡ i .F-seq f g =
        isProp→PathP
          (λ j → (SET ℓTm) .isSetHom
                   (Tm≡ j .F-hom (((∫ (Ty≡ j)) ^op) ._⋆_ f g))
                   (λ t → Tm≡ j .F-hom g (Tm≡ j .F-hom f t)))
          (RT .Categorical.CwF.Tm .F-seq f g)
          (Cw .Categorical.CwF.Tm .F-seq f g) i
  ACwF-Iso-CCwF .Iso.ret Cw =
    Algebraic.makeACwFPath Ctx (CCwF→ACwF Ctx (ACwF→CCwF Ctx Cw)) Cw
    refl  -- ⟨⟩≡
    refl  -- Ty≡
    refl  -- []Ty≡
    refl  -- Tm≡
    -- []Tm≡: the only transport the round trip introduces
    (λ i x σ → substRefl {B = λ z → z} (Cw .Algebraic.CwF._[_]Tm x σ) i)
    refl  -- ▹≡
    refl  -- p≡
    refl  -- q≡
    (λ i {Γ} {Δ} {A} σ → RoundTrip.wkPath Cw {Γ} {Δ} {A} σ i)  -- ⁺≡
    (λ i {Γ} {A} a → RoundTrip.extPath Cw {Γ} {A} a i)         -- ⟨⟩'≡

  ACwF≃CCwF : Algebraic.CwF Ctx ℓTy ℓTm ≃ Categorical.CwF Ctx ℓTy ℓTm
  ACwF≃CCwF = isoToEquiv ACwF-Iso-CCwF
