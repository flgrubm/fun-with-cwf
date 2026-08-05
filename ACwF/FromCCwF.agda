module ACwF.FromCCwF where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Transport

open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Limits.Terminal

open import Cubical.Categories.Presheaf
open import Cubical.Categories.Functor
import Cubical.Categories.Instances.Elements as Els
open Els.Contravariant

open import ACwF.Base
open import CCwF.Base

module _ {ℓOb ℓHom ℓTy ℓTm : Level} (C : Category ℓOb ℓHom) (X : Categorical.CwF C ℓTy ℓTm) where

  open Category C hiding (_⋆_)

  open Categorical.CwF X
  -- `reindex` / `_∙Tm_` are re-derived below for the *CCwF* `X`: the ACwF
  -- versions live on `CCwF→ACwF`, which is exactly what we are defining.
  open Algebraic.CwF hiding (_[_]Ty ; _[_]Tm ; reindex ; _∙Tm_ ; coeP)
  open Functor
  open Iso

  -- first, a lot of lemmas
  private
    variable
      Θ Δ Γ : ob

    -- Presheaf notation: `TyP.⋆IdL` / `TyP.⋆Assoc` *are* the type substitution
    -- laws, and `TmP.⋆IdL` / `TmP.⋆Assoc` are functoriality of Tm over ∫ Ty.
    module ∫Ty = Category (∫ (X .Ty))
    module TyP = PresheafNotation (X .Ty)
    module TmP = PresheafNotation (X .Tm)

    -- | The structure, defined outside of the record so that the proofs below
    --   may refer to it without upsetting the termination checker.

    -- projection
    pr : {A : Ty[ Γ ]} → Hom[ Γ ⋆ A , Γ ]
    pr {A = A} = ctxExtIso A .fun id .fst

    -- generic variable
    qv : {A : Ty[ Γ ]} → Tm[ Γ ⋆ A , A [ pr ]Ty ]
    qv {A = A} = ctxExtIso A .fun id .snd

    -- transporting a term along an equality of types
    coeTm : {A B : Ty[ Γ ]} → A ≡ B → Tm[ Γ , A ] → Tm[ Γ , B ]
    coeTm e = subst (λ T → Tm[ _ , T ]) e

    -- weakening
    wk : {A : Ty[ Γ ]} (σ : Hom[ Δ , Γ ]) → Hom[ Δ ⋆ A [ σ ]Ty , Γ ⋆ A ]
    wk {A = A} σ = ctxExtIso A .inv (σ ∘ pr , coeTm (coerceInv A σ pr) qv)

    -- section associated to a term
    ext : {A : Ty[ Γ ]} (a : Tm[ Γ , A ]) → Hom[ Γ , Γ ⋆ A ]
    ext {A = A} a = ctxExtIso A .inv (id , coeTm (sym (TyP.⋆IdL A)) a)

    -- | Moving terms along equalities of types.

    -- Ty[ Γ ] is a set, so a dependent path of terms can be reindexed along any
    -- other path with the same endpoints.  This lets each lemma below state
    -- whichever type-level path is most convenient and fix it up at the use site.
    reindex : {A B : Ty[ Γ ]} {e e' : A ≡ B} {x : Tm[ Γ , A ]} {y : Tm[ Γ , B ]}
            → PathP (λ i → Tm[ Γ , e i ]) x y → PathP (λ i → Tm[ Γ , e' i ]) x y
    reindex {Γ = Γ} {e = e} {e' = e'} {x = x} {y = y} =
      subst (λ ε → PathP (λ i → Tm[ Γ , ε i ]) x y) (X .Ty .F-ob Γ .snd _ _ e e')

    infixr 30 _∙Tm_
    _∙Tm_ : {A B B' : Ty[ Γ ]} {e : A ≡ B} {e' : B ≡ B'}
            {x : Tm[ Γ , A ]} {y : Tm[ Γ , B ]} {z : Tm[ Γ , B' ]}
          → PathP (λ i → Tm[ Γ , e i ]) x y → PathP (λ i → Tm[ Γ , e' i ]) y z
          → PathP (λ i → Tm[ Γ , (e ∙ e') i ]) x z
    _∙Tm_ {Γ = Γ} = compPathP' {B = λ T → Tm[ Γ , T ]}

    -- Term substitution only depends on the C-part of a ∫ Ty-morphism (the
    -- other component is a path in a set), and is a congruence in the term.
    substTmPathP : {A A' : Ty[ Γ ]} {B B' : Ty[ Δ ]} (eA : A ≡ A') (eB : B ≡ B')
                   (m : ∫ (X .Ty) [ (Δ , B) , (Γ , A) ])
                   (m' : ∫ (X .Ty) [ (Δ , B') , (Γ , A') ])
                 → m .fst ≡ m' .fst
                 → {a : Tm[ Γ , A ]} {a' : Tm[ Γ , A' ]}
                 → PathP (λ i → Tm[ Γ , eA i ]) a a'
                 → PathP (λ i → Tm[ Δ , eB i ]) (m TmP.⋆ a) (m' TmP.⋆ a')
    substTmPathP eA eB m m' r =
      congP₂ (λ _ n b → n TmP.⋆ b)
             (ElementHomPathP (X .Ty) m m' (λ i → _ , eB i) (λ i → _ , eA i) r)

    -- | The generic variable substituted along an arbitrary τ : Δ ⟶ Γ ⋆ A.

    qv[_] : {A : Ty[ Γ ]} (τ : Hom[ Δ , Γ ⋆ A ]) → Tm[ Δ , A [ pr ∘ τ ]Ty ]
    qv[_] {A = A} τ = (τ , coerceFun A id τ) TmP.⋆ qv

    -- `fun` is completely determined: it sends τ to (pr ∘ τ , qv[ τ ]).
    funIsPrQv : (A : Ty[ Γ ]) (τ : Hom[ Δ , Γ ⋆ A ])
              → ctxExtIso A .fun τ ≡ (pr ∘ τ , qv[ τ ])
    funIsPrQv A τ = cong (ctxExtIso A .fun) (sym (⋆IdR τ)) ∙ ctxExtIsoFunNat A id τ

    -- ... so the morphism classified by (σ , a) is characterised by σ and a.
    invChar : {A : Ty[ Γ ]} (σ : Hom[ Δ , Γ ]) (a : Tm[ Δ , A [ σ ]Ty ])
            → (pr ∘ ctxExtIso A .inv (σ , a) , qv[ ctxExtIso A .inv (σ , a) ]) ≡ (σ , a)
    invChar {A = A} σ a = sym (funIsPrQv A _) ∙ ctxExtIso A .sec (σ , a)

    -- ... and morphisms into Γ ⋆ A are determined by pr ∘ τ together with qv[ τ ].
    ctxExtη : {A : Ty[ Γ ]} {τ τ' : Hom[ Δ , Γ ⋆ A ]} (e : pr ∘ τ ≡ pr ∘ τ')
            → PathP (λ i → Tm[ Δ , A [ e i ]Ty ]) qv[ τ ] qv[ τ' ]
            → τ ≡ τ'
    ctxExtη {A = A} {τ} {τ'} e h =
      isoFunInjective (ctxExtIso A) τ τ'
        (funIsPrQv A τ ∙∙ ΣPathP (e , h) ∙∙ sym (funIsPrQv A τ'))

    -- | The projection laws, and their type-level consequences.

    pr∘wk : {A : Ty[ Γ ]} (σ : Hom[ Δ , Γ ]) → pr {A = A} ∘ wk σ ≡ σ ∘ pr
    pr∘wk σ = cong fst (invChar (σ ∘ pr) _)

    pr∘ext : {A : Ty[ Γ ]} (a : Tm[ Γ , A ]) → pr ∘ ext a ≡ id
    pr∘ext a = cong fst (invChar id _)

    Ty-wk : {A : Ty[ Γ ]} (B : Ty[ Γ ]) (σ : Hom[ Δ , Γ ])
          → B [ pr {A = A} ]Ty [ wk σ ]Ty ≡ B [ σ ]Ty [ pr ]Ty
    Ty-wk B σ = sym (TyP.⋆Assoc (wk σ) pr B) ∙ TyP.⟨ pr∘wk σ ⟩⋆⟨⟩ ∙ TyP.⋆Assoc pr σ B

    Ty-ext : {A : Ty[ Γ ]} (B : Ty[ Γ ]) (a : Tm[ Γ , A ]) → B [ pr ]Ty [ ext a ]Ty ≡ B
    Ty-ext B a = sym (TyP.⋆Assoc (ext a) pr B) ∙ TyP.⟨ pr∘ext a ⟩⋆⟨⟩ ∙ TyP.⋆IdL B

    Ty-∘ : {A : Ty[ Γ ]} (τ : Hom[ Δ , Γ ⋆ A ]) (ρ : Hom[ Θ , Δ ])
         → A [ pr ∘ (τ ∘ ρ) ]Ty ≡ A [ pr ∘ τ ]Ty [ ρ ]Ty
    Ty-∘ {A = A} τ ρ = TyP.⟨ ⋆Assoc ρ τ pr ⟩⋆⟨⟩ ∙ TyP.⋆Assoc ρ (pr ∘ τ) A

    -- | Computing the generic variable.

    -- `q [ τ ]Tm` and `qv[ τ ]` differ only in the witness carried by the morphism.
    qv[]≡ : {A : Ty[ Γ ]} (τ : Hom[ Δ , Γ ⋆ A ])
          → PathP (λ i → Tm[ Δ , sym (TyP.⋆Assoc τ pr A) i ]) (qv [ τ ]Tm) qv[ τ ]
    qv[]≡ {A = A} τ =
      substTmPathP refl (sym (TyP.⋆Assoc τ pr A)) (τ , refl) (τ , coerceFun A id τ) refl refl

    qvWk : {A : Ty[ Γ ]} (σ : Hom[ Δ , Γ ])
         → PathP (λ i → Tm[ Δ ⋆ A [ σ ]Ty , (TyP.⟨ pr∘wk σ ⟩⋆⟨⟩ ∙ TyP.⋆Assoc pr σ A) i ])
                 qv[ wk σ ] qv
    qvWk {A = A} σ = reindex (cong snd (invChar (σ ∘ pr) _)
                     ∙Tm symP (subst-filler (λ T → Tm[ _ , T ]) (coerceInv A σ pr) qv))

    qvExt : {A : Ty[ Γ ]} (a : Tm[ Γ , A ])
          → PathP (λ i → Tm[ Γ , (TyP.⟨ pr∘ext a ⟩⋆⟨⟩ ∙ TyP.⋆IdL A) i ]) qv[ ext a ] a
    qvExt {A = A} a = reindex (cong snd (invChar id _)
                      ∙Tm symP (subst-filler (λ T → Tm[ _ , T ]) (sym (TyP.⋆IdL A)) a))

    qvId : {A : Ty[ Γ ]}
         → PathP (λ i → Tm[ Γ ⋆ A , TyP.⟨ ⋆IdL pr ⟩⋆⟨⟩ i ]) qv[ id ] (qv {A = A})
    qvId {A = A} =
      substTmPathP refl (TyP.⟨ ⋆IdL pr ⟩⋆⟨⟩) (id , coerceFun A id id) ∫Ty.id refl refl
      ▷ TmP.⋆IdL qv

    -- naturality of qv[_]
    qv[]∘ : {A : Ty[ Γ ]} (τ : Hom[ Δ , Γ ⋆ A ]) (ρ : Hom[ Θ , Δ ])
          → PathP (λ i → Tm[ Θ , Ty-∘ τ ρ i ]) qv[ τ ∘ ρ ] (qv[ τ ] [ ρ ]Tm)
    qv[]∘ {A = A} τ ρ =
      substTmPathP refl (Ty-∘ τ ρ) (τ ∘ ρ , coerceFun A id (τ ∘ ρ))
                   ((ρ , refl) ∫Ty.⋆ (τ , coerceFun A id τ)) refl refl
      ▷ TmP.⋆Assoc (ρ , refl) (τ , coerceFun A id τ) qv

    -- | The generic variable under weakening and under a section.

    q[wk] : {A : Ty[ Γ ]} (σ : Hom[ Δ , Γ ])
          → PathP (λ i → Tm[ Δ ⋆ A [ σ ]Ty , Ty-wk A σ i ]) (qv [ wk σ ]Tm) qv
    q[wk] σ = reindex (qv[]≡ (wk σ) ∙Tm qvWk σ)

    q[ext] : {A : Ty[ Γ ]} (a : Tm[ Γ , A ])
           → PathP (λ i → Tm[ Γ , Ty-ext A a i ]) (qv [ ext a ]Tm) a
    q[ext] a = reindex (qv[]≡ (ext a) ∙Tm qvExt a)

    -- | `ctxExtη` over a path of contexts.

    -- The laws `∘⁺` and `id⁺` compare two morphisms whose *sources* differ by a
    -- path of types, so `ctxExtη` cannot be applied directly.  Path induction on
    -- that path puts both morphisms back in the same hom-set; what survives is
    -- the requirement that each of the two generic variables be *the* generic
    -- variable of its own context, which is exactly what `qvWk` / `qvId` /
    -- `qv[]∘` produce.
    ctxExtηP : {A : Ty[ Γ ]} {B B' : Ty[ Δ ]} (eB : B ≡ B')
               {τ : Hom[ Δ ⋆ B , Γ ⋆ A ]} {τ' : Hom[ Δ ⋆ B' , Γ ⋆ A ]}
               (e : PathP (λ i → Hom[ Δ ⋆ eB i , Γ ]) (pr ∘ τ) (pr ∘ τ'))
               {eT : A [ pr ∘ τ ]Ty ≡ B [ pr ]Ty} {eT' : A [ pr ∘ τ' ]Ty ≡ B' [ pr ]Ty}
             → PathP (λ i → Tm[ Δ ⋆ B , eT i ]) qv[ τ ] qv
             → PathP (λ i → Tm[ Δ ⋆ B' , eT' i ]) qv[ τ' ] qv
             → PathP (λ i → Hom[ Δ ⋆ eB i , Γ ⋆ A ]) τ τ'
    ctxExtηP {Γ = Γ} {Δ = Δ} {A = A} {B = B} eB {τ = τ} e h =
      J (λ B'' eB'' → {τ'' : Hom[ Δ ⋆ B'' , Γ ⋆ A ]}
                      (e'' : PathP (λ i → Hom[ Δ ⋆ eB'' i , Γ ]) (pr ∘ τ) (pr ∘ τ''))
                      {eT'' : A [ pr ∘ τ'' ]Ty ≡ B'' [ pr ]Ty}
                    → PathP (λ i → Tm[ Δ ⋆ B'' , eT'' i ]) qv[ τ'' ] qv
                    → PathP (λ i → Hom[ Δ ⋆ eB'' i , Γ ⋆ A ]) τ τ'')
        (λ e'' h'' → ctxExtη e'' (reindex (h ∙Tm symP h'')))
        eB e

  -- the interesting computational part
  CCwF→ACwF : Algebraic.CwF C ℓTy ℓTm
  CCwF→ACwF .⟨⟩ = emptyContext
  CCwF→ACwF .Ty Γ = X .Ty .F-ob Γ .fst
  CCwF→ACwF .Algebraic.CwF._[_]Ty A σ = X .Ty .F-hom σ A
  CCwF→ACwF .Tm Γ A = X .Tm .F-ob (Γ , A) .fst
  CCwF→ACwF .Algebraic.CwF._[_]Tm x σ = X .Tm .F-hom (σ , refl) x
  CCwF→ACwF ._▹_ Γ A = ctxExt .F-ob (Γ , A)
  CCwF→ACwF .p = pr
  CCwF→ACwF .q = qv
  CCwF→ACwF .⟨_⟩ = ext
  CCwF→ACwF ._⁺ = wk

  -- now let's prove the laws and coherences
  CCwF→ACwF .isSetTy Γ = X .Ty .F-ob Γ .snd
  CCwF→ACwF .isSetTm Γ A = X .Tm .F-ob (Γ , A) .snd
  CCwF→ACwF .[id]Ty = TyP.⋆IdL
  CCwF→ACwF .[][]Ty A σ' σ = TyP.⋆Assoc σ' σ A

  -- Both term-substitution laws say the same thing: `_[_]Tm` picks the
  -- morphism of ∫ Ty with a `refl` witness, whereas functoriality of Tm speaks
  -- about the identity / composite of ∫ Ty, whose witnesses are the type laws.
  -- The two morphisms only differ in their source object, so `substTmPathP`
  -- relates them and functoriality finishes the job.
  CCwF→ACwF .[id]Tm {A = A} a =
    substTmPathP refl (TyP.⋆IdL A) (id , refl) ∫Ty.id refl (refl {x = a})
    ▷ TmP.⋆IdL a
  CCwF→ACwF .[][]Tm {A = A} a σ' σ =
    substTmPathP refl (TyP.⋆Assoc σ' σ A) (σ ∘ σ' , refl)
                 ((σ' , refl) ∫Ty.⋆ (σ , refl)) refl (refl {x = a})
    ▷ TmP.⋆Assoc (σ' , refl) (σ , refl) a

  CCwF→ACwF .p∘⁺ = pr∘wk
  CCwF→ACwF .p∘⟨⟩≡id = pr∘ext
  CCwF→ACwF .[p][⁺]Ty = Ty-wk
  CCwF→ACwF .[p][⟨⟩]Ty = Ty-ext
  CCwF→ACwF .q[⁺]Tm = q[wk]
  CCwF→ACwF .q[⟨⟩]Tm = q[ext]

  -- Two morphisms into Γ ⋆ A agree as soon as their projections and their
  -- generic variables do (`ctxExtη`); in both cases the projections compose
  -- away by `pr∘wk`/`pr∘ext`, and the generic variables are computed by
  -- pushing `qv[_]` through the composite (`qv[]∘`) and then through each
  -- factor (`qvWk`, `qvExt`, `q[ext]`, `qvId`).
  CCwF→ACwF .p⁺∘⟨q⟩≡id =
    ctxExtη ( ⋆Assoc (ext qv) (wk pr) pr
            ∙ ⟨⟩⋆⟨ pr∘wk pr ⟩
            ∙ sym (⋆Assoc (ext qv) pr pr)
            ∙ ⟨ pr∘ext qv ⟩⋆⟨⟩)
            (reindex ( qv[]∘ (wk pr) (ext qv)
                   ∙Tm congP (λ _ x → x [ ext qv ]Tm) (qvWk pr)
                   ∙Tm q[ext] qv
                   ∙Tm symP qvId))

  CCwF→ACwF .⟨⟩∘ a σ =
    ctxExtη (prExt ∙ sym prWk)
            (reindex ( qv[]∘ (ext a) σ
                   ∙Tm congP (λ _ x → x [ σ ]Tm) (qvExt a)
                   ∙Tm symP ( qv[]∘ (wk σ) (ext (a [ σ ]Tm))
                          ∙Tm congP (λ _ x → x [ ext (a [ σ ]Tm) ]Tm) (qvWk σ)
                          ∙Tm q[ext] (a [ σ ]Tm))))
    where
      prExt : pr ∘ (ext a ∘ σ) ≡ σ
      prExt = ⋆Assoc σ (ext a) pr ∙ ⟨⟩⋆⟨ pr∘ext a ⟩ ∙ ⋆IdR σ

      prWk : pr ∘ (wk σ ∘ ext (a [ σ ]Tm)) ≡ σ
      prWk = ⋆Assoc (ext (a [ σ ]Tm)) (wk σ) pr
           ∙ ⟨⟩⋆⟨ pr∘wk σ ⟩
           ∙ sym (⋆Assoc (ext (a [ σ ]Tm)) pr σ)
           ∙ ⟨ pr∘ext (a [ σ ]Tm) ⟩⋆⟨⟩
           ∙ ⋆IdL σ

  -- Same idea one level up: the projections compose away, and each generic
  -- variable is computed in its own (fixed) context.
  CCwF→ACwF .∘⁺ {A = A} σ' σ =
    ctxExtηP (TyP.⋆Assoc σ' σ A) prPath
             (qvWk (σ ∘ σ'))
             ( qv[]∘ (wk σ) (wk σ')
           ∙Tm congP (λ _ x → x [ wk σ' ]Tm) (qvWk σ)
           ∙Tm q[wk] σ')
    where
      prPath : PathP (λ i → Hom[ _ ⋆ TyP.⋆Assoc σ' σ A i , _ ])
                     (pr ∘ wk (σ ∘ σ')) (pr ∘ (wk σ ∘ wk σ'))
      prPath = (pr∘wk (σ ∘ σ') ∙ sym (⋆Assoc pr σ' σ))
             ◁ cong (λ B → σ ∘ (σ' ∘ pr {A = B})) (TyP.⋆Assoc σ' σ A)
             ▷ sym ( ⋆Assoc (wk σ') (wk σ) pr
                   ∙ ⟨⟩⋆⟨ pr∘wk σ ⟩
                   ∙ sym (⋆Assoc (wk σ') pr σ)
                   ∙ ⟨ pr∘wk σ' ⟩⋆⟨⟩)

  CCwF→ACwF .id⁺ {A = A} =
    ctxExtηP (TyP.⋆IdL A) prPath (qvWk id) qvId
    where
      prPath : PathP (λ i → Hom[ _ ⋆ TyP.⋆IdL A i , _ ]) (pr ∘ wk id) (pr ∘ id)
      prPath = (pr∘wk id ∙ ⋆IdR pr)
             ◁ cong (λ B → pr {A = B}) (TyP.⋆IdL A)
             ▷ sym (⋆IdL pr)
