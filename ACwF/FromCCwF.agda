module ACwF.FromCCwF where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
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
  open Functor
  open Iso

  -- Everything lives in this block; the record below is nothing but
  -- `field = lemma`.  That is not just tidiness: a proof may not refer to
  -- `CCwF→ACwF` while defining it, so `wk`/`ext` and the coherences that
  -- mention them have to be defined first.
  --
  -- `Algebraic.CwF` is deliberately opened only *after* the block: with both
  -- presentations in scope, `_▹_`, `p` and `q` are ambiguous overloaded
  -- projections.  Here they are unqualified and always `X`'s.
  private
    variable
      Θ Δ Γ : ob

    -- Presheaf notation: `TyP.⋆IdL` / `TyP.⋆Assoc` *are* the type substitution
    -- laws, and `TmP.⋆IdL` / `TmP.⋆Assoc` are functoriality of Tm over ∫ Ty.
    module ∫Ty = Category (∫ Ty)
    module TyP = PresheafNotation Ty
    module TmP = PresheafNotation Tm

    -- | Context extension as an equivalence.

    ⟨p,q⟩equiv : (A : Ty[ Γ ])
               → Hom[ Δ , Γ ▹ A ] ≃ (Σ[ σ ∈ Hom[ Δ , Γ ] ] Tm[ Δ , A [ σ ]Ty ])
    ⟨p,q⟩equiv A = ⟨p,q⟩ A , ctxExtRepr A

    ⟨p,q⟩inv : (A : Ty[ Γ ])
             → (Σ[ σ ∈ Hom[ Δ , Γ ] ] Tm[ Δ , A [ σ ]Ty ]) → Hom[ Δ , Γ ▹ A ]
    ⟨p,q⟩inv A = invEq (⟨p,q⟩equiv A)

    -- contravariant functoriality of `Ty`, in the direction that undoes the
    -- coercion `⟨p,q⟩` carries
    Ty-∘ : (A : Ty[ Γ ]) (σ : Hom[ Δ , Γ ]) (ρ : Hom[ Θ , Δ ])
         → A [ σ ]Ty [ ρ ]Ty ≡ A [ σ ∘ ρ ]Ty
    Ty-∘ A σ ρ = sym (TyP.⋆Assoc ρ σ A)

    -- weakening
    wk : {A : Ty[ Γ ]} (σ : Hom[ Δ , Γ ]) → Hom[ Δ ▹ A [ σ ]Ty , Γ ▹ A ]
    wk {A = A} σ = ⟨p,q⟩inv A (σ ∘ p , subst (λ T → Tm[ _ , T ]) (Ty-∘ A σ p) q)

    -- section associated to a term
    ext : {A : Ty[ Γ ]} (a : Tm[ Γ , A ]) → Hom[ Γ , Γ ▹ A ]
    ext {A = A} a = ⟨p,q⟩inv A (id , a [ id ]Tm)

    -- | Moving terms along equalities of types.

    -- Ty[ Γ ] is a set, so a dependent path of terms can be reindexed along any
    -- other path with the same endpoints.  This lets each lemma below state
    -- whichever type-level path is most convenient and fix it up at the use site.
    reindex : {A B : Ty[ Γ ]} {e e' : A ≡ B} {x : Tm[ Γ , A ]} {y : Tm[ Γ , B ]}
            → PathP (λ i → Tm[ Γ , e i ]) x y → PathP (λ i → Tm[ Γ , e' i ]) x y
    reindex {e = e} {e' = e'} {x = x} {y = y} =
      subst (λ ε → PathP (λ i → Tm[ _ , ε i ]) x y) (TyP.isSetPsh _ _ e e')

    infixr 30 _∙Tm_
    _∙Tm_ : {A B B' : Ty[ Γ ]} {e : A ≡ B} {e' : B ≡ B'}
            {x : Tm[ Γ , A ]} {y : Tm[ Γ , B ]} {z : Tm[ Γ , B' ]}
          → PathP (λ i → Tm[ Γ , e i ]) x y → PathP (λ i → Tm[ Γ , e' i ]) y z
          → PathP (λ i → Tm[ Γ , (e ∙ e') i ]) x z
    _∙Tm_ {Γ = Γ} = compPathP' {B = λ T → Tm[ Γ , T ]}

    -- Term substitution only depends on the C-part of a ∫ Ty-morphism (the
    -- other component is a path in a set), and is a congruence in the term.
    substTmPathP : {A A' : Ty[ Γ ]} {B B' : Ty[ Δ ]} (eA : A ≡ A') (eB : B ≡ B')
                   (m : ∫ Ty [ (Δ , B) , (Γ , A) ])
                   (m' : ∫ Ty [ (Δ , B') , (Γ , A') ])
                 → m .fst ≡ m' .fst
                 → {a : Tm[ Γ , A ]} {a' : Tm[ Γ , A' ]}
                 → PathP (λ i → Tm[ Γ , eA i ]) a a'
                 → PathP (λ i → Tm[ Δ , eB i ]) (m TmP.⋆ a) (m' TmP.⋆ a')
    substTmPathP eA eB m m' r =
      congP₂ (λ _ n b → n TmP.⋆ b)
             (ElementHomPathP Ty m m' (λ i → _ , eB i) (λ i → _ , eA i) r)

    -- `_[_]Tm` picks the ∫ Ty-morphism with a `refl` witness, whereas
    -- functoriality of `Tm` speaks about the identity of ∫ Ty, whose witness is
    -- the type law.  The two differ only in their source object, so
    -- `substTmPathP` relates them and functoriality finishes the job.  (The
    -- corresponding statement for composition is inlined into `[][]Tm`.)
    Tm-id : {A : Ty[ Γ ]} (a : Tm[ Γ , A ])
          → PathP (λ i → Tm[ Γ , TyP.⋆IdL A i ]) (a [ id ]Tm) a
    Tm-id {A = A} a =
      substTmPathP refl (TyP.⋆IdL A) (id , refl) ∫Ty.id refl (refl {x = a})
      ▷ TmP.⋆IdL a

    -- | The generic variable substituted along an arbitrary τ : Δ ⟶ Γ ▹ A.

    qv[_] : {A : Ty[ Γ ]} (τ : Hom[ Δ , Γ ▹ A ]) → Tm[ Δ , A [ p ∘ τ ]Ty ]
    qv[_] {A = A} τ = (τ , Ty-∘ A p τ) TmP.⋆ q

    -- `⟨p,q⟩` sends τ to (p ∘ τ , qv[ τ ]).  This is *almost* definitional: its
    -- second component is `q [ τ ]Tm` transported along `Ty-∘`, and transporting
    -- along the witness is the same as carrying it in the morphism.
    funIsPQ : (A : Ty[ Γ ]) (τ : Hom[ Δ , Γ ▹ A ]) → ⟨p,q⟩ A τ ≡ (p ∘ τ , qv[ τ ])
    funIsPQ A τ =
      ΣPathP (refl , fromPathP (substTmPathP refl (Ty-∘ A p τ)
                                             (τ , refl) (τ , Ty-∘ A p τ) refl refl))

    -- ... so the morphism classified by (σ , a) is characterised by σ and a.
    invChar : {A : Ty[ Γ ]} (σ : Hom[ Δ , Γ ]) (a : Tm[ Δ , A [ σ ]Ty ])
            → (p ∘ ⟨p,q⟩inv A (σ , a) , qv[ ⟨p,q⟩inv A (σ , a) ]) ≡ (σ , a)
    invChar {A = A} σ a = sym (funIsPQ A _) ∙ secEq (⟨p,q⟩equiv A) (σ , a)

    -- ... and morphisms into Γ ▹ A are determined by p ∘ τ together with qv[ τ ].
    ctxExtη : {A : Ty[ Γ ]} {τ τ' : Hom[ Δ , Γ ▹ A ]} (e : p ∘ τ ≡ p ∘ τ')
            → PathP (λ i → Tm[ Δ , A [ e i ]Ty ]) qv[ τ ] qv[ τ' ]
            → τ ≡ τ'
    ctxExtη {A = A} {τ} {τ'} e h =
      isoFunInjective (equivToIso (⟨p,q⟩equiv A)) τ τ'
        (funIsPQ A τ ∙∙ ΣPathP (e , h) ∙∙ sym (funIsPQ A τ'))

    -- | The projection laws, and their type-level consequences.

    p∘wk : {A : Ty[ Γ ]} (σ : Hom[ Δ , Γ ]) → p {A = A} ∘ wk σ ≡ σ ∘ p
    p∘wk σ = cong fst (invChar (σ ∘ p) _)

    p∘ext : {A : Ty[ Γ ]} (a : Tm[ Γ , A ]) → p ∘ ext a ≡ id
    p∘ext a = cong fst (invChar id _)

    Ty-wk : {A : Ty[ Γ ]} (B : Ty[ Γ ]) (σ : Hom[ Δ , Γ ])
          → B [ p {A = A} ]Ty [ wk σ ]Ty ≡ B [ σ ]Ty [ p ]Ty
    Ty-wk B σ = Ty-∘ B p (wk σ) ∙ TyP.⟨ p∘wk σ ⟩⋆⟨⟩ ∙ TyP.⋆Assoc p σ B

    Ty-ext : {A : Ty[ Γ ]} (B : Ty[ Γ ]) (a : Tm[ Γ , A ]) → B [ p ]Ty [ ext a ]Ty ≡ B
    Ty-ext B a = Ty-∘ B p (ext a) ∙ TyP.⟨ p∘ext a ⟩⋆⟨⟩ ∙ TyP.⋆IdL B

    Ty-comp : {A : Ty[ Γ ]} (τ : Hom[ Δ , Γ ▹ A ]) (ρ : Hom[ Θ , Δ ])
            → A [ p ∘ (τ ∘ ρ) ]Ty ≡ A [ p ∘ τ ]Ty [ ρ ]Ty
    Ty-comp {A = A} τ ρ = TyP.⟨ ⋆Assoc ρ τ p ⟩⋆⟨⟩ ∙ TyP.⋆Assoc ρ (p ∘ τ) A

    -- | Computing the generic variable.

    -- `q [ τ ]Tm` and `qv[ τ ]` differ only in the witness carried by the morphism.
    qv[]≡ : {A : Ty[ Γ ]} (τ : Hom[ Δ , Γ ▹ A ])
          → PathP (λ i → Tm[ Δ , Ty-∘ A p τ i ]) (q [ τ ]Tm) qv[ τ ]
    qv[]≡ {A = A} τ =
      substTmPathP refl (Ty-∘ A p τ) (τ , refl) (τ , Ty-∘ A p τ) refl refl

    qvWk : {A : Ty[ Γ ]} (σ : Hom[ Δ , Γ ])
         → PathP (λ i → Tm[ Δ ▹ A [ σ ]Ty , (TyP.⟨ p∘wk σ ⟩⋆⟨⟩ ∙ TyP.⋆Assoc p σ A) i ])
                 qv[ wk σ ] q
    qvWk {A = A} σ =
      reindex (cong snd (invChar (σ ∘ p) _)
               ∙Tm symP (subst-filler (λ T → Tm[ _ , T ]) (Ty-∘ A σ p) q))

    qvExt : {A : Ty[ Γ ]} (a : Tm[ Γ , A ])
          → PathP (λ i → Tm[ Γ , (TyP.⟨ p∘ext a ⟩⋆⟨⟩ ∙ TyP.⋆IdL A) i ]) qv[ ext a ] a
    qvExt a = reindex (cong snd (invChar id _) ∙Tm Tm-id a)

    qvId : {A : Ty[ Γ ]}
         → PathP (λ i → Tm[ Γ ▹ A , TyP.⟨ ⋆IdL p ⟩⋆⟨⟩ i ]) qv[ id ] (q {A = A})
    qvId {A = A} =
      substTmPathP refl (TyP.⟨ ⋆IdL p ⟩⋆⟨⟩) (id , Ty-∘ A p id) ∫Ty.id refl refl
      ▷ TmP.⋆IdL q

    -- naturality of qv[_]
    qv[]∘ : {A : Ty[ Γ ]} (τ : Hom[ Δ , Γ ▹ A ]) (ρ : Hom[ Θ , Δ ])
          → PathP (λ i → Tm[ Θ , Ty-comp τ ρ i ]) qv[ τ ∘ ρ ] (qv[ τ ] [ ρ ]Tm)
    qv[]∘ {A = A} τ ρ =
      substTmPathP refl (Ty-comp τ ρ) (τ ∘ ρ , Ty-∘ A p (τ ∘ ρ))
                   ((ρ , refl) ∫Ty.⋆ (τ , Ty-∘ A p τ)) refl refl
      ▷ TmP.⋆Assoc (ρ , refl) (τ , Ty-∘ A p τ) q

    -- | The generic variable under weakening and under a section.

    q[wk] : {A : Ty[ Γ ]} (σ : Hom[ Δ , Γ ])
          → PathP (λ i → Tm[ Δ ▹ A [ σ ]Ty , Ty-wk A σ i ]) (q [ wk σ ]Tm) q
    q[wk] σ = reindex (qv[]≡ (wk σ) ∙Tm qvWk σ)

    q[ext] : {A : Ty[ Γ ]} (a : Tm[ Γ , A ])
           → PathP (λ i → Tm[ Γ , Ty-ext A a i ]) (q [ ext a ]Tm) a
    q[ext] a = reindex (qv[]≡ (ext a) ∙Tm qvExt a)

    -- | `ctxExtη` over a path of contexts.

    -- The laws `∘⁺` and `id⁺` compare two morphisms whose *sources* differ by a
    -- path of types, so `ctxExtη` cannot be applied directly.  Path induction on
    -- that path puts both morphisms back in the same hom-set; what survives is
    -- the requirement that each of the two generic variables be *the* generic
    -- variable of its own context, which is exactly what `qvWk` / `qvId` /
    -- `qv[]∘` produce.
    ctxExtηP : {A : Ty[ Γ ]} {B B' : Ty[ Δ ]} (eB : B ≡ B')
               {τ : Hom[ Δ ▹ B , Γ ▹ A ]} {τ' : Hom[ Δ ▹ B' , Γ ▹ A ]}
               (e : PathP (λ i → Hom[ Δ ▹ eB i , Γ ]) (p ∘ τ) (p ∘ τ'))
               {eT : A [ p ∘ τ ]Ty ≡ B [ p ]Ty} {eT' : A [ p ∘ τ' ]Ty ≡ B' [ p ]Ty}
             → PathP (λ i → Tm[ Δ ▹ B , eT i ]) qv[ τ ] q
             → PathP (λ i → Tm[ Δ ▹ B' , eT' i ]) qv[ τ' ] q
             → PathP (λ i → Hom[ Δ ▹ eB i , Γ ▹ A ]) τ τ'
    ctxExtηP {Γ = Γ} {Δ = Δ} {A = A} {B = B} eB {τ = τ} e h =
      J (λ B'' eB'' → {τ'' : Hom[ Δ ▹ B'' , Γ ▹ A ]}
                      (e'' : PathP (λ i → Hom[ Δ ▹ eB'' i , Γ ]) (p ∘ τ) (p ∘ τ''))
                      {eT'' : A [ p ∘ τ'' ]Ty ≡ B'' [ p ]Ty}
                    → PathP (λ i → Tm[ Δ ▹ B'' , eT'' i ]) qv[ τ'' ] q
                    → PathP (λ i → Hom[ Δ ▹ eB'' i , Γ ▹ A ]) τ τ'')
        (λ e'' h'' → ctxExtη e'' (reindex (h ∙Tm symP h'')))
        eB e

    -- | The four coherences relating weakening and sections.

    -- Two morphisms into Γ ▹ A agree as soon as their projections and their
    -- generic variables do (`ctxExtη`); in every case the projections compose
    -- away by `p∘wk`/`p∘ext`, and the generic variables are computed by pushing
    -- `qv[_]` through the composite (`qv[]∘`) and then through each factor
    -- (`qvWk`, `qvExt`, `q[ext]`, `qvId`).
    wkP∘extQ : {A : Ty[ Γ ]} → wk p ∘ ext q ≡ id {x = Γ ▹ A}
    wkP∘extQ =
      ctxExtη ( ⋆Assoc (ext q) (wk p) p
              ∙ ⟨⟩⋆⟨ p∘wk p ⟩
              ∙ sym (⋆Assoc (ext q) p p)
              ∙ ⟨ p∘ext q ⟩⋆⟨⟩)
              (reindex ( qv[]∘ (wk p) (ext q)
                     ∙Tm congP (λ _ x → x [ ext q ]Tm) (qvWk p)
                     ∙Tm q[ext] q
                     ∙Tm symP qvId))

    ext∘ : {A : Ty[ Γ ]} (a : Tm[ Γ , A ]) (σ : Hom[ Δ , Γ ])
         → ext a ∘ σ ≡ wk σ ∘ ext (a [ σ ]Tm)
    ext∘ a σ =
      ctxExtη (prExt ∙ sym prWk)
              (reindex ( qv[]∘ (ext a) σ
                     ∙Tm congP (λ _ x → x [ σ ]Tm) (qvExt a)
                     ∙Tm symP ( qv[]∘ (wk σ) (ext (a [ σ ]Tm))
                            ∙Tm congP (λ _ x → x [ ext (a [ σ ]Tm) ]Tm) (qvWk σ)
                            ∙Tm q[ext] (a [ σ ]Tm))))
      where
        prExt : p ∘ (ext a ∘ σ) ≡ σ
        prExt = ⋆Assoc σ (ext a) p ∙ ⟨⟩⋆⟨ p∘ext a ⟩ ∙ ⋆IdR σ

        prWk : p ∘ (wk σ ∘ ext (a [ σ ]Tm)) ≡ σ
        prWk = ⋆Assoc (ext (a [ σ ]Tm)) (wk σ) p
             ∙ ⟨⟩⋆⟨ p∘wk σ ⟩
             ∙ sym (⋆Assoc (ext (a [ σ ]Tm)) p σ)
             ∙ ⟨ p∘ext (a [ σ ]Tm) ⟩⋆⟨⟩
             ∙ ⋆IdL σ

    -- Same idea one level up: the projections compose away, and each generic
    -- variable is computed in its own (fixed) context.
    ∘wk : {A : Ty[ Γ ]} (σ' : Hom[ Θ , Δ ]) (σ : Hom[ Δ , Γ ])
        → PathP (λ i → Hom[ Θ ▹ TyP.⋆Assoc σ' σ A i , Γ ▹ A ])
                (wk (σ ∘ σ')) (wk σ ∘ wk σ')
    ∘wk {Γ = Γ} {Θ = Θ} {A = A} σ' σ =
      ctxExtηP (TyP.⋆Assoc σ' σ A) prPath
               (qvWk (σ ∘ σ'))
               ( qv[]∘ (wk σ) (wk σ')
             ∙Tm congP (λ _ x → x [ wk σ' ]Tm) (qvWk σ)
             ∙Tm q[wk] σ')
      where
        prPath : PathP (λ i → Hom[ Θ ▹ TyP.⋆Assoc σ' σ A i , Γ ])
                       (p ∘ wk (σ ∘ σ')) (p ∘ (wk σ ∘ wk σ'))
        prPath = (p∘wk (σ ∘ σ') ∙ sym (⋆Assoc p σ' σ))
               ◁ cong (λ B → σ ∘ (σ' ∘ p {A = B})) (TyP.⋆Assoc σ' σ A)
               ▷ sym ( ⋆Assoc (wk σ') (wk σ) p
                     ∙ ⟨⟩⋆⟨ p∘wk σ ⟩
                     ∙ sym (⋆Assoc (wk σ') p σ)
                     ∙ ⟨ p∘wk σ' ⟩⋆⟨⟩)

    idWk : {A : Ty[ Γ ]} → PathP (λ i → Hom[ Γ ▹ TyP.⋆IdL A i , Γ ▹ A ]) (wk id) id
    idWk {Γ = Γ} {A = A} =
      ctxExtηP (TyP.⋆IdL A) prPath (qvWk id) qvId
      where
        prPath : PathP (λ i → Hom[ Γ ▹ TyP.⋆IdL A i , Γ ]) (p ∘ wk id) (p ∘ id)
        prPath = (p∘wk id ∙ ⋆IdR p)
               ◁ cong (λ B → p {A = B}) (TyP.⋆IdL A)
               ▷ sym (⋆IdL p)

  open Algebraic.CwF hiding (_[_]Ty ; _[_]Tm)

  -- the interesting computational part
  CCwF→ACwF : Algebraic.CwF C ℓTy ℓTm
  CCwF→ACwF .⟨⟩ = emptyContext
  CCwF→ACwF .Ty Γ = X .Ty .F-ob Γ .fst
  CCwF→ACwF .Algebraic.CwF._[_]Ty A σ = X .Ty .F-hom σ A
  CCwF→ACwF .Tm Γ A = X .Tm .F-ob (Γ , A) .fst
  CCwF→ACwF .Algebraic.CwF._[_]Tm x σ = X .Tm .F-hom (σ , refl) x
  CCwF→ACwF ._▹_ = X ._▹_
  CCwF→ACwF .p = X .p
  CCwF→ACwF .q = X .q
  CCwF→ACwF .⟨_⟩ = ext
  CCwF→ACwF ._⁺ = wk

  -- now let's prove the laws and coherences
  CCwF→ACwF .isSetTy Γ = X .Ty .F-ob Γ .snd
  CCwF→ACwF .isSetTm Γ A = X .Tm .F-ob (Γ , A) .snd
  CCwF→ACwF .[id]Ty A = funExt⁻ (X .Ty .F-id) A
  CCwF→ACwF .[][]Ty A σ' σ = funExt⁻ (X .Ty .F-seq σ σ') A
  CCwF→ACwF .[id]Tm = Tm-id
  CCwF→ACwF .[][]Tm {A = A} a σ' σ =
    substTmPathP refl (TyP.⋆Assoc σ' σ A) (σ ∘ σ' , refl)
                 ((σ' , refl) ∫Ty.⋆ (σ , refl)) refl (refl {x = a})
    ▷ TmP.⋆Assoc (σ' , refl) (σ , refl) a

  CCwF→ACwF .p∘⁺ = p∘wk
  CCwF→ACwF .p∘⟨⟩≡id = p∘ext
  CCwF→ACwF .[p][⁺]Ty = Ty-wk
  CCwF→ACwF .[p][⟨⟩]Ty = Ty-ext
  CCwF→ACwF .q[⁺]Tm = q[wk]
  CCwF→ACwF .q[⟨⟩]Tm = q[ext]

  CCwF→ACwF .p⁺∘⟨q⟩≡id = wkP∘extQ
  CCwF→ACwF .⟨⟩∘ = ext∘
  CCwF→ACwF .∘⁺ = ∘wk
  CCwF→ACwF .id⁺ = idWk
