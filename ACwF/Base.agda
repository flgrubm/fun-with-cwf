module ACwF.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Isomorphism

open import Cubical.Functions.FunExtEquiv

open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Limits.Terminal

module Algebraic {ℓOb ℓHom : Level} (C : Category ℓOb ℓHom) where

  open Category C hiding (_⋆_)

  Ctx = Category.ob C

  -- potentially rename
  _⟶_ : (Δ Γ : Ctx) → Type ℓHom
  Δ ⟶ Γ = C [ Δ , Γ ]

  infix 20 _⟶_

  private variable
    Θ Δ Γ : Ctx

  -- Unfolded definition of CwF à la Pitts
  record CwF (ℓTy ℓTm : Level) :
             Type (ℓ-suc (ℓ-max ℓOb (ℓ-max ℓHom (ℓ-max ℓTy  ℓTm)))) where
    field
      -- Empty context
      ⟨⟩ : Terminal C

      -- | Types

      Ty : (Γ : Ctx) → Type ℓTy

      isSetTy : (Γ : Ctx) → isSet (Ty Γ)

      _[_]Ty : (A : Ty Γ) (σ : Δ ⟶ Γ)
             → ----------------------
               Ty Δ

      [id]Ty : (A : Ty Γ)
             → ----------------
               A [ id ]Ty ≡ A

      [][]Ty : (A : Ty Γ) (σ' : Θ ⟶ Δ) (σ : Δ ⟶ Γ)
             → -------------------------------------------
               A [ σ ∘ σ' ]Ty ≡ (A [ σ ]Ty ) [ σ' ]Ty

      -- | Terms

      Tm : (Γ : Ctx) (A : Ty Γ) → Type ℓTm

      isSetTm : (Γ : Ctx) (A : Ty Γ) → isSet (Tm Γ A)

      _[_]Tm : {A : Ty Γ} (a : Tm Γ A) (σ : Δ ⟶ Γ)
             → -----------------------------------
               Tm Δ (A [ σ ]Ty)

      [id]Tm : {A : Ty Γ} (a : Tm Γ A)
             → ------------------------------------------------
               PathP (λ i → Tm Γ ([id]Ty A i)) (a [ id ]Tm) a

      [][]Tm : {A : Ty Γ} (a : Tm Γ A) (σ' : Θ ⟶ Δ) (σ : Δ ⟶ Γ)
             → ------------------------------------------------
                PathP (λ i → Tm Θ ([][]Ty A σ' σ i))
                      (a [ σ ∘ σ' ]Tm)
                      (a [ σ ]Tm [ σ' ]Tm)

      -- | Context extension

      _▹_ : (Γ : Ctx) (A : Ty Γ) → Ctx

      p : {A : Ty Γ} → Γ ▹ A ⟶ Γ

      q : {A : Ty Γ} → Tm (Γ ▹ A) (A [ p ]Ty)

    infix  40 _[_]Ty
    infix  40 _[_]Tm
    infixl 30 _▹_

    field
      _⁺ : {A : Ty Γ} (σ : Δ ⟶ Γ)
         → ----------------------
           Δ ▹ A [ σ ]Ty ⟶ Γ ▹ A

      ⟨_⟩ : {A : Ty Γ} (a : Tm Γ A)
          → -----------------------
            Γ ⟶ (Γ ▹ A)

      ⟨⟩∘ : {A : Ty Γ} (a : Tm Γ A) (σ : Δ ⟶ Γ)
          → -----------------------------------
            ⟨ a ⟩ ∘ σ ≡ σ ⁺ ∘ ⟨ a [ σ ]Tm ⟩

      p⁺∘⟨q⟩≡id : {A : Ty Γ}
                → ------------------------
                  p ⁺ ∘ ⟨ q ⟩ ≡ id {Γ ▹ A}

      ∘⁺ : {A : Ty Γ} (σ' : Θ ⟶ Δ) (σ : Δ ⟶ Γ)
         → -------------------------------------------------------------------
           PathP (λ i → Θ ▹ [][]Ty A σ' σ i ⟶ Γ ▹ A) ((σ ∘ σ') ⁺) (σ ⁺ ∘ σ' ⁺)

      id⁺ : {A : Ty Γ}
          → ----------------------------------------------
            PathP (λ i → Γ ▹ [id]Ty A i ⟶ Γ ▹ A) (id ⁺) id

      p∘⁺ : {A : Ty Γ} (σ : Δ ⟶ Γ)
          → -----------------------
            p {A = A} ∘ σ ⁺ ≡ σ ∘ p

      [p][⁺]Ty : {A : Ty Γ} (B : Ty Γ) (σ : Δ ⟶ Γ)
               → -----------------------------------------------
                 B [ p {A = A} ]Ty [ σ ⁺ ]Ty ≡ B [ σ ]Ty [ p ]Ty

      q[⁺]Tm : {A : Ty Γ} (σ : Δ ⟶ Γ)
             → -----------------------------------------------------------------
               PathP (λ i → Tm (Δ ▹ A [ σ ]Ty) ([p][⁺]Ty A σ i)) (q [ σ ⁺ ]Tm) q

      p∘⟨⟩≡id : {A : Ty Γ} (a : Tm Γ A)
              → -----------------------
                p ∘ ⟨ a ⟩ ≡ id

      [p][⟨⟩]Ty : {A : Ty Γ} (B : Ty Γ) (a : Tm Γ A)
                → ----------------------------------
                  B [ p ]Ty [ ⟨ a ⟩ ]Ty ≡ B

      q[⟨⟩]Tm : {A : Ty Γ} (a : Tm Γ A)
              → ------------------------------------------------------
                PathP (λ i → Tm Γ ([p][⟨⟩]Ty A a i)) (q [ ⟨ a ⟩ ]Tm) a

    -- | Moving terms along equalities of types.

    -- `Ty Γ` is a set, so a dependent path of terms may be reindexed along *any*
    -- other type-path with the same endpoints.  This lets a lemma be stated with
    -- whichever path is convenient to build and fixed up at the use site.
    reindex : {A B : Ty Γ} {e e' : A ≡ B} {x : Tm Γ A} {y : Tm Γ B}
            → PathP (λ i → Tm Γ (e i)) x y → PathP (λ i → Tm Γ (e' i)) x y
    reindex {Γ = Γ} {e = e} {e' = e'} {x = x} {y = y} =
      subst (λ ε → PathP (λ i → Tm Γ (ε i)) x y) (isSetTy Γ _ _ e e')

    -- Composition of dependent paths of terms.  `compPathP'` cannot infer its
    -- `B`, so pin it here once and for all.
    infixr 30 _∙Tm_
    _∙Tm_ : {A B B' : Ty Γ} {e : A ≡ B} {e' : B ≡ B'}
            {x : Tm Γ A} {y : Tm Γ B} {z : Tm Γ B'}
          → PathP (λ i → Tm Γ (e i)) x y → PathP (λ i → Tm Γ (e' i)) y z
          → PathP (λ i → Tm Γ ((e ∙ e') i)) x z
    _∙Tm_ {Γ = Γ} = compPathP' {B = Tm Γ}

    -- Transporting a term backwards along a type-path, read as a dependent path.
    coeP : {A B : Ty Γ} (e : A ≡ B) (x : Tm Γ B)
         → PathP (λ i → Tm Γ (e i)) (subst⁻ (Tm Γ) e x) x
    coeP {Γ = Γ} e x = symP (subst-filler (Tm Γ) (sym e) x)

  open CwF

  -- | Two CwFs on the same base category are equal as soon as their
  -- *computational* parts agree: the empty context, types and terms with their
  -- substitution, context extension with its projection, generic variable,
  -- weakening and sections.  Everything else — the h-level fields and all the
  -- laws and coherences — is a proposition (equations in the sets `Ty`, `Tm`
  -- and `C [_,_]`), hence transported for free by `isProp→PathP`.
  module _ {ℓTy ℓTm : Level} (Cw Cw' : CwF ℓTy ℓTm)
    (⟨⟩≡ : Cw .⟨⟩ .fst ≡ Cw' .⟨⟩ .fst)
    (Ty≡ : Cw .Ty ≡ Cw' .Ty)
    ([]Ty≡ : PathP (λ i → {Γ Δ : Ctx} → Ty≡ i Γ → Δ ⟶ Γ → Ty≡ i Δ)
                   (Cw ._[_]Ty) (Cw' ._[_]Ty))
    (Tm≡ : PathP (λ i → (Γ : Ctx) → Ty≡ i Γ → Type ℓTm) (Cw .Tm) (Cw' .Tm))
    ([]Tm≡ : PathP (λ i → {Γ Δ : Ctx} {A : Ty≡ i Γ}
                        → Tm≡ i Γ A → (σ : Δ ⟶ Γ) → Tm≡ i Δ ([]Ty≡ i A σ))
                   (Cw ._[_]Tm) (Cw' ._[_]Tm))
    (▹≡ : PathP (λ i → (Γ : Ctx) → Ty≡ i Γ → Ctx) (Cw ._▹_) (Cw' ._▹_))
    (p≡ : PathP (λ i → {Γ : Ctx} {A : Ty≡ i Γ} → ▹≡ i Γ A ⟶ Γ) (Cw .p) (Cw' .p))
    (q≡ : PathP (λ i → {Γ : Ctx} {A : Ty≡ i Γ}
                     → Tm≡ i (▹≡ i Γ A) ([]Ty≡ i A (p≡ i)))
                (Cw .q) (Cw' .q))
    (⁺≡ : PathP (λ i → {Γ Δ : Ctx} {A : Ty≡ i Γ} (σ : Δ ⟶ Γ)
                     → ▹≡ i Δ ([]Ty≡ i A σ) ⟶ ▹≡ i Γ A)
                (Cw ._⁺) (Cw' ._⁺))
    (⟨⟩'≡ : PathP (λ i → {Γ : Ctx} {A : Ty≡ i Γ} → Tm≡ i Γ A → Γ ⟶ ▹≡ i Γ A)
                  (Cw .⟨_⟩) (Cw' .⟨_⟩))
    where

    private
      -- The propositional fields, in dependency order: each one is stated as a
      -- `PathP` over the computational data above and filled by `isProp→PathP`.
      -- They are defined *before* the record so that no clause of
      -- `makeACwFPath` refers to `makeACwFPath` itself.

      isSetTy≡ : PathP (λ i → (Γ : Ctx) → isSet (Ty≡ i Γ))
                       (Cw .isSetTy) (Cw' .isSetTy)
      isSetTy≡ = isProp→PathP (λ i → isPropΠ λ _ → isPropIsSet) _ _

      isSetTm≡ : PathP (λ i → (Γ : Ctx) (A : Ty≡ i Γ) → isSet (Tm≡ i Γ A))
                       (Cw .isSetTm) (Cw' .isSetTm)
      isSetTm≡ = isProp→PathP (λ i → isPropΠ2 λ _ _ → isPropIsSet) _ _

      [id]Ty≡ : PathP (λ i → {Γ : Ctx} (A : Ty≡ i Γ) → []Ty≡ i A id ≡ A)
                      (Cw .[id]Ty) (Cw' .[id]Ty)
      [id]Ty≡ = isProp→PathP
        (λ i → isPropImplicitΠ λ _ → isPropΠ λ _ → isSetTy≡ i _ _ _) _ _

      [][]Ty≡ : PathP (λ i → {Γ Θ Δ : Ctx} (A : Ty≡ i Γ) (σ' : Θ ⟶ Δ) (σ : Δ ⟶ Γ)
                           → []Ty≡ i A (σ ∘ σ') ≡ []Ty≡ i ([]Ty≡ i A σ) σ')
                      (Cw .[][]Ty) (Cw' .[][]Ty)
      [][]Ty≡ = isProp→PathP
        (λ i → isPropImplicitΠ3 λ _ _ _ → isPropΠ3 λ _ _ _ → isSetTy≡ i _ _ _) _ _

      [id]Tm≡ : PathP (λ i → {Γ : Ctx} {A : Ty≡ i Γ} (a : Tm≡ i Γ A)
                           → PathP (λ j → Tm≡ i Γ ([id]Ty≡ i A j))
                                   ([]Tm≡ i a id) a)
                      (Cw .[id]Tm) (Cw' .[id]Tm)
      [id]Tm≡ = isProp→PathP
        (λ i → isPropImplicitΠ2 λ _ _ → isPropΠ λ _ →
                 isOfHLevelPathP' 1 (isSetTm≡ i _ _) _ _) _ _

      [][]Tm≡ : PathP (λ i → {Γ Θ Δ : Ctx} {A : Ty≡ i Γ}
                             (a : Tm≡ i Γ A) (σ' : Θ ⟶ Δ) (σ : Δ ⟶ Γ)
                           → PathP (λ j → Tm≡ i Θ ([][]Ty≡ i A σ' σ j))
                                   ([]Tm≡ i a (σ ∘ σ'))
                                   ([]Tm≡ i ([]Tm≡ i a σ) σ'))
                      (Cw .[][]Tm) (Cw' .[][]Tm)
      [][]Tm≡ = isProp→PathP
        (λ i → isPropImplicitΠ4 λ _ _ _ _ → isPropΠ3 λ _ _ _ →
                 isOfHLevelPathP' 1 (isSetTm≡ i _ _) _ _) _ _

      ⟨⟩∘≡ : PathP (λ i → {Γ Δ : Ctx} {A : Ty≡ i Γ} (a : Tm≡ i Γ A) (σ : Δ ⟶ Γ)
                        → ⟨⟩'≡ i a ∘ σ ≡ ⁺≡ i σ ∘ ⟨⟩'≡ i ([]Tm≡ i a σ))
                   (Cw .⟨⟩∘) (Cw' .⟨⟩∘)
      ⟨⟩∘≡ = isProp→PathP
        (λ i → isPropImplicitΠ3 λ _ _ _ → isPropΠ2 λ _ _ → isSetHom _ _) _ _

      p⁺∘⟨q⟩≡id≡ : PathP (λ i → {Γ : Ctx} {A : Ty≡ i Γ}
                              → ⁺≡ i (p≡ i {A = A}) ∘ ⟨⟩'≡ i (q≡ i)
                                ≡ id {▹≡ i Γ A})
                         (Cw .p⁺∘⟨q⟩≡id) (Cw' .p⁺∘⟨q⟩≡id)
      p⁺∘⟨q⟩≡id≡ = isProp→PathP
        (λ i → isPropImplicitΠ2 λ _ _ → isSetHom _ _) _ _

      ∘⁺≡ : PathP (λ i → {Γ Θ Δ : Ctx} {A : Ty≡ i Γ} (σ' : Θ ⟶ Δ) (σ : Δ ⟶ Γ)
                       → PathP (λ j → ▹≡ i Θ ([][]Ty≡ i A σ' σ j) ⟶ ▹≡ i Γ A)
                               (⁺≡ i (σ ∘ σ')) (⁺≡ i σ ∘ ⁺≡ i σ'))
                  (Cw .∘⁺) (Cw' .∘⁺)
      ∘⁺≡ = isProp→PathP
        (λ i → isPropImplicitΠ4 λ _ _ _ _ → isPropΠ2 λ _ _ →
                 isOfHLevelPathP' 1 isSetHom _ _) _ _

      id⁺≡ : PathP (λ i → {Γ : Ctx} {A : Ty≡ i Γ}
                        → PathP (λ j → ▹≡ i Γ ([id]Ty≡ i A j) ⟶ ▹≡ i Γ A)
                                (⁺≡ i id) id)
                   (Cw .id⁺) (Cw' .id⁺)
      id⁺≡ = isProp→PathP
        (λ i → isPropImplicitΠ2 λ _ _ → isOfHLevelPathP' 1 isSetHom _ _) _ _

      p∘⁺≡ : PathP (λ i → {Γ Δ : Ctx} {A : Ty≡ i Γ} (σ : Δ ⟶ Γ)
                        → p≡ i {A = A} ∘ ⁺≡ i σ ≡ σ ∘ p≡ i)
                   (Cw .p∘⁺) (Cw' .p∘⁺)
      p∘⁺≡ = isProp→PathP
        (λ i → isPropImplicitΠ3 λ _ _ _ → isPropΠ λ _ → isSetHom _ _) _ _

      [p][⁺]Ty≡ : PathP (λ i → {Γ Δ : Ctx} {A : Ty≡ i Γ}
                               (B : Ty≡ i Γ) (σ : Δ ⟶ Γ)
                             → []Ty≡ i ([]Ty≡ i B (p≡ i {A = A})) (⁺≡ i σ)
                               ≡ []Ty≡ i ([]Ty≡ i B σ) (p≡ i))
                        (Cw .[p][⁺]Ty) (Cw' .[p][⁺]Ty)
      [p][⁺]Ty≡ = isProp→PathP
        (λ i → isPropImplicitΠ3 λ _ _ _ → isPropΠ2 λ _ _ → isSetTy≡ i _ _ _) _ _

      q[⁺]Tm≡ : PathP (λ i → {Γ Δ : Ctx} {A : Ty≡ i Γ} (σ : Δ ⟶ Γ)
                           → PathP (λ j → Tm≡ i (▹≡ i Δ ([]Ty≡ i A σ))
                                                ([p][⁺]Ty≡ i A σ j))
                                   ([]Tm≡ i (q≡ i) (⁺≡ i σ)) (q≡ i))
                      (Cw .q[⁺]Tm) (Cw' .q[⁺]Tm)
      q[⁺]Tm≡ = isProp→PathP
        (λ i → isPropImplicitΠ3 λ _ _ _ → isPropΠ λ _ →
                 isOfHLevelPathP' 1 (isSetTm≡ i _ _) _ _) _ _

      p∘⟨⟩≡id≡ : PathP (λ i → {Γ : Ctx} {A : Ty≡ i Γ} (a : Tm≡ i Γ A)
                            → p≡ i ∘ ⟨⟩'≡ i a ≡ id)
                       (Cw .p∘⟨⟩≡id) (Cw' .p∘⟨⟩≡id)
      p∘⟨⟩≡id≡ = isProp→PathP
        (λ i → isPropImplicitΠ2 λ _ _ → isPropΠ λ _ → isSetHom _ _) _ _

      [p][⟨⟩]Ty≡ : PathP (λ i → {Γ : Ctx} {A : Ty≡ i Γ}
                                (B : Ty≡ i Γ) (a : Tm≡ i Γ A)
                              → []Ty≡ i ([]Ty≡ i B (p≡ i)) (⟨⟩'≡ i a) ≡ B)
                         (Cw .[p][⟨⟩]Ty) (Cw' .[p][⟨⟩]Ty)
      [p][⟨⟩]Ty≡ = isProp→PathP
        (λ i → isPropImplicitΠ2 λ _ _ → isPropΠ2 λ _ _ → isSetTy≡ i _ _ _) _ _

      q[⟨⟩]Tm≡ : PathP (λ i → {Γ : Ctx} {A : Ty≡ i Γ} (a : Tm≡ i Γ A)
                            → PathP (λ j → Tm≡ i Γ ([p][⟨⟩]Ty≡ i A a j))
                                    ([]Tm≡ i (q≡ i) (⟨⟩'≡ i a)) a)
                       (Cw .q[⟨⟩]Tm) (Cw' .q[⟨⟩]Tm)
      q[⟨⟩]Tm≡ = isProp→PathP
        (λ i → isPropImplicitΠ2 λ _ _ → isPropΠ λ _ →
                 isOfHLevelPathP' 1 (isSetTm≡ i _ _) _ _) _ _

    makeACwFPath : Cw ≡ Cw'
    makeACwFPath i .⟨⟩ =
      Σ≡Prop (isPropIsTerminal C) {u = Cw .⟨⟩} {v = Cw' .⟨⟩} ⟨⟩≡ i
    makeACwFPath i .Ty = Ty≡ i
    makeACwFPath i .isSetTy = isSetTy≡ i
    makeACwFPath i ._[_]Ty = []Ty≡ i
    makeACwFPath i .[id]Ty = [id]Ty≡ i
    makeACwFPath i .[][]Ty = [][]Ty≡ i
    makeACwFPath i .Tm = Tm≡ i
    makeACwFPath i .isSetTm = isSetTm≡ i
    makeACwFPath i ._[_]Tm = []Tm≡ i
    makeACwFPath i .[id]Tm = [id]Tm≡ i
    makeACwFPath i .[][]Tm = [][]Tm≡ i
    makeACwFPath i ._▹_ = ▹≡ i
    makeACwFPath i .p = p≡ i
    makeACwFPath i .q = q≡ i
    makeACwFPath i ._⁺ = ⁺≡ i
    makeACwFPath i .⟨_⟩ = ⟨⟩'≡ i
    makeACwFPath i .⟨⟩∘ = ⟨⟩∘≡ i
    makeACwFPath i .p⁺∘⟨q⟩≡id = p⁺∘⟨q⟩≡id≡ i
    makeACwFPath i .∘⁺ = ∘⁺≡ i
    makeACwFPath i .id⁺ = id⁺≡ i
    makeACwFPath i .p∘⁺ = p∘⁺≡ i
    makeACwFPath i .[p][⁺]Ty = [p][⁺]Ty≡ i
    makeACwFPath i .q[⁺]Tm = q[⁺]Tm≡ i
    makeACwFPath i .p∘⟨⟩≡id = p∘⟨⟩≡id≡ i
    makeACwFPath i .[p][⟨⟩]Ty = [p][⟨⟩]Ty≡ i
    makeACwFPath i .q[⟨⟩]Tm = q[⟨⟩]Tm≡ i

