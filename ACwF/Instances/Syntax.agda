-- | The syntax of type theory as a quotient inductive-inductive type, following
-- Altenkirch–Kaposi, "Type theory in type theory using quotient inductive
-- types" (POPL 2016): substitutions are built from `ε` and `_,_` and taken
-- apart with `π₁`/`π₂`.  The Pitts-style operations of `ACwF.Base`
-- (`p`, `q`, `_⁺`, `⟨_⟩`) are defined, and their laws proved.
--
-- Agda checks each data definition as a whole, so constructors of distinct
-- sorts cannot refer to each other cyclically; yet the signature does
-- (`[][]Ty` uses `_∘_`, `_,_` uses `_[_]Ty`, `,∘` uses `_[_]Tm`).
-- Substitutions, types and terms are therefore one family `Syn` indexed by a
-- `Sort`, whose constructors may mention each other freely.
module ACwF.Instances.Syntax where

open import Cubical.Foundations.Prelude hiding (Sub)
open import Cubical.Foundations.Transport using (subst⁻)
open import Cubical.Data.Sigma using (ΣPathP)
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import ACwF.Base
open import ACwF.Morphism
import ACwF.Comprehension

data Con  : Type
data Sort : Con → Type
data Syn  : (Γ : Con) → Sort Γ → Type

data Sort where
  ty  : {Γ : Con} → Sort Γ
  sub : {Δ : Con} (Γ : Con) → Sort Δ
  tm  : {Γ : Con} → Syn Γ ty → Sort Γ

Ty : Con → Type
Ty Γ = Syn Γ ty

Sub : Con → Con → Type
Sub Δ Γ = Syn Δ (sub Γ)

Tm : (Γ : Con) → Ty Γ → Type
Tm Γ A = Syn Γ (tm A)

data Con where
  ◇   : Con
  _▹_ : (Γ : Con) → Ty Γ → Con

infixr 4  _,_
infixl 30 _▹_
infix  40 _[_]Ty _[_]Tm
infixr 50 _∘_
infix  60 _⁺

private variable
  Θ Δ Γ Ξ : Con

data Syn where
  -- | Category of substitutions
  id     : Sub Γ Γ
  _∘_    : Sub Δ Γ → Sub Θ Δ → Sub Θ Γ
  idr    : (σ : Sub Δ Γ) → σ ∘ id ≡ σ
  idl    : (σ : Sub Δ Γ) → id ∘ σ ≡ σ
  assoc  : (ν : Sub Ξ Θ) (δ : Sub Θ Δ) (σ : Sub Δ Γ)
         → σ ∘ (δ ∘ ν) ≡ (σ ∘ δ) ∘ ν

  -- | Types
  _[_]Ty : Ty Γ → Sub Δ Γ → Ty Δ
  [id]Ty : (A : Ty Γ) → A [ id ]Ty ≡ A
  [][]Ty : (A : Ty Γ) (σ' : Sub Θ Δ) (σ : Sub Δ Γ)
         → A [ σ ∘ σ' ]Ty ≡ A [ σ ]Ty [ σ' ]Ty

  -- | Terms
  _[_]Tm : {A : Ty Γ} → Tm Γ A → (σ : Sub Δ Γ) → Tm Δ (A [ σ ]Ty)
  [id]Tm : {A : Ty Γ} (a : Tm Γ A)
         → PathP (λ i → Tm Γ ([id]Ty A i)) (a [ id ]Tm) a
  [][]Tm : {A : Ty Γ} (a : Tm Γ A) (σ' : Sub Θ Δ) (σ : Sub Δ Γ)
         → PathP (λ i → Tm Θ ([][]Ty A σ' σ i))
                 (a [ σ ∘ σ' ]Tm) (a [ σ ]Tm [ σ' ]Tm)

  -- | Substitutions as lists of terms
  ε      : Sub Γ ◇
  εη     : (σ : Sub Γ ◇) → ε ≡ σ
  _,_    : {A : Ty Γ} (σ : Sub Δ Γ) → Tm Δ (A [ σ ]Ty) → Sub Δ (Γ ▹ A)
  π₁     : {A : Ty Γ} → Sub Δ (Γ ▹ A) → Sub Δ Γ
  π₂     : {A : Ty Γ} (σ : Sub Δ (Γ ▹ A)) → Tm Δ (A [ π₁ σ ]Ty)
  π₁β    : {A : Ty Γ} (σ : Sub Δ Γ) (t : Tm Δ (A [ σ ]Ty)) → π₁ (σ , t) ≡ σ
  π₂β    : {A : Ty Γ} (σ : Sub Δ Γ) (t : Tm Δ (A [ σ ]Ty))
         → PathP (λ i → Tm Δ (A [ π₁β σ t i ]Ty)) (π₂ (σ , t)) t
  πη     : {A : Ty Γ} (σ : Sub Δ (Γ ▹ A)) → (π₁ σ , π₂ σ) ≡ σ
  -- AK's `,∘` has `subst⁻ (Tm Θ) ([][]Ty A ν σ) (t [ ν ]Tm)` in place of `t'`,
  -- but a transport along a family built from `Syn` is not strictly positive.
  -- Abstracting the transported term over its defining path is equivalent
  -- (singletons are contractible) and transport-free.
  ,∘     : {A : Ty Γ} (σ : Sub Δ Γ) (t : Tm Δ (A [ σ ]Ty)) (ν : Sub Θ Δ)
           (t' : Tm Θ (A [ σ ∘ ν ]Ty))
         → PathP (λ i → Tm Θ ([][]Ty A ν σ i)) t' (t [ ν ]Tm)
         → (σ , t) ∘ ν ≡ (σ ∘ ν , t')

  -- | Set-truncation, for all three sorts at once
  trunc  : {s : Sort Γ} → isSet (Syn Γ s)

-- | Term equations as paths in the total space `Σ (Ty Γ) (Tm Γ)`.
-- These compose with plain `_∙_`; since `Ty Γ` is a set, they are converted
-- back to a `PathP` over whichever type-path is wanted.

private
  ∫Tm≡→PathP : {A B : Ty Γ} {e : A ≡ B} {x : Tm Γ A} {y : Tm Γ B}
             → Path (Σ (Ty Γ) (Tm Γ)) (A , x) (B , y)
             → PathP (λ i → Tm Γ (e i)) x y
  ∫Tm≡→PathP {Γ = Γ} {x = x} {y = y} P =
    subst (λ e → PathP (λ i → Tm Γ (e i)) x y) (trunc _ _ _ _) (cong snd P)

  coe⁻P : {A B : Ty Γ} (e : A ≡ B) (x : Tm Γ B)
        → PathP (λ i → Tm Γ (e i)) (subst⁻ (Tm Γ) e x) x
  coe⁻P {Γ = Γ} e x = symP (subst-filler (Tm Γ) (sym e) x)

  coe⁻∫ : {A B : Ty Γ} (e : A ≡ B) (x : Tm Γ B)
        → Path (Σ (Ty Γ) (Tm Γ)) (A , subst⁻ (Tm Γ) e x) (B , x)
  coe⁻∫ e x = ΣPathP (e , coe⁻P e x)

  sub∫ : Sub Δ Γ → Σ (Ty Γ) (Tm Γ) → Σ (Ty Δ) (Tm Δ)
  sub∫ σ (B , x) = B [ σ ]Ty , x [ σ ]Tm

  -- The second projection, packed with its type.
  π∫ : {A : Ty Γ} → Sub Δ (Γ ▹ A) → Σ (Ty Δ) (Tm Δ)
  π∫ {A = A} τ = A [ π₁ τ ]Ty , π₂ τ

  π₂β∫ : {A : Ty Γ} (σ : Sub Δ Γ) (t : Tm Δ (A [ σ ]Ty))
       → π∫ (σ , t) ≡ (A [ σ ]Ty , t)
  π₂β∫ {A = A} σ t = ΣPathP (cong (A [_]Ty) (π₁β σ t) , π₂β σ t)

  -- Extensionality of substitutions into an extended context.
  Sub▹≡ : {A : Ty Γ} {τ τ' : Sub Δ (Γ ▹ A)}
        → π₁ τ ≡ π₁ τ' → π∫ τ ≡ π∫ τ' → τ ≡ τ'
  Sub▹≡ {A = A} {τ = τ} {τ'} e P =
    sym (πη τ) ∙∙ (λ i → e i , ∫Tm≡→PathP {e = cong (A [_]Ty) e} P i) ∙∙ πη τ'

  π₁∘ : {A : Ty Γ} (σ : Sub Δ (Γ ▹ A)) (ν : Sub Θ Δ)
      → π₁ σ ∘ ν ≡ π₁ (σ ∘ ν)
  π₁∘ {A = A} σ ν = sym (π₁β (π₁ σ ∘ ν) _)
          ∙ cong π₁ (sym (,∘ (π₁ σ) (π₂ σ) ν _ (coe⁻P ([][]Ty A ν (π₁ σ)) _))
                     ∙ cong (_∘ ν) (πη σ))

  π₂∘ : {A : Ty Γ} (σ : Sub Δ (Γ ▹ A)) (ν : Sub Θ Δ)
      → sub∫ ν (π∫ σ) ≡ π∫ (σ ∘ ν)
  π₂∘ {A = A} σ ν = sym (coe⁻∫ ([][]Ty A ν (π₁ σ)) (π₂ σ [ ν ]Tm))
                  ∙ sym (π₂β∫ (π₁ σ ∘ ν) _)
                  ∙ cong π∫ (sym (,∘ (π₁ σ) (π₂ σ) ν _ (coe⁻P ([][]Ty A ν (π₁ σ)) _))
                             ∙ cong (_∘ ν) (πη σ))

-- | The Pitts-style operations

p : {A : Ty Γ} → Sub (Γ ▹ A) Γ
p = π₁ id

q : {A : Ty Γ} → Tm (Γ ▹ A) (A [ p ]Ty)
q = π₂ id

-- Weakening along any type equal to `A [ ρ ]Ty`; `_⁺` is the case `refl`.
-- The generality is what lets `∘⁺` and `id⁺` move along a path of contexts.
--
-- `wk⁺` and `⟨_⟩` contain a transport, so they are opaque and used only
-- through their `π₁`/`π₂` lemmas.  Otherwise Agda unfolds them when comparing
-- types (the boundary of `∘⁺`, the field `p⁺∘⟨q⟩≡id`) and normalises the
-- transport instead of comparing arguments: neither finished in 2 min.
opaque
  wk⁺ : {A : Ty Γ} {B : Ty Δ} (ρ : Sub Δ Γ) → A [ ρ ]Ty ≡ B → Sub (Δ ▹ B) (Γ ▹ A)
  wk⁺ {Δ = Δ} {A = A} {B} ρ e =
    ρ ∘ p , subst⁻ (Tm (Δ ▹ B)) ([][]Ty A (p {A = B}) ρ ∙ cong (_[ p ]Ty) e) q

  wk⁺-π₁ : {A : Ty Γ} {B : Ty Δ} (ρ : Sub Δ Γ) (e : A [ ρ ]Ty ≡ B)
         → π₁ (wk⁺ ρ e) ≡ ρ ∘ p
  wk⁺-π₁ ρ e = π₁β (ρ ∘ p) _

  wk⁺-π₂ : {A : Ty Γ} {B : Ty Δ} (ρ : Sub Δ Γ) (e : A [ ρ ]Ty ≡ B)
         → π∫ (wk⁺ ρ e) ≡ (B [ p ]Ty , q)
  wk⁺-π₂ {A = A} {B} ρ e =
    π₂β∫ (ρ ∘ p) _ ∙ coe⁻∫ ([][]Ty A (p {A = B}) ρ ∙ cong (_[ p ]Ty) e) q

_⁺ : {A : Ty Γ} (σ : Sub Δ Γ) → Sub (Δ ▹ A [ σ ]Ty) (Γ ▹ A)
σ ⁺ = wk⁺ σ refl

opaque
  ⟨_⟩ : {A : Ty Γ} → Tm Γ A → Sub Γ (Γ ▹ A)
  ⟨_⟩ {Γ = Γ} {A = A} a = id , subst⁻ (Tm Γ) ([id]Ty A) a

  ⟨⟩-π₁ : {A : Ty Γ} (a : Tm Γ A) → π₁ ⟨ a ⟩ ≡ id
  ⟨⟩-π₁ a = π₁β id _

  ⟨⟩-π₂ : {A : Ty Γ} (a : Tm Γ A) → π∫ ⟨ a ⟩ ≡ (A , a)
  ⟨⟩-π₂ {A = A} a = π₂β∫ id _ ∙ coe⁻∫ ([id]Ty A) a

private
  p∘ : {A : Ty Γ} (τ : Sub Δ (Γ ▹ A)) → p ∘ τ ≡ π₁ τ
  p∘ τ = π₁∘ id τ ∙ cong π₁ (idl τ)

  q[] : {A : Ty Γ} (τ : Sub Δ (Γ ▹ A)) → sub∫ τ (A [ p ]Ty , q) ≡ π∫ τ
  q[] τ = π₂∘ id τ ∙ cong π∫ (idl τ)

-- | The Pitts-style laws

p∘⟨⟩≡id : {A : Ty Γ} (a : Tm Γ A) → p ∘ ⟨ a ⟩ ≡ id
p∘⟨⟩≡id a = p∘ ⟨ a ⟩ ∙ ⟨⟩-π₁ a

[p][⟨⟩]Ty : {A : Ty Γ} (B : Ty Γ) (a : Tm Γ A) → B [ p ]Ty [ ⟨ a ⟩ ]Ty ≡ B
[p][⟨⟩]Ty B a = sym ([][]Ty B ⟨ a ⟩ p) ∙ cong (B [_]Ty) (p∘⟨⟩≡id a) ∙ [id]Ty B

private
  q[⟨⟩]∫ : {A : Ty Γ} (a : Tm Γ A)
         → (A [ p ]Ty [ ⟨ a ⟩ ]Ty , q [ ⟨ a ⟩ ]Tm) ≡ (A , a)
  q[⟨⟩]∫ a = q[] ⟨ a ⟩ ∙ ⟨⟩-π₂ a

q[⟨⟩]Tm : {A : Ty Γ} (a : Tm Γ A)
        → PathP (λ i → Tm Γ ([p][⟨⟩]Ty A a i)) (q [ ⟨ a ⟩ ]Tm) a
q[⟨⟩]Tm a = ∫Tm≡→PathP (q[⟨⟩]∫ a)

p∘⁺ : {A : Ty Γ} (σ : Sub Δ Γ) → p {A = A} ∘ σ ⁺ ≡ σ ∘ p
p∘⁺ σ = p∘ (σ ⁺) ∙ wk⁺-π₁ σ refl

[p][⁺]Ty : {A : Ty Γ} (B : Ty Γ) (σ : Sub Δ Γ)
         → B [ p {A = A} ]Ty [ σ ⁺ ]Ty ≡ B [ σ ]Ty [ p ]Ty
[p][⁺]Ty B σ = sym ([][]Ty B (σ ⁺) p) ∙ cong (B [_]Ty) (p∘⁺ σ) ∙ [][]Ty B p σ

private
  q[⁺]∫ : {A : Ty Γ} (σ : Sub Δ Γ)
        → (A [ p ]Ty [ σ ⁺ ]Ty , q [ σ ⁺ ]Tm) ≡ (A [ σ ]Ty [ p ]Ty , q)
  q[⁺]∫ σ = q[] (σ ⁺) ∙ wk⁺-π₂ σ refl

q[⁺]Tm : {A : Ty Γ} (σ : Sub Δ Γ)
       → PathP (λ i → Tm (Δ ▹ A [ σ ]Ty) ([p][⁺]Ty A σ i)) (q [ σ ⁺ ]Tm) q
q[⁺]Tm σ = ∫Tm≡→PathP (q[⁺]∫ σ)

⟨⟩∘ : {A : Ty Γ} (a : Tm Γ A) (σ : Sub Δ Γ) → ⟨ a ⟩ ∘ σ ≡ σ ⁺ ∘ ⟨ a [ σ ]Tm ⟩
⟨⟩∘ a σ = Sub▹≡
  (  sym (π₁∘ ⟨ a ⟩ σ)
   ∙ cong (_∘ σ) (⟨⟩-π₁ a)
   ∙ idl σ
   ∙ sym (idr σ)
   ∙ cong (σ ∘_) (sym (p∘⟨⟩≡id (a [ σ ]Tm)))
   ∙ assoc ⟨ a [ σ ]Tm ⟩ p σ
   ∙ cong (_∘ ⟨ a [ σ ]Tm ⟩) (sym (wk⁺-π₁ σ refl))
   ∙ π₁∘ (σ ⁺) ⟨ a [ σ ]Tm ⟩)
  (  sym (π₂∘ ⟨ a ⟩ σ)
   ∙ cong (sub∫ σ) (⟨⟩-π₂ a)
   ∙ sym (q[⟨⟩]∫ (a [ σ ]Tm))
   ∙ cong (sub∫ ⟨ a [ σ ]Tm ⟩) (sym (wk⁺-π₂ σ refl))
   ∙ π₂∘ (σ ⁺) ⟨ a [ σ ]Tm ⟩)

p⁺∘⟨q⟩≡id : {A : Ty Γ} → p ⁺ ∘ ⟨ q ⟩ ≡ id {Γ ▹ A}
p⁺∘⟨q⟩≡id {A = A} = Sub▹≡
  (  sym (π₁∘ (p ⁺) ⟨ q ⟩)
   ∙ cong (_∘ ⟨ q ⟩) (wk⁺-π₁ p refl)
   ∙ sym (assoc ⟨ q ⟩ p p)
   ∙ cong (p ∘_) (p∘⟨⟩≡id q)
   ∙ idr p)
  (  sym (π₂∘ (p ⁺) ⟨ q ⟩)
   ∙ cong (sub∫ ⟨ q ⟩) (wk⁺-π₂ p refl)
   ∙ q[⟨⟩]∫ q)

∘⁺ : {A : Ty Γ} (σ' : Sub Θ Δ) (σ : Sub Δ Γ)
   → PathP (λ i → Sub (Θ ▹ [][]Ty A σ' σ i) (Γ ▹ A)) ((σ ∘ σ') ⁺) (σ ⁺ ∘ σ' ⁺)
∘⁺ {A = A} σ' σ =
  (λ i → wk⁺ (σ ∘ σ') (λ j → [][]Ty A σ' σ (i ∧ j))) ▷ Sub▹≡
    (  wk⁺-π₁ (σ ∘ σ') ([][]Ty A σ' σ)
     ∙ sym (assoc p σ' σ)
     ∙ cong (σ ∘_) (sym (p∘⁺ σ'))
     ∙ assoc (σ' ⁺) p σ
     ∙ cong (_∘ σ' ⁺) (sym (wk⁺-π₁ σ refl))
     ∙ π₁∘ (σ ⁺) (σ' ⁺))
    (  wk⁺-π₂ (σ ∘ σ') ([][]Ty A σ' σ)
     ∙ sym (q[⁺]∫ {A = A [ σ ]Ty} σ')
     ∙ cong (sub∫ (σ' ⁺)) (sym (wk⁺-π₂ {A = A} σ refl))
     ∙ π₂∘ (σ ⁺) (σ' ⁺))

id⁺ : {A : Ty Γ} → PathP (λ i → Sub (Γ ▹ [id]Ty A i) (Γ ▹ A)) (id ⁺) id
id⁺ {A = A} =
  (λ i → wk⁺ id (λ j → [id]Ty A (i ∧ j))) ▷ Sub▹≡
    (wk⁺-π₁ id ([id]Ty A) ∙ idl p)
    (wk⁺-π₂ id ([id]Ty A))

-- | The instance

-- `_⋆_` is diagrammatic, so that the record's `σ ∘ σ'` is definitionally the
-- constructor `σ ∘ σ'`.
SynConCategory : Category ℓ-zero ℓ-zero
SynConCategory .Category.ob = Con
SynConCategory .Category.Hom[_,_] = Sub
SynConCategory .Category.id = id
SynConCategory .Category._⋆_ f g = g ∘ f
SynConCategory .Category.⋆IdL = idr
SynConCategory .Category.⋆IdR = idl
SynConCategory .Category.⋆Assoc = assoc
SynConCategory .Category.isSetHom = trunc

-- Copatterns are qualified rather than opened: the record's projections share
-- their names with the definitions above.
Syn-CwF : Algebraic.CwF SynConCategory ℓ-zero ℓ-zero
Syn-CwF .Algebraic.CwF.⟨⟩ = ◇ , λ Γ → ε , εη
Syn-CwF .Algebraic.CwF.Ty = Ty
Syn-CwF .Algebraic.CwF.isSetTy Γ = trunc
Syn-CwF .Algebraic.CwF._[_]Ty = _[_]Ty
Syn-CwF .Algebraic.CwF.[id]Ty = [id]Ty
Syn-CwF .Algebraic.CwF.[][]Ty = [][]Ty
Syn-CwF .Algebraic.CwF.Tm = Tm
Syn-CwF .Algebraic.CwF.isSetTm Γ A = trunc
Syn-CwF .Algebraic.CwF._[_]Tm = _[_]Tm
Syn-CwF .Algebraic.CwF.[id]Tm = [id]Tm
Syn-CwF .Algebraic.CwF.[][]Tm = [][]Tm
Syn-CwF .Algebraic.CwF._▹_ = _▹_
Syn-CwF .Algebraic.CwF.p = p
Syn-CwF .Algebraic.CwF.q = q
Syn-CwF .Algebraic.CwF._⁺ = _⁺
Syn-CwF .Algebraic.CwF.⟨_⟩ = ⟨_⟩
Syn-CwF .Algebraic.CwF.⟨⟩∘ = ⟨⟩∘
Syn-CwF .Algebraic.CwF.p⁺∘⟨q⟩≡id = p⁺∘⟨q⟩≡id
Syn-CwF .Algebraic.CwF.∘⁺ = ∘⁺
Syn-CwF .Algebraic.CwF.id⁺ = id⁺
Syn-CwF .Algebraic.CwF.p∘⁺ = p∘⁺
Syn-CwF .Algebraic.CwF.[p][⁺]Ty = [p][⁺]Ty
Syn-CwF .Algebraic.CwF.q[⁺]Tm = q[⁺]Tm
Syn-CwF .Algebraic.CwF.p∘⟨⟩≡id = p∘⟨⟩≡id
Syn-CwF .Algebraic.CwF.[p][⟨⟩]Ty = [p][⟨⟩]Ty
Syn-CwF .Algebraic.CwF.q[⟨⟩]Tm = q[⟨⟩]Tm

-- | Initiality

-- The recursor into an arbitrary CwF `M`, by pattern matching on `Syn`.  The
-- meaning of a sort, `El`, is computed together with the interpretation
-- itself, since the meaning of `tm A` mentions the interpretation of `A`.
-- The substitution constructors go to the comprehension structure that
-- `ACwF.Comprehension` derives in `M`.
module Rec {ℓOb ℓHom ℓTy ℓTm : Level} {C : Category ℓOb ℓHom}
  (M : Algebraic.CwF C ℓTy ℓTm) where

  module ℂ = Category C
  module 𝕄 = Algebraic.CwF M
  module ℙ = ACwF.Comprehension M

  lvl : Sort Γ → Level
  lvl ty      = ℓTy
  lvl (sub _) = ℓHom
  lvl (tm _)  = ℓTm

  ⟦_⟧C  : Con → ℂ.ob
  El    : (s : Sort Γ) → Type (lvl s)
  isSetEl : (s : Sort Γ) → isSet (El s)
  ⟦_⟧   : {s : Sort Γ} → Syn Γ s → El s

  -- `El` first: its clauses only mention `⟦_⟧C`/`⟦_⟧`, while theirs need
  -- `El` to compute.
  El {Γ = Γ} ty      = 𝕄.Ty ⟦ Γ ⟧C
  El {Γ = Γ} (sub Δ) = C [ ⟦ Γ ⟧C , ⟦ Δ ⟧C ]
  El {Γ = Γ} (tm A)  = 𝕄.Tm ⟦ Γ ⟧C ⟦ A ⟧

  isSetEl ty      = 𝕄.isSetTy _
  isSetEl (sub _) = ℂ.isSetHom
  isSetEl (tm _)  = 𝕄.isSetTm _ _

  ⟦ ◇ ⟧C     = 𝕄.⟨⟩ .fst
  ⟦ Γ ▹ A ⟧C = ⟦ Γ ⟧C 𝕄.▹ ⟦ A ⟧

  ⟦ id ⟧               = ℂ.id
  ⟦ σ ∘ δ ⟧            = ⟦ σ ⟧ ℂ.∘ ⟦ δ ⟧
  ⟦ idr σ i ⟧          = ℂ.⋆IdL ⟦ σ ⟧ i
  ⟦ idl σ i ⟧          = ℂ.⋆IdR ⟦ σ ⟧ i
  ⟦ assoc ν δ σ i ⟧    = ℂ.⋆Assoc ⟦ ν ⟧ ⟦ δ ⟧ ⟦ σ ⟧ i
  ⟦ A [ σ ]Ty ⟧        = ⟦ A ⟧ 𝕄.[ ⟦ σ ⟧ ]Ty
  ⟦ [id]Ty A i ⟧       = 𝕄.[id]Ty ⟦ A ⟧ i
  ⟦ [][]Ty A σ' σ i ⟧  = 𝕄.[][]Ty ⟦ A ⟧ ⟦ σ' ⟧ ⟦ σ ⟧ i
  ⟦ a [ σ ]Tm ⟧        = ⟦ a ⟧ 𝕄.[ ⟦ σ ⟧ ]Tm
  ⟦ [id]Tm a i ⟧       = 𝕄.[id]Tm ⟦ a ⟧ i
  ⟦ [][]Tm a σ' σ i ⟧  = 𝕄.[][]Tm ⟦ a ⟧ ⟦ σ' ⟧ ⟦ σ ⟧ i
  ⟦ ε ⟧                = 𝕄.⟨⟩ .snd _ .fst
  ⟦ εη σ i ⟧           = 𝕄.⟨⟩ .snd _ .snd ⟦ σ ⟧ i
  ⟦ σ , t ⟧            = ℙ.pair ⟦ σ ⟧ ⟦ t ⟧
  ⟦ π₁ τ ⟧             = 𝕄.p ℂ.∘ ⟦ τ ⟧
  ⟦ π₂ τ ⟧             = ℙ.π₂ ⟦ τ ⟧
  ⟦ π₁β σ t i ⟧        = ℙ.π₁β ⟦ σ ⟧ ⟦ t ⟧ i
  ⟦ π₂β σ t i ⟧        = ℙ.π₂β ⟦ σ ⟧ ⟦ t ⟧ i
  ⟦ πη τ i ⟧           = ℙ.πη ⟦ τ ⟧ i
  ⟦ ,∘ σ t ν t' P i ⟧  = ℙ.pair∘ ⟦ σ ⟧ ⟦ t ⟧ ⟦ ν ⟧ ⟦ t' ⟧ (λ j → ⟦ P j ⟧) i
  ⟦ trunc {s = s} x y e e' i j ⟧ =
    isSetEl s ⟦ x ⟧ ⟦ y ⟧ (cong ⟦_⟧ e) (cong ⟦_⟧ e') i j

  -- `p = π₁ id` and `q = π₂ id` are interpreted up to `p ∘ id ≡ p`.
  ⟦p⟧ : {A : Ty Γ} → ⟦ p {A = A} ⟧ ≡ 𝕄.p
  ⟦p⟧ = ℂ.⋆IdL 𝕄.p

  ⟦q⟧ : {A : Ty Γ}
      → PathP (λ i → 𝕄.Tm ⟦ Γ ▹ A ⟧C (⟦ A ⟧ 𝕄.[ ⟦p⟧ {A = A} i ]Ty)) ⟦ q {A = A} ⟧ 𝕄.q
  ⟦q⟧ {Γ = Γ} {A = A} = 𝕄.reindex
    (ℙ.π₂≡q[] (ℂ.id {⟦ Γ ▹ A ⟧C}) 𝕄.∙Tm 𝕄.[id]Tm (𝕄.q {A = ⟦ A ⟧}))

  ⟦_⟧F : Functor SynConCategory C
  ⟦_⟧F = record
    { F-ob  = ⟦_⟧C
    ; F-hom = ⟦_⟧
    ; F-id  = refl
    ; F-seq = λ _ _ → refl
    }

  rec : CwFMorphism SynConCategory C Syn-CwF M
  rec = record
    { ctxMorph      = ⟦_⟧F
    ; tyMorph       = ⟦_⟧
    ; tmMorph       = ⟦_⟧
    ; preserves⟨⟩   = refl
    ; preserves[]Ty = λ _ → refl
    ; preserves[]Tm = λ _ → refl
    ; preserves▹    = λ _ _ → refl
    ; preservesp    = λ {Γ} {A} → ⟦p⟧ {Γ = Γ} {A = A}
    ; preservesq    = λ {Γ} {A} → 𝕄.reindex (⟦q⟧ {Γ = Γ} {A = A})
    }

SynInitial : {ℓOb ℓHom ℓTy ℓTm : Level} {C : Category ℓOb ℓHom}
             (M : Algebraic.CwF C ℓTy ℓTm)
           → isContr (CwFMorphism SynConCategory C Syn-CwF M)
SynInitial M .fst = Rec.rec M
SynInitial M .snd = {!!}
