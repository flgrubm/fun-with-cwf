-- | The Pitts-style CwF structure of the syntax: `p`, `q`, `_⁺`, `⟨_⟩` are
-- defined from Altenkirch–Kaposi's comprehension, and their laws proved.
module ACwF.Instances.Syntax.CwF where

open import Cubical.Foundations.Prelude hiding (Sub)
open import Cubical.Foundations.Transport using (subst⁻)
open import Cubical.Data.Sigma using (ΣPathP)
open import Cubical.Categories.Category
open import ACwF.Base
open import ACwF.Instances.Syntax.Base

infix 60 _⁺

private variable
  Θ Δ Γ Ξ : Con

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

-- Used by `ACwF.Instances.Syntax.Initial`.
sub∫ : Sub Δ Γ → Σ (Ty Γ) (Tm Γ) → Σ (Ty Δ) (Tm Δ)
sub∫ σ (B , x) = B [ σ ]Ty , x [ σ ]Tm

-- The second projection, packed with its type.
π∫ : {A : Ty Γ} → Sub Δ (Γ ▹ A) → Σ (Ty Δ) (Tm Δ)
π∫ {A = A} τ = A [ π₁ τ ]Ty , π₂ τ

π₂β∫ : {A : Ty Γ} (σ : Sub Δ Γ) (t : Tm Δ (A [ σ ]Ty))
     → π∫ (σ , t) ≡ (A [ σ ]Ty , t)
π₂β∫ {A = A} σ t = ΣPathP (cong (A [_]Ty) (π₁β σ t) , π₂β σ t)

private
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

-- Used by `ACwF.Instances.Syntax.Initial`.
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
