-- | Initiality of the syntax: `rec` is the unique morphism into any CwF.
module ACwF.Instances.Syntax.Initial where

open import Cubical.Foundations.Prelude hiding (Sub)
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma using (ΣPathP)
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Limits.Terminal
open import ACwF.Base
open import ACwF.Morphism
open import ACwF.Instances.Syntax.Base
open import ACwF.Instances.Syntax.CwF
import ACwF.Instances.Syntax.Rec as Rec

private variable
  Θ Δ Γ Ξ : Con

module _ {ℓOb ℓHom ℓTy ℓTm : Level} {C : Category ℓOb ℓHom}
  (M : Algebraic.CwF C ℓTy ℓTm) where

  open Rec M

  private
    -- Opaque: only their types are used, and checking `Uniq.rec≡` would
    -- otherwise unfold `HTm q i` through them into transports.
    opaque
      -- Dependent version of `_▷_`.
      ▷P : ∀ {ℓ ℓ'} {A : I → Type ℓ} {B : (i : I) → A i → Type ℓ'}
           {a₀ : A i0} {a₁ a₁' : A i1} (a : PathP A a₀ a₁) (q : a₁ ≡ a₁')
           {b₀ : B i0 a₀} {b₁ : B i1 a₁} {b₁' : B i1 a₁'}
         → PathP (λ i → B i (a i)) b₀ b₁ → PathP (λ j → B i1 (q j)) b₁ b₁'
         → PathP (λ i → B i ((a ▷ q) i)) b₀ b₁'
      ▷P {B = B} a q {b₀ = b₀} b b' i =
        comp (λ k → B i (doubleWhiskFiller refl a q k i))
             (λ k → λ { (i = i0) → b₀ ; (i = i1) → b' k })
             (b i)
  
      -- A path of (type, term) pairs over a line of contexts gives a path of
      -- terms over any path of types: types form a set.
      fromTot : (c : I → ℂ.ob) {T₀ : 𝕄.Ty (c i0)} {T₁ : 𝕄.Ty (c i1)}
                {e : PathP (λ i → 𝕄.Ty (c i)) T₀ T₁}
                {x : 𝕄.Tm (c i0) T₀} {y : 𝕄.Tm (c i1) T₁}
              → PathP (λ i → Σ (𝕄.Ty (c i)) (𝕄.Tm (c i))) (T₀ , x) (T₁ , y)
              → PathP (λ i → 𝕄.Tm (c i) (e i)) x y
      fromTot c {x = x} {y} P =
        subst (λ ε → PathP (λ i → 𝕄.Tm (c i) (ε i)) x y)
              (isOfHLevelPathP' {A = λ i → 𝕄.Ty (c i)} 1 (𝕄.isSetTy _) _ _ _ _)
              (λ i → snd (P i))

  module Uniq (F : CwFMorphism SynConCategory C Syn-CwF M) where

    module F  = CwFMorphism F
    module F₀ = Functor F.ctxMorph

    -- The type path along which `F` preserves `q`.
    Tq : (Γ : Con) (A : Ty Γ)
       → PathP (λ j → 𝕄.Ty (F.preserves▹ Γ A j))
               (F.tyMorph (A [ p ]Ty)) (F.tyMorph A 𝕄.[ 𝕄.p ]Ty)
    Tq Γ A = F.preserves[]Ty p ◁ (λ k → F.tyMorph A 𝕄.[ F.preservesp k ]Ty)

    -- `F` on (type, term) pairs.
    FΣ : Σ (Ty Γ) (Tm Γ) → Σ (𝕄.Ty (F₀.F-ob Γ)) (𝕄.Tm (F₀.F-ob Γ))
    FΣ (A , a) = F.tyMorph A , F.tmMorph a

    -- `h` relates the object parts; `HTy`, `HSub`, `HTm` relate the rest over
    -- it.  Each point constructor is handled by a non-recursive combinator
    -- (`cTy[]`, `cid`, …) taking the results for its arguments, so that the
    -- endpoints of the path-constructor cases can be written in terms of
    -- recursive calls on subterms only (as for the library's `elimProp`s).
    --
    -- Types never mention `h (Γ ▹ A)` but its body `h▹ Γ A` (hence
    -- `HSub▹T`): the termination checker also checks calls in types, and
    -- cannot see that `π₁ τ ↦ h (Γ ▹ A) ↦ HTy A` decreases.

    h     : (Γ : Con) → ⟦ Γ ⟧C ≡ F₀.F-ob Γ
    h▹    : (Γ : Con) (A : Ty Γ) → ⟦ Γ ▹ A ⟧C ≡ F₀.F-ob (Γ ▹ A)
    HTyT  : Ty Γ → Type ℓTy
    HSubT : Sub Δ Γ → Type ℓHom
    HSub▹T : (Γ : Con) (A : Ty Γ) → Sub Δ (Γ ▹ A) → Type ℓHom
    HTmT  : {A : Ty Γ} → HTyT A → Tm Γ A → Type ℓTm

    HTy  : (A : Ty Γ) → HTyT A
    HSub : (σ : Sub Δ Γ) → HSubT σ
    HTm  : {A : Ty Γ} (a : Tm Γ A) → HTmT (HTy A) a

    isPropHTy  : (A : Ty Γ) → isProp (HTyT A)
    isPropHSub : (σ : Sub Δ Γ) → isProp (HSubT σ)
    isPropHTm  : {A : Ty Γ} (HA : HTyT A) (a : Tm Γ A) → isProp (HTmT HA a)

    Hp   : (Γ : Con) (A : Ty Γ)
         → PathP (λ i → C [ h▹ Γ A i , h Γ i ]) 𝕄.p (F₀.F-hom p)
    Hq   : (Γ : Con) (A : Ty Γ)
         → PathP (λ i → Σ (𝕄.Ty (h▹ Γ A i)) (𝕄.Tm (h▹ Γ A i)))
                 (⟦ A ⟧ 𝕄.[ 𝕄.p ]Ty , 𝕄.q) (F.tyMorph (A [ p ]Ty) , F.tmMorph q)

    cTy[] : {A : Ty Γ} {σ : Sub Δ Γ} → HTyT A → HSubT σ → HTyT (A [ σ ]Ty)
    cid   : HSubT (id {Γ})
    c∘    : {σ : Sub Δ Γ} {δ : Sub Θ Δ} → HSubT σ → HSubT δ → HSubT (σ ∘ δ)
    cε    : HSubT (ε {Γ})
    c,    : (A : Ty Γ) {σ : Sub Δ Γ} {t : Tm Δ (A [ σ ]Ty)} (Hσ : HSubT σ)
          → HTmT (cTy[] (HTy A) Hσ) t → HSub▹T Γ A (σ , t)
    cπ₁   : (A : Ty Γ) {τ : Sub Δ (Γ ▹ A)} → HSub▹T Γ A τ → HSubT (π₁ τ)
    cTm[] : {A : Ty Γ} {a : Tm Γ A} {σ : Sub Δ Γ} (HA : HTyT A)
          → HTmT HA a → (Hσ : HSubT σ) → HTmT (cTy[] HA Hσ) (a [ σ ]Tm)
    cπ₂   : (A : Ty Γ) {τ : Sub Δ (Γ ▹ A)} (Hτ : HSub▹T Γ A τ)
          → HTmT (cTy[] (HTy A) (cπ₁ A Hτ)) (π₂ τ)

    HTyT {Γ = Γ} A = PathP (λ i → 𝕄.Ty (h Γ i)) ⟦ A ⟧ (F.tyMorph A)
    HSubT {Δ = Δ} {Γ = Γ} σ = PathP (λ i → C [ h Δ i , h Γ i ]) ⟦ σ ⟧ (F₀.F-hom σ)
    HSub▹T {Δ = Δ} Γ A τ =
      PathP (λ i → C [ h Δ i , h▹ Γ A i ]) ⟦ τ ⟧ (F₀.F-hom τ)
    HTmT {Γ = Γ} HA a = PathP (λ i → 𝕄.Tm (h Γ i) (HA i)) ⟦ a ⟧ (F.tmMorph a)

    h▹ Γ A = (λ i → h Γ i 𝕄.▹ HTy A i) ▷ sym (F.preserves▹ Γ A)

    isPropHTy {Γ = Γ} A = isOfHLevelPathP' 1 (𝕄.isSetTy (F₀.F-ob Γ)) _ _
    isPropHSub σ = isOfHLevelPathP' 1 ℂ.isSetHom _ _
    isPropHTm {Γ = Γ} {A = A} HA a =
      isOfHLevelPathP' 1 (𝕄.isSetTm (F₀.F-ob Γ) (F.tyMorph A)) _ _

    h ◇       = sym F.preserves⟨⟩
    h (Γ ▹ A) = h▹ Γ A

    Hp Γ A = ▷P {B = λ i o → C [ o , h Γ i ]}
      (λ i → h Γ i 𝕄.▹ HTy A i) (sym (F.preserves▹ Γ A))
      (λ _ → 𝕄.p) (symP F.preservesp)

    Hq Γ A = ▷P {B = λ i o → Σ (𝕄.Ty o) (𝕄.Tm o)}
      (λ i → h Γ i 𝕄.▹ HTy A i) (sym (F.preserves▹ Γ A))
      (λ i → HTy A i 𝕄.[ 𝕄.p ]Ty , 𝕄.q)
      (symP (ΣPathP (Tq Γ A , F.preservesq)))

    cTy[] {σ = σ} HA Hσ =
      (λ i → HA i 𝕄.[ Hσ i ]Ty) ▷ sym (F.preserves[]Ty σ)

    cid = (λ _ → ℂ.id) ▷ sym F₀.F-id

    c∘ {σ = σ} {δ} Hσ Hδ =
      (λ i → Hσ i ℂ.∘ Hδ i) ▷ sym (F₀.F-seq δ σ)

    cε {Γ = Γ} = isProp→PathP
      (λ i → isContr→isProp (term i (h Γ i))) ⟦ ε {Γ} ⟧ (F₀.F-hom (ε {Γ}))
      where
        term : (i : I) → isTerminal C (h ◇ i)
        term i = transport-filler (λ j → isTerminal C (h ◇ j)) (𝕄.⟨⟩ .snd) i

    cπ₁ {Γ = Γ} A {τ} Hτ =
      (λ i → Hp Γ A i ℂ.∘ Hτ i)
      ▷ (sym (F₀.F-seq τ p) ∙ cong F₀.F-hom (p∘ τ))

    cTm[] {Δ = Δ} {σ = σ} HA Ha Hσ = fromTot (λ i → h Δ i)
      ((λ i → HA i 𝕄.[ Hσ i ]Ty , Ha i 𝕄.[ Hσ i ]Tm)
       ▷ sym (ΣPathP (F.preserves[]Ty σ , F.preserves[]Tm σ)))

    -- The target `h (Γ ▹ A)` runs through `F.preserves▹`.  Over its first
    -- part we pair the components; along `F.preserves▹` we transport
    -- `F (σ , t)` and compare at the fixed context `F₀.F-ob Δ` by `πη`.
    c, {Γ = Γ} {Δ = Δ} A {σ} {t} Hσ Ht =
      ▷P {B = λ i o → C [ h Δ i , o ]}
        (λ i → h Γ i 𝕄.▹ HTy A i) (sym P▹)
        (λ i → ℙ.pair (Hσ i) (E i)) (symP (τ'-fill ▷ ext))
      where
        P▹  = F.preserves▹ Γ A
        P[] = F.preserves[]Ty {A = A} σ

        t₁ : 𝕄.Tm (F₀.F-ob Δ) (F.tyMorph A 𝕄.[ F₀.F-hom σ ]Ty)
        t₁ = subst (𝕄.Tm (F₀.F-ob Δ)) P[] (F.tmMorph t)

        t₁-fill : PathP (λ j → 𝕄.Tm (F₀.F-ob Δ) (P[] j)) (F.tmMorph t) t₁
        t₁-fill = subst-filler (𝕄.Tm (F₀.F-ob Δ)) P[] (F.tmMorph t)

        E : PathP (λ i → 𝕄.Tm (h Δ i) (HTy A i 𝕄.[ Hσ i ]Ty)) ⟦ t ⟧ t₁
        E = fromTot (λ i → h Δ i)
          (ΣPathP (cTy[] (HTy A) Hσ , Ht) ▷ ΣPathP (P[] , t₁-fill))

        τ' : C [ F₀.F-ob Δ , F₀.F-ob Γ 𝕄.▹ F.tyMorph A ]
        τ' = subst (λ o → C [ F₀.F-ob Δ , o ]) P▹ (F₀.F-hom (σ , t))

        τ'-fill : PathP (λ j → C [ F₀.F-ob Δ , P▹ j ]) (F₀.F-hom (σ , t)) τ'
        τ'-fill = subst-filler (λ o → C [ F₀.F-ob Δ , o ]) P▹ (F₀.F-hom (σ , t))

        e : 𝕄.p ℂ.∘ τ' ≡ F₀.F-hom σ
        e = sym (λ j → F.preservesp j ℂ.∘ τ'-fill j)
          ∙ sym (F₀.F-seq (σ , t) p)
          ∙ cong F₀.F-hom (p∘ (σ , t) ∙ π₁β σ t)

        E' : PathP (λ i → 𝕄.Tm (F₀.F-ob Δ) (F.tyMorph A 𝕄.[ e i ]Ty)) (ℙ.π₂ τ') t₁
        E' = fromTot (λ _ → F₀.F-ob Δ)
          (  ΣPathP (𝕄.[][]Ty (F.tyMorph A) τ' 𝕄.p , ℙ.π₂≡q[] τ')
           ∙ sym (λ j → Tq Γ A j 𝕄.[ τ'-fill j ]Ty , F.preservesq j 𝕄.[ τ'-fill j ]Tm)
           ∙ sym (ΣPathP ( F.preserves[]Ty {A = A [ p {A = A} ]Ty} (σ , t)
                         , F.preserves[]Tm {x = q {A = A}} (σ , t)))
           ∙ cong FΣ
                  (q[] (σ , t) ∙ π₂β∫ σ t)
           ∙ ΣPathP (P[] , t₁-fill))

        ext : τ' ≡ ℙ.pair (F₀.F-hom σ) t₁
        ext = sym (ℙ.πη τ') ∙ (λ i → ℙ.pair (e i) (E' i))

    cπ₂ {Γ = Γ} {Δ = Δ} A {τ} Hτ = fromTot (λ i → h Δ i)
      ((ΣPathP (𝕄.[][]Ty ⟦ A ⟧ ⟦ τ ⟧ 𝕄.p , ℙ.π₂≡q[] ⟦ τ ⟧)
        ◁ (λ i → fst (Hq Γ A i) 𝕄.[ Hτ i ]Ty , snd (Hq Γ A i) 𝕄.[ Hτ i ]Tm))
       ▷ (  sym (ΣPathP ( F.preserves[]Ty {A = A [ p {A = A} ]Ty} τ
                        , F.preserves[]Tm {x = q {A = A}} τ))
          ∙ cong FΣ (q[] τ)))

    HTy (A [ σ ]Ty) = cTy[] (HTy A) (HSub σ)
    HTy ([id]Ty A j) = isProp→PathP
      (λ j → isPropHTy ([id]Ty A j))
      (cTy[] (HTy A) cid) (HTy A) j
    HTy ([][]Ty A σ' σ j) = isProp→PathP
      (λ j → isPropHTy ([][]Ty A σ' σ j))
      (cTy[] (HTy A) (c∘ (HSub σ) (HSub σ')))
      (cTy[] (cTy[] (HTy A) (HSub σ)) (HSub σ')) j
    HTy (trunc x y e e' i j) = isOfHLevel→isOfHLevelDep 2
      (λ A → isProp→isSet (isPropHTy A))
      (HTy x) (HTy y) (cong HTy e) (cong HTy e') (trunc x y e e') i j

    HSub id = cid
    HSub (σ ∘ δ) = c∘ (HSub σ) (HSub δ)
    HSub ε = cε
    HSub (_,_ {A = A} σ t) = c, A (HSub σ) (HTm t)
    HSub (π₁ {A = A} τ) = cπ₁ A (HSub τ)
    HSub (idr σ j) = isProp→PathP
      (λ j → isPropHSub (idr σ j))
      (c∘ (HSub σ) cid) (HSub σ) j
    HSub (idl σ j) = isProp→PathP
      (λ j → isPropHSub (idl σ j))
      (c∘ cid (HSub σ)) (HSub σ) j
    HSub (assoc ν δ σ j) = isProp→PathP
      (λ j → isPropHSub (assoc ν δ σ j))
      (c∘ (HSub σ) (c∘ (HSub δ) (HSub ν)))
      (c∘ (c∘ (HSub σ) (HSub δ)) (HSub ν)) j
    HSub (εη σ j) = isProp→PathP
      (λ j → isPropHSub (εη σ j))
      cε (HSub σ) j
    HSub (π₁β {A = A} σ t j) = isProp→PathP
      (λ j → isPropHSub (π₁β σ t j))
      (cπ₁ A (c, A (HSub σ) (HTm t))) (HSub σ) j
    HSub (πη {A = A} τ j) = isProp→PathP
      (λ j → isPropHSub (πη τ j))
      (c, A (cπ₁ A (HSub τ)) (cπ₂ A (HSub τ))) (HSub τ) j
    HSub (,∘ {A = A} σ t ν t' P j) = isProp→PathP
      (λ j → isPropHSub (,∘ σ t ν t' P j))
      (c∘ (c, A (HSub σ) (HTm t)) (HSub ν))
      (c, A (c∘ (HSub σ) (HSub ν)) (HTm t')) j
    HSub (trunc x y e e' i j) = isOfHLevel→isOfHLevelDep 2
      (λ σ → isProp→isSet (isPropHSub σ))
      (HSub x) (HSub y) (cong HSub e) (cong HSub e') (trunc x y e e') i j

    HTm (_[_]Tm {A = A} a σ) = cTm[] (HTy A) (HTm a) (HSub σ)
    HTm (π₂ {A = A} τ) = cπ₂ A (HSub τ)
    -- In the path cases the type path `HA` is the corresponding clause of
    -- `HTy`, unfolded so as to recurse on subterms only.
    HTm ([id]Tm {A = A} a j) = isProp→PathP
      (λ j → isPropHTm
         (isProp→PathP (λ k → isPropHTy ([id]Ty A k)) (cTy[] (HTy A) cid) (HTy A) j)
         ([id]Tm a j))
      (cTm[] (HTy A) (HTm a) cid) (HTm a) j
    HTm ([][]Tm {A = A} a σ' σ j) = isProp→PathP
      (λ j → isPropHTm
         (isProp→PathP (λ k → isPropHTy ([][]Ty A σ' σ k))
            (cTy[] (HTy A) (c∘ (HSub σ) (HSub σ')))
            (cTy[] (cTy[] (HTy A) (HSub σ)) (HSub σ')) j)
         ([][]Tm a σ' σ j))
      (cTm[] (HTy A) (HTm a) (c∘ (HSub σ) (HSub σ')))
      (cTm[] (cTy[] (HTy A) (HSub σ)) (cTm[] (HTy A) (HTm a) (HSub σ)) (HSub σ')) j
    HTm (π₂β {A = A} σ t j) = isProp→PathP
      (λ j → isPropHTm
         (cTy[] (HTy A) (isProp→PathP (λ k → isPropHSub (π₁β σ t k))
                          (cπ₁ A (c, A (HSub σ) (HTm t))) (HSub σ) j))
         (π₂β σ t j))
      (cπ₂ A (c, A (HSub σ) (HTm t))) (HTm t) j
    HTm {A = A} (trunc x y e e' i j) = isOfHLevel→isOfHLevelDep 2
      (λ a → isProp→isSet (isPropHTm (HTy A) a))
      (HTm x) (HTm y) (cong HTm e) (cong HTm e') (trunc x y e e') i j

    -- | Assembling the path `rec ≡ F`.
    --
    -- From here on the results above are only used through opaque copies:
    -- `rec≡`'s field types mention `Syn-CwF`'s projections (`Syn-CwF .q`,
    -- `Syn-CwF ._[_]Ty`, …) where we write `q`, `_[_]Ty`, …, and comparing,
    -- say, `HTm (Syn-CwF .q) i` with `HTm q i` would unfold `HTm` before its
    -- argument (did not finish in 4 min).  Opaque, they are compared by their
    -- arguments, and their endpoints come from their types.
    opaque
      h° : (Γ : Con) → ⟦ Γ ⟧C ≡ F₀.F-ob Γ
      h° = h

      HTy° : (A : Ty Γ) → PathP (λ i → 𝕄.Ty (h° Γ i)) ⟦ A ⟧ (F.tyMorph A)
      HTy° = HTy

      HSub° : (σ : Sub Δ Γ) → PathP (λ i → C [ h° Δ i , h° Γ i ]) ⟦ σ ⟧ (F₀.F-hom σ)
      HSub° = HSub

      HTm° : {A : Ty Γ} (a : Tm Γ A)
           → PathP (λ i → 𝕄.Tm (h° Γ i) (HTy° A i)) ⟦ a ⟧ (F.tmMorph a)
      HTm° = HTm

      -- The object-level fields of `F` are absorbed into `h`.
      S⟨⟩ : PathP (λ i → h° ◇ i ≡ 𝕄.⟨⟩ .fst) refl F.preserves⟨⟩
      S⟨⟩ i k = F.preserves⟨⟩ (~ i ∨ k)

      S▹ : (Γ : Con) (A : Ty Γ)
         → PathP (λ i → h° (Γ ▹ A) i ≡ h° Γ i 𝕄.▹ HTy° A i) refl (F.preserves▹ Γ A)
      S▹ Γ A i k = doubleWhiskFiller refl (λ i → h Γ i 𝕄.▹ HTy A i)
                                     (sym (F.preserves▹ Γ A)) (~ k) i

    -- The remaining fields are propositions.  Opaque as well, so that their
    -- endpoints come from their types rather than from unfolding
    -- `isProp→PathP`.
    opaque
      P[]Ty : PathP (λ i → ∀ {Γ Δ} {A : Ty Γ} (σ : Sub Δ Γ)
                         → HTy° (A [ σ ]Ty) i ≡ HTy° A i 𝕄.[ HSub° σ i ]Ty)
                    (λ _ → refl) F.preserves[]Ty
      P[]Ty = isProp→PathP
        (λ i → isPropImplicitΠ3 λ _ _ _ → isPropΠ λ _ → 𝕄.isSetTy _ _ _) _ _

      P[]Tm : PathP (λ i → ∀ {Γ Δ} {A : Ty Γ} {x : Tm Γ A} (σ : Sub Δ Γ)
                         → PathP (λ k → 𝕄.Tm (h° Δ i) (P[]Ty i {A = A} σ k))
                                 (HTm° (x [ σ ]Tm) i) (HTm° x i 𝕄.[ HSub° σ i ]Tm))
                    (λ _ → refl) F.preserves[]Tm
      P[]Tm = isProp→PathP
        (λ i → isPropImplicitΠ4 λ _ _ _ _ → isPropΠ λ _ →
                 isOfHLevelPathP' 1 (𝕄.isSetTm _ _) _ _) _ _

      Pp : PathP (λ i → ∀ {Γ} {A : Ty Γ}
                      → PathP (λ k → C [ S▹ Γ A i k , h° Γ i ]) (HSub° (p {A = A}) i) 𝕄.p)
                 (λ {Γ} {A} → ⟦p⟧ {Γ = Γ} {A = A}) F.preservesp
      Pp = isProp→PathP
        (λ i → isPropImplicitΠ2 λ _ _ → isOfHLevelPathP' 1 ℂ.isSetHom _ _) _ _

      Pq : PathP (λ i → ∀ {Γ} {A : Ty Γ}
                      → PathP (λ k → 𝕄.Tm (S▹ Γ A i k)
                                       ((P[]Ty i {A = A} (p {A = A})
                                         ◁ (λ j → HTy° A i 𝕄.[ Pp i {Γ} {A} j ]Ty)) k))
                              (HTm° (q {A = A}) i) 𝕄.q)
                 (λ {Γ} {A} → 𝕄.reindex (⟦q⟧ {Γ = Γ} {A = A})) F.preservesq
      Pq = isProp→PathP
        (λ i → isPropImplicitΠ2 λ Γ A → isOfHLevelPathP' 1
                   (𝕄.isSetTm (h° Γ i 𝕄.▹ HTy° A i) (HTy° A i 𝕄.[ 𝕄.p ]Ty)) _ _) _ _

    rec≡ : rec ≡ F
    rec≡ i .CwFMorphism.ctxMorph =
      Functor≡ {F = ⟦_⟧F} {G = F.ctxMorph} h° HSub° i
    rec≡ i .CwFMorphism.tyMorph A       = HTy° A i
    rec≡ i .CwFMorphism.tmMorph a       = HTm° a i
    rec≡ i .CwFMorphism.preserves⟨⟩     = S⟨⟩ i
    rec≡ i .CwFMorphism.preserves[]Ty   = P[]Ty i
    rec≡ i .CwFMorphism.preserves[]Tm   = P[]Tm i
    rec≡ i .CwFMorphism.preserves▹ Γ A  = S▹ Γ A i
    rec≡ i .CwFMorphism.preservesp      = Pp i
    rec≡ i .CwFMorphism.preservesq      = Pq i

SynInitial : {ℓOb ℓHom ℓTy ℓTm : Level} {C : Category ℓOb ℓHom}
             (M : Algebraic.CwF C ℓTy ℓTm)
           → isContr (CwFMorphism SynConCategory C Syn-CwF M)
SynInitial M .fst = Rec.rec M
SynInitial M .snd F = Uniq.rec≡ M F
