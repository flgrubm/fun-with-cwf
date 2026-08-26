module FinSet-Pi-Contradiction where

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import TarskiUniverse.Base
open import TarskiUniverse.Instances.FinSets
open import ACwF.Base
open import ACwF.Pi
open import ACwF.Instances.TarskiPresheaf
open import Utils.TarskiPresheaf
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Functions.Embedding
open import Cubical.Data.Unit
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Sum
open import Cubical.Relation.Nullary
open import Cubical.Data.SumFin
open import Cubical.Data.FinSet
open import Cubical.Data.FinSet.Cardinality
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation
open import Cubical.Categories.Functors.Constant

-- Construction of a category C such that finite-set-valued presheaves on it
-- have no Π-structure. The result is
--
-- ```agda
-- ¬Π-FinSet : Σ[ C ∈ Category ℓ-zero ℓ-zero ] ¬ (Π-Structure (PRESHEAFU C ℕ-TarskiUniverse) (Psh-CwF C ℕ-TarskiUniverse))
-- ```
module _ where
  data Ob : Type₀ where
    top : Ob
    bot : ℕ → Ob

  Hom : Ob → Ob → Type₀
  Hom top     top     = Unit
  Hom top     (bot n) = ⊥
  Hom (bot n) top     = Unit
  Hom (bot n) (bot m) = n ≡ m

  isPropHom : ∀ {a} {b} → isProp (Hom a b)
  isPropHom {top}   {top}   = isPropUnit
  isPropHom {top}   {bot b} = isProp⊥
  isPropHom {bot a} {top}   = isPropUnit
  isPropHom {bot a} {bot b} = isSetℕ a b

  --  C is a cone with countably many legs:
  --
  --     bot 0   bot 1   bot 2   ⋯   bot n   ⋯
  --       │       │       │           │
  --       └───────┴───┬───┴─── ⋯ ─────┘
  --                   │
  --                   ▼
  --                  top
  --
  --  Each hom set shown here has just one arrow. What makes Π-structures
  --  impossible is that there are uncountably many objects, so this C is not
  --  internal to the tarski universe.
  C : Category ℓ-zero ℓ-zero
  C .Category.ob                              = Ob
  C .Category.Hom[_,_]                        = Hom
  C .Category.id {top}                        = tt
  C .Category.id {bot x}                      = refl
  C .Category._⋆_ {top}   {top}   {top}   f g = tt
  C .Category._⋆_ {bot x} {top}   {top}   f g = tt
  C .Category._⋆_ {bot x} {bot y} {top}   f g = tt
  C .Category._⋆_ {bot x} {bot y} {bot z} f g = f ∙ g
  C .Category.⋆IdL _                          = isPropHom _ _
  C .Category.⋆IdR _                          = isPropHom _ _
  C .Category.⋆Assoc _ _ _                    = isPropHom _ _
  C .Category.isSetHom                        = isProp→isSet isPropHom

  -- now take the presheaf CwF on it.
  CwF : Algebraic.CwF (PRESHEAFU C ℕ-TarskiUniverse) ℓ-zero ℓ-zero
  CwF = Psh-CwF C ℕ-TarskiUniverse

  -- equality decision valued in Fin 2.
  hit : ℕ → ℕ → Fin 2
  hit n x = decRec (λ _ → inr (inl tt)) (λ _ → inl tt) (discreteℕ n x)

  hitnn : ∀ n → hit n n ≡ inr (inl tt)
  hitnn n with discreteℕ n n
  ...          | yes p = refl
  ...          | no  p = ⊥.rec (p refl)
  hitnm : ∀ n m → ¬ (n ≡ m) → hit n m ≡ fzero
  hitnm n m p with discreteℕ n m
  ...              | yes q = ⊥.rec (p q)
  ...              | no  q = refl

  module _ (Π-S : Π-Structure _ CwF) where
    open Π-Structure
    open Category
    open Functor
    open NatTrans
    open Algebraic.CwF CwF
    open TarskiUniverse ℕ-TarskiUniverse

    CtxCat = PRESHEAFU C ℕ-TarskiUniverse
    Ctx = Category.ob CtxCat

    -- Let's choose Γ, A, and B such that Π A B will lead to a contradiction.
    --
    -- Γ : We take for Γ the empty context. One first lemma , `restrict-inj`, is
    -- that terms of types in Γ are defined only by their value at the apex of
    -- the cone.
    --
    -- A: apex has 1 value and bot has 2. This way, ∫ (Γ ▹ A) looks like one
    -- rigid cone plus ω points.
    --
    --     (bot 0 , 0)   (bot 1 , 0)   ⋯        (bot 0 , 1)   (bot 1 , 1)   ⋯
    --          │             │                      ·             ·
    --          └──────┬──────┘                      ·             ·
    --                 ▼                            (no morphisms in at all)
    --            (top , •)
    --
    -- B: We essentially pick the type of booleans. This way, a term Tm (Γ ▹ A)
    -- B has one value fixed in the cone, plus ω boolean choices. There are thus
    -- an uncountable number of terms in B.
    --
    -- The contradiction is that Π A B is a type in Γ. Thus by the lemma, its
    -- terms are fixed by their value at the apex, and Π A B .F-ob apex is a
    -- finite set. Therefore it has a finite number of terms. However, we have
    -- that Tm Γ (Π A B) ≃ Tm (Γ ▹ A) B, and as we have seen above, B has an
    -- infinite number of terms.
    Γ : Ctx
    Γ .F-ob _ = 1
    Γ .F-hom _ x = x
    Γ .F-id = refl
    Γ .F-seq _ _ = refl
    A : Ty Γ
    A .F-ob (top , _) = 1
    A .F-ob (bot n , _) = 2
    A .F-hom {top , _}   {top , _}   _ x = x
    A .F-hom {top , _}   {bot _ , _} _ _ = inl tt
    A .F-hom {bot _ , _} {top , _}   ()
    A .F-hom {bot _ , _} {bot _ , _} _ x = x
    A .F-id {top , _}                            = refl
    A .F-id {bot _ , _}                          = refl
    A .F-seq {top , _}   {top , _}   {top , _}   _ _ = refl
    A .F-seq {top , _}   {top , _}   {bot _ , _} _ _ = refl
    A .F-seq {top , _}   {bot _ , _} {top , _}   _ ()
    A .F-seq {top , _}   {bot _ , _} {bot _ , _} _ _ = refl
    A .F-seq {bot _ , _} {top , _}               ()
    A .F-seq {bot _ , _} {bot _ , _} {top , _}   _ ()
    A .F-seq {bot _ , _} {bot _ , _} {bot _ , _} _ _ = refl
    B : Ty (Γ ▹ A)
    B = Constant _ _ 2

    apex : Ob × El (Γ ⟅ top ⟆)
    apex = top , inl tt
    restrict : (T : Ty Γ) → Tm Γ T → El (T ⟅ apex ⟆)
    restrict T t = t .N-ob apex (inl tt)

    restrict-inj : (T : Ty Γ) (t s : Tm Γ T) → restrict T t ≡ restrict T s → t ≡ s
    restrict-inj T t s path = makeNatTransPath (funExt λ z → goal z )
      where
        leg : ∀ n y → (∫U Γ) [ (top , inl tt) , (bot n , y) ]
        leg n y = tt , isContr→isProp isContrSumFin1 _ _
        goal : ∀ z → N-ob t z ≡ N-ob s z
        goal (top , inl tt) = funExt λpath
          where
            λpath : ∀ x → (N-ob t (top , inl tt) x) ≡ (N-ob s (top , inl tt) x)
            λpath (inl tt) = path
        goal (bot n , y) =
          t .N-ob (bot n , y)                                   ≡⟨ t .N-hom (leg n y) ⟩
          (λ u → T .F-hom (leg n y) (t .N-ob (top , inl tt) u)) ≡⟨ (λ i u → T .F-hom (leg n y) (goal (top , inl tt) i u)) ⟩
          (λ u → T .F-hom (leg n y) (s .N-ob (top , inl tt) u)) ≡⟨ sym (s .N-hom (leg n y)) ⟩
          s .N-ob (bot n , y)                                   ∎


    -- An infinite number of distinct terms in B. tn n is inl tt everywhere
    -- except at the free point of leg n
    tn : ℕ → Tm (Γ ▹ A) B
    tn n .N-ob (top , _)              _ = inl tt
    tn n .N-ob (bot _ , inl tt)       _ = inl tt
    tn n .N-ob (bot x , inr (inl tt)) _ = hit n x
    -- both Psh-UnitType and B are Constant, so this says: tn n is constant
    -- along morphisms.  The absurd cases are the point of the counterexample:
    -- nothing maps into a free point, since A ⟪ top ⟶ bot ⟫ is constantly inl tt.
    tn n .N-hom {top , _}                {top , _}                _ = refl
    tn n .N-hom {top , _}                {bot _ , inl tt}         _ = refl
    tn n .N-hom {top , inl tt}           {bot _ , inr (inl tt)}   f =
      ⊥.rec (⊎Path.inl≢inr _ _ (f .snd))
    tn n .N-hom {bot _ , _}              {top , _}                (() , _)
    tn n .N-hom {bot _ , inl tt}         {bot _ , inl tt}         _ = refl
    tn n .N-hom {bot _ , inl tt}         {bot _ , inr (inl tt)}   f =
      ⊥.rec (⊎Path.inl≢inr _ _ (f .snd))
    tn n .N-hom {bot _ , inr (inl tt)}   {bot _ , inl tt}         f =
      ⊥.rec (⊎Path.inl≢inr _ _ (sym (f .snd)))
    tn n .N-hom {bot _ , inr (inl tt)}   {bot _ , inr (inl tt)}   f =
      λ i _ → hit n (f .fst i)

    tn-injective : ∀ n m → tn n ≡ tn m → n ≡ m
    tn-injective n m path = goal
      where
        pa : hit n n ≡ hit m n
        pa = cong (λ t → t .N-ob (bot n , inr (inl tt)) (inl tt)) path
        pb : ¬ (m ≡ n) → fsuc fzero ≡ fzero
        pb neq = sym (hitnn n) ∙ pa ∙ hitnm m n neq
        goal : n ≡ m
        goal = decRec (λ eq → eq) (λ neq → ⊥.rec (⊎Path.inl≢inr _ _ (sym (pb (λ eq → neq (sym eq)))))) (discreteℕ n m)

    -- now we can show that ℕ ↪ Tm (Γ ▹ A) B ≃ Tm Γ (Π A B) ↪ Fin k
    embed₁ : ℕ ↪ Tm (Γ ▹ A) B
    embed₁ = tn , injEmbedding (isSetTm _ _) (tn-injective _ _)

    embed₂ : Tm Γ (Π-S .ΠTy A B) ↪ El (Π-S .ΠTy A B .F-ob apex)
    embed₂ = (restrict _) , (injEmbedding (isSetEl _) (restrict-inj _ _ _))

    k-embed : Σ[ k ∈ ℕ ] ℕ ↪ Fin k
    k-embed = _ , compEmbedding embed₂ (compEmbedding (Equiv→Embedding (isoToEquiv (invIso (Π-S .ΠTmIso _ _)))) embed₁)
    k = k-embed .fst
    embed : Fin (suc k) ↪ Fin k
    embed = compEmbedding (k-embed .snd) ℕemb
      where
        ℕemb : ∀ {n} → Fin n ↪ ℕ
        ℕemb = toℕ , injEmbedding isSetℕ toℕ-injective

    -- and we conclude by a kind of pigeonhole principle.
    k<k : suc k ≤ k
    k<k = card↪Inequality (_ , isFinSetFin) (_ , isFinSetFin) ∣ embed ∣₁

    Π-Structure-FinSet→⊥ : ⊥
    Π-Structure-FinSet→⊥ = <-irrefl k<k

¬Π-FinSet : Σ[ C ∈ Category ℓ-zero ℓ-zero ] ¬ (Π-Structure (PRESHEAFU C ℕ-TarskiUniverse) (Psh-CwF C ℕ-TarskiUniverse))
¬Π-FinSet = C , Π-Structure-FinSet→⊥
