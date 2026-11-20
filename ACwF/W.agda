module ACwF.W where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma

open import Cubical.Categories.Category

open import ACwF.Base
open import ACwF.Pi

open Iso

module _ {ℓOb ℓHom ℓTy ℓTm : Level} {C : Category ℓOb ℓHom} (cwf : Algebraic.CwF C ℓTy ℓTm) where

  open Algebraic C
  open CwF cwf
  open Category C using (_∘_ ; ⋆Assoc ; ⋆IdL)

  private variable
    Δ Γ : Ctx

  -- | W-types, in the presence of Π (the subtrees of a node are a function
  -- out of its branching type).  For labels `A : Ty Γ` and branching
  -- `B : Ty (Γ ▹ A)`:
  --
  --   * a node is a label together with a subtree function, a variable of
  --     the context `NodeCtx A B = Γ ▹ A ▹ ΠTy B (WTy A B ⇑²)`;
  --   * the constructor is a substitution `supSub : NodeCtx A B ⟶ Γ ▹ WTy A B`
  --     over Γ (the generic `sup`);
  --   * applying the subtree function to a branch is a substitution
  --     `branchSub : NodeCtx A B ▹ B ⇑ ⟶ Γ ▹ WTy A B` over Γ;
  --   * elimination with its β- and η-laws: for a motive `P` over a variable
  --     of the W-type and a method `m` that, at a node, uses the induction
  --     hypotheses at its branches, there is exactly one term `s` of `P`
  --     whose instance at a node is the method applied to the instances of
  --     `s` at the branches (`isContrWElim`, as for natural numbers in
  --     Angiuli–Gratzer, Structure 6.3.16).
  --
  -- `wkW`, `supSub` and `branchSub` are derivable, or determined by their
  -- laws, but are fields (Fording) so that a model can supply ones that
  -- compute; with them every field is a `PathP` over a single path, without
  -- transport in its type.
  module _ (Πs : Π-Structure C cwf) where
    open Π-Structure Πs

    record W-Structure : Type (ℓ-max ℓOb (ℓ-max ℓHom (ℓ-max ℓTy ℓTm))) where
      field
        WTy : (A : Ty Γ) (B : Ty (Γ ▹ A))
            → -------------------------------
              Ty Γ

        WTyNat : (A : Ty Γ) (B : Ty (Γ ▹ A)) (σ : Δ ⟶ Γ)
               → ----------------------------------------------------
                 WTy A B [ σ ]Ty ≡ WTy (A [ σ ]Ty) (B [ σ ⁺ ]Ty)

      -- | The subtree functions at a node labelled by the variable.
      SubTy : (A : Ty Γ) (B : Ty (Γ ▹ A)) → Ty (Γ ▹ A)
      SubTy A B = ΠTy B (WTy A B [ p ]Ty [ p ]Ty)

      SubTyNat : (A : Ty Γ) (B : Ty (Γ ▹ A)) (σ : Δ ⟶ Γ)
               → ---------------------------------------------------------
                 SubTy A B [ σ ⁺ ]Ty ≡ SubTy (A [ σ ]Ty) (B [ σ ⁺ ]Ty)
      SubTyNat A B σ =
          ΠTyNat B (WTy A B [ p ]Ty [ p ]Ty) (σ ⁺)
        ∙ cong (ΠTy (B [ σ ⁺ ]Ty))
            ( [p][⁺]Ty {A = B} (WTy A B [ p ]Ty) (σ ⁺)
            ∙ cong (_[ p ]Ty) ([p][⁺]Ty {A = A} (WTy A B) σ)
            ∙ cong (λ T → T [ p ]Ty [ p ]Ty) (WTyNat A B σ))

      NodeCtx : (A : Ty Γ) (B : Ty (Γ ▹ A)) → Ctx
      NodeCtx A B = _ ▹ A ▹ SubTy A B

      BranchCtx : (A : Ty Γ) (B : Ty (Γ ▹ A)) → Ctx
      BranchCtx A B = NodeCtx A B ▹ B [ p ]Ty

      field
        -- | The weakening of σ past a variable of the W-type, retyped along
        -- `WTyNat`.
        wkW : {A : Ty Γ} {B : Ty (Γ ▹ A)} (σ : Δ ⟶ Γ)
            → ----------------------------------------------------
              Δ ▹ WTy (A [ σ ]Ty) (B [ σ ⁺ ]Ty) ⟶ Γ ▹ WTy A B

        wkW≡ : {A : Ty Γ} {B : Ty (Γ ▹ A)} (σ : Δ ⟶ Γ)
             → -------------------------------------------------------------------
               PathP (λ i → Δ ▹ WTyNat A B σ i ⟶ Γ ▹ WTy A B) (σ ⁺) (wkW σ)

        -- | The constructor, generically.
        supSub : {A : Ty Γ} {B : Ty (Γ ▹ A)}
               → ----------------------------
                 NodeCtx A B ⟶ Γ ▹ WTy A B

        p∘supSub : {A : Ty Γ} {B : Ty (Γ ▹ A)}
                 → -----------------------------------------
                   p ∘ supSub {A = A} {B = B} ≡ p ∘ p

        supSubNat : {A : Ty Γ} {B : Ty (Γ ▹ A)} (σ : Δ ⟶ Γ)
                  → -------------------------------------------------------------------
                    PathP (λ i → Δ ▹ A [ σ ]Ty ▹ SubTyNat A B σ i ⟶ Γ ▹ WTy A B)
                          (supSub ∘ (σ ⁺) ⁺) (wkW σ ∘ supSub)

        -- | The subtree at a branch, generically.
        branchSub : {A : Ty Γ} {B : Ty (Γ ▹ A)}
                  → ------------------------------
                    BranchCtx A B ⟶ Γ ▹ WTy A B

        p∘branchSub : {A : Ty Γ} {B : Ty (Γ ▹ A)}
                    → -------------------------------------------------
                      p ∘ branchSub {A = A} {B = B} ≡ p ∘ (p ∘ p)

      -- the type of the subtree, after `branchSub` and as the result of
      -- applying the subtree function
      branchTy : (A : Ty Γ) (B : Ty (Γ ▹ A))
               → -----------------------------------------------------------------------------
                 WTy A B [ p ]Ty [ branchSub ]Ty ≡ WTy A B [ p ]Ty [ p ]Ty [ (p {A = SubTy A B}) ⁺ ]Ty
      branchTy A B =
          sym ([][]Ty (WTy A B) branchSub p)
        ∙ cong (WTy A B [_]Ty)
            ( p∘branchSub
            ∙ cong (p ∘_) (sym (p∘⁺ (p {A = SubTy A B})))
            ∙ ⋆Assoc (p {A = SubTy A B} ⁺) p p)
        ∙ [][]Ty (WTy A B) (p {A = SubTy A B} ⁺) (p ∘ p)
        ∙ cong (_[ p {A = SubTy A B} ⁺ ]Ty) ([][]Ty (WTy A B) p p)

      field
        -- `q [ branchSub ]Tm` is the subtree function applied to the branch.
        -- Stated relationally: whenever `f'` is the variable `q` along
        -- `ΠTyNat`, the subtree is `f'` applied.
        q[branchSub] : {A : Ty Γ} {B : Ty (Γ ▹ A)}
                       {f' : Tm (NodeCtx A B) (ΠTy (B [ p ]Ty) (WTy A B [ p ]Ty [ p ]Ty [ p ⁺ ]Ty))}
                     → PathP (λ i → Tm (NodeCtx A B) (ΠTyNat B (WTy A B [ p ]Ty [ p ]Ty) p i)) q f'
                     → ---------------------------------------------------------------------------
                       PathP (λ i → Tm (BranchCtx A B) (branchTy A B i))
                             (q [ branchSub ]Tm) (ΠTmIso _ _ .fun f')

      -- | Elimination.  The induction hypotheses at a node are a function on
      -- its branches.
      IHTy : (A : Ty Γ) (B : Ty (Γ ▹ A)) (P : Ty (Γ ▹ WTy A B))
           → -----------------------------------------------------
             Ty (NodeCtx A B)
      IHTy A B P = ΠTy (B [ p ]Ty) (P [ branchSub ]Ty)

      -- the induction hypotheses provided by a term of the motive
      ih : (A : Ty Γ) (B : Ty (Γ ▹ A)) (P : Ty (Γ ▹ WTy A B))
         → Tm (Γ ▹ WTy A B) P
         → ---------------------------
           Tm (NodeCtx A B) (IHTy A B P)
      ih A B P s = ΠTmIso (B [ p ]Ty) (P [ branchSub ]Ty) .inv (s [ branchSub ]Tm)

      -- `P` at a node, as the type of the method instantiated at `ih`
      stepTy : (A : Ty Γ) (B : Ty (Γ ▹ A)) (P : Ty (Γ ▹ WTy A B)) (s : Tm (Γ ▹ WTy A B) P)
             → ----------------------------------------------------------------------
               P [ supSub ]Ty ≡ P [ supSub ∘ p ]Ty [ ⟨ ih A B P s ⟩ ]Ty
      stepTy A B P s =
          cong (P [_]Ty) ( sym (⋆IdL supSub)
                         ∙ cong (supSub ∘_) (sym (p∘⟨⟩≡id (ih A B P s)))
                         ∙ ⋆Assoc ⟨ ih A B P s ⟩ p supSub)
        ∙ [][]Ty P ⟨ ih A B P s ⟩ (supSub ∘ p)

      -- `s` is an eliminator for the method `m`: at a node, it is `m` applied
      -- to the induction hypotheses it provides.
      isWElim : (A : Ty Γ) (B : Ty (Γ ▹ A)) (P : Ty (Γ ▹ WTy A B))
                (m : Tm (NodeCtx A B ▹ IHTy A B P) (P [ supSub ∘ p ]Ty))
              → Tm (Γ ▹ WTy A B) P
              → --------------------------------------------------------
                Type ℓTm
      isWElim A B P m s =
        PathP (λ i → Tm (NodeCtx A B) (stepTy A B P s i)) (s [ supSub ]Tm) (m [ ⟨ ih A B P s ⟩ ]Tm)

      field
        isContrWElim : (A : Ty Γ) (B : Ty (Γ ▹ A)) (P : Ty (Γ ▹ WTy A B))
                       (m : Tm (NodeCtx A B ▹ IHTy A B P) (P [ supSub ∘ p ]Ty))
                     → --------------------------------------------------------------
                       isContr (Σ[ s ∈ Tm (Γ ▹ WTy A B) P ] isWElim A B P m s)

      -- | The eliminator with its β- and η-laws.

      wElim : (A : Ty Γ) (B : Ty (Γ ▹ A)) (P : Ty (Γ ▹ WTy A B))
              (m : Tm (NodeCtx A B ▹ IHTy A B P) (P [ supSub ∘ p ]Ty))
            → ---------------------------------------------------------
              Tm (Γ ▹ WTy A B) P
      wElim A B P m = isContrWElim A B P m .fst .fst

      wElim-β : (A : Ty Γ) (B : Ty (Γ ▹ A)) (P : Ty (Γ ▹ WTy A B))
                (m : Tm (NodeCtx A B ▹ IHTy A B P) (P [ supSub ∘ p ]Ty))
              → ---------------------------------------------------------
                isWElim A B P m (wElim A B P m)
      wElim-β A B P m = isContrWElim A B P m .fst .snd

      wElim-η : (A : Ty Γ) (B : Ty (Γ ▹ A)) (P : Ty (Γ ▹ WTy A B))
                (m : Tm (NodeCtx A B ▹ IHTy A B P) (P [ supSub ∘ p ]Ty))
                (s : Tm (Γ ▹ WTy A B) P)
              → isWElim A B P m s
              → ---------------------------------------------------------
                wElim A B P m ≡ s
      wElim-η A B P m s h = cong fst (isContrWElim A B P m .snd (s , h))
