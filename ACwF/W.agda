module ACwF.W where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism

open import Cubical.Categories.Category

open import ACwF.Base
open import ACwF.Pi

open Iso

module _ {ℓOb ℓHom ℓTy ℓTm : Level} {C : Category ℓOb ℓHom} (cwf : Algebraic.CwF C ℓTy ℓTm) where

  open Algebraic C
  open CwF cwf
  open Category C using (_∘_ ; ⋆Assoc)

  private variable
    Δ Γ : Ctx

  -- | W-types, given Π: the subtrees of a node are a function out of its
  -- branching type.  For labels `A : Ty Γ` and branching `B : Ty (Γ ▹ A)`:
  --
  --   * a node is a label and its subtree function, the last two variables of
  --     `NodeCtx A B = Γ ▹ A ▹ ΠTy B (WTy A B [ p ]Ty [ p ]Ty)`;
  --   * the constructor is a substitution `supSub : NodeCtx A B ⟶ Γ ▹ WTy A B`
  --     over Γ;
  --   * the subtree at a branch is a substitution
  --     `branchSub : NodeCtx A B ▹ B [ p ]Ty ⟶ Γ ▹ WTy A B` over Γ;
  --   * elimination: for a motive `P` and a method `m` that builds `P` at a
  --     node from the induction hypotheses at its branches, exactly one term
  --     `s` of `P` is, at every node, `m` at the induction hypotheses that `s`
  --     provides (`isContrWElim`, as for natural numbers in Angiuli–Gratzer,
  --     Structure 6.3.16).
  --
  -- Redundant on purpose (Fording): `wkW` is determined by `wkW≡`, and
  -- `branchSub` by `p∘branchSub` and `q[branchSub]`; the constructor is a
  -- substitution with the law `p∘supSub` instead of a term of
  -- `WTy A B [ p ]Ty [ p ]Ty`.  A model can then supply substitutions that
  -- compute, and no law has a transport in its type.
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

      -- the type of subtree functions of a node whose label is the variable of `Γ ▹ A`
      SubtreesTy : (A : Ty Γ) (B : Ty (Γ ▹ A)) → Ty (Γ ▹ A)
      SubtreesTy A B = ΠTy B (WTy A B [ p ]Ty [ p ]Ty)

      SubtreesTyNat : (A : Ty Γ) (B : Ty (Γ ▹ A)) (σ : Δ ⟶ Γ)
                    → ---------------------------------------------------------
                 SubtreesTy A B [ σ ⁺ ]Ty ≡ SubtreesTy (A [ σ ]Ty) (B [ σ ⁺ ]Ty)
      SubtreesTyNat A B σ =
          ΠTyNat B (WTy A B [ p ]Ty [ p ]Ty) (σ ⁺)
        ∙ cong (ΠTy (B [ σ ⁺ ]Ty))
            ( [p][⁺]Ty {A = B} (WTy A B [ p ]Ty) (σ ⁺)
            ∙ cong (_[ p ]Ty) ([p][⁺]Ty {A = A} (WTy A B) σ)
            ∙ cong (λ T → T [ p ]Ty [ p ]Ty) (WTyNat A B σ))

      NodeCtx : (A : Ty Γ) (B : Ty (Γ ▹ A)) → Ctx
      NodeCtx A B = _ ▹ A ▹ SubtreesTy A B

      BranchCtx : (A : Ty Γ) (B : Ty (Γ ▹ A)) → Ctx
      BranchCtx A B = NodeCtx A B ▹ B [ p ]Ty

      field
        -- the weakening of σ past a variable of the W-type, retyped along
        -- `WTyNat`
        wkW : {A : Ty Γ} {B : Ty (Γ ▹ A)} (σ : Δ ⟶ Γ)
            → ----------------------------------------------------
              Δ ▹ WTy (A [ σ ]Ty) (B [ σ ⁺ ]Ty) ⟶ Γ ▹ WTy A B

        wkW≡ : {A : Ty Γ} {B : Ty (Γ ▹ A)} (σ : Δ ⟶ Γ)
             → -------------------------------------------------------------------
               PathP (λ i → Δ ▹ WTyNat A B σ i ⟶ Γ ▹ WTy A B) (σ ⁺) (wkW σ)

        -- the constructor, at the node given by the last two variables of `NodeCtx A B`
        supSub : {A : Ty Γ} {B : Ty (Γ ▹ A)}
               → ----------------------------
                 NodeCtx A B ⟶ Γ ▹ WTy A B

        p∘supSub : {A : Ty Γ} {B : Ty (Γ ▹ A)}
                 → -----------------------------------------
                   p ∘ supSub {A = A} {B = B} ≡ p ∘ p

        supSubNat : {A : Ty Γ} {B : Ty (Γ ▹ A)} (σ : Δ ⟶ Γ)
                  → -------------------------------------------------------------------
                    PathP (λ i → Δ ▹ A [ σ ]Ty ▹ SubtreesTyNat A B σ i ⟶ Γ ▹ WTy A B)
                          (supSub ∘ (σ ⁺) ⁺) (wkW σ ∘ supSub)

        -- the subtree at the branch given by the last variable of `BranchCtx A B`
        branchSub : {A : Ty Γ} {B : Ty (Γ ▹ A)}
                  → ------------------------------
                    BranchCtx A B ⟶ Γ ▹ WTy A B

        p∘branchSub : {A : Ty Γ} {B : Ty (Γ ▹ A)}
                    → -------------------------------------------------
                      p ∘ branchSub {A = A} {B = B} ≡ p ∘ (p ∘ p)

      -- the type of `q [ branchSub ]Tm` is the type of the subtree function
      -- applied to the branch
      branchTy : (A : Ty Γ) (B : Ty (Γ ▹ A))
               → -----------------------------------------------------------------------------
                 WTy A B [ p ]Ty [ branchSub ]Ty ≡ WTy A B [ p ]Ty [ p ]Ty [ (p {A = SubtreesTy A B}) ⁺ ]Ty
      branchTy A B =
          sym ([][]Ty (WTy A B) branchSub p)
        ∙ cong (WTy A B [_]Ty)
            ( p∘branchSub
            ∙ cong (p ∘_) (sym (p∘⁺ (p {A = SubtreesTy A B})))
            ∙ ⋆Assoc (p {A = SubtreesTy A B} ⁺) p p)
        ∙ [][]Ty (WTy A B) (p {A = SubtreesTy A B} ⁺) (p ∘ p)
        ∙ cong (_[ p {A = SubtreesTy A B} ⁺ ]Ty) ([][]Ty (WTy A B) p p)

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

      -- | Elimination

      -- the type of the induction hypotheses at a node: a function on its branches
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
             → --------------------------------------------------------------------------
               P [ supSub ]Ty ≡ P [ supSub ]Ty [ p ]Ty [ ⟨ ih A B P s ⟩ ]Ty
      stepTy A B P s = sym ([p][⟨⟩]Ty (P [ supSub ]Ty) (ih A B P s))

      -- `s` is an eliminator for the method `m`: at a node, it is `m` applied
      -- to the induction hypotheses it provides.
      isWElim : (A : Ty Γ) (B : Ty (Γ ▹ A)) (P : Ty (Γ ▹ WTy A B))
                (m : Tm (NodeCtx A B ▹ IHTy A B P) (P [ supSub ]Ty [ p ]Ty))
              → Tm (Γ ▹ WTy A B) P
              → --------------------------------------------------------
                Type ℓTm
      isWElim A B P m s =
        PathP (λ i → Tm (NodeCtx A B) (stepTy A B P s i)) (s [ supSub ]Tm) (m [ ⟨ ih A B P s ⟩ ]Tm)

      field
        isContrWElim : (A : Ty Γ) (B : Ty (Γ ▹ A)) (P : Ty (Γ ▹ WTy A B))
                       (m : Tm (NodeCtx A B ▹ IHTy A B P) (P [ supSub ]Ty [ p ]Ty))
                     → --------------------------------------------------------------
                       isContr (Σ[ s ∈ Tm (Γ ▹ WTy A B) P ] isWElim A B P m s)

      -- | The eliminator with its β- and η-laws.

      wElim : (A : Ty Γ) (B : Ty (Γ ▹ A)) (P : Ty (Γ ▹ WTy A B))
              (m : Tm (NodeCtx A B ▹ IHTy A B P) (P [ supSub ]Ty [ p ]Ty))
            → ---------------------------------------------------------
              Tm (Γ ▹ WTy A B) P
      wElim A B P m = isContrWElim A B P m .fst .fst

      wElim-β : (A : Ty Γ) (B : Ty (Γ ▹ A)) (P : Ty (Γ ▹ WTy A B))
                (m : Tm (NodeCtx A B ▹ IHTy A B P) (P [ supSub ]Ty [ p ]Ty))
              → ---------------------------------------------------------
                isWElim A B P m (wElim A B P m)
      wElim-β A B P m = isContrWElim A B P m .fst .snd

      wElim-η : (A : Ty Γ) (B : Ty (Γ ▹ A)) (P : Ty (Γ ▹ WTy A B))
                (m : Tm (NodeCtx A B ▹ IHTy A B P) (P [ supSub ]Ty [ p ]Ty))
                (s : Tm (Γ ▹ WTy A B) P)
              → isWElim A B P m s
              → ---------------------------------------------------------
                wElim A B P m ≡ s
      wElim-η A B P m s h = cong fst (isContrWElim A B P m .snd (s , h))
