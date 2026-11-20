{-# OPTIONS --lossy-unification #-}
module ACwF.Instances.IterativeSets  where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Functions.FunExtEquiv

open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.Bool

open import Cubical.Categories.Category

open import ACwF.Base
open import ACwF.Sigma
open import ACwF.Pi
open import ACwF.Eq
open import ACwF.Empty
open import ACwF.Unit
open import ACwF.Bool
open import ACwF.W

open import Cubical.Data.IterativeSets.Base renaming (V⁰ to V ; El⁰ to El ; isSetEl⁰ to isSetEl)
open import Utils.VCat
open import Cubical.Data.IterativeSets.Sigma
open import Cubical.Data.IterativeSets.Pi
open import Cubical.Data.IterativeSets.Unit
open import Cubical.Data.IterativeSets.Identity
open import Cubical.Data.IterativeSets.Empty
open import Cubical.Data.IterativeSets.Bool
open import Cubical.Data.IterativeSets.W
open import Cubical.Data.W.W using (sup-W)

open Category

module _ {ℓ : Level} where

  open Algebraic
  open CwF
  open Iso

  VCwF : CwF (VCat _) (ℓ-suc ℓ) ℓ
  VCwF .⟨⟩                = unit⁰ , λ _ → (λ _ → lift tt) , λ _ _ _ → lift tt
  VCwF .Ty Γ              = El Γ → V {ℓ}
  VCwF .isSetTy Γ         = isSet→ isSetV⁰
  VCwF ._[_]Ty A σ x      = A (σ x)
  VCwF .[id]Ty _          = refl
  VCwF .[][]Ty _ _ _      = refl
  VCwF .Tm Γ A            = (x : El Γ) → El (A x)
  VCwF .isSetTm Γ A       = isSetΠ (λ _ → isSetEl _)
  VCwF ._[_]Tm a σ x      = a (σ x)
  VCwF .[id]Tm _          = refl
  VCwF .[][]Tm _ _ _      = refl
  VCwF ._▹_               = Σ⁰
  VCwF .p                 = fst
  VCwF .q                 = snd
  VCwF ._⁺ σ (x , _) .fst = σ x
  VCwF ._⁺ _ (_ , y) .snd = y
  VCwF .⟨_⟩ _ x .fst      = x
  VCwF .⟨_⟩ a x .snd      = a x
  VCwF .⟨⟩∘ a σ           = refl
  VCwF .p⁺∘⟨q⟩≡id         = refl
  VCwF .∘⁺ σ' σ           = refl
  VCwF .id⁺               = refl
  VCwF .p∘⁺ σ             = refl
  VCwF .[p][⁺]Ty B σ      = refl
  VCwF .q[⁺]Tm σ          = refl
  VCwF .p∘⟨⟩≡id a         = refl
  VCwF .[p][⟨⟩]Ty B a     = refl
  VCwF .q[⟨⟩]Tm a         = refl

module _ {ℓHom : Level} where

  open Algebraic
  open CwF {ℓHom = ℓHom} VCwF

  open Σ-Structure

  V-Σ-Structure : Σ-Structure (VCat _) VCwF
  V-Σ-Structure .ΣTy A B x              = Σ⁰ (A x) (λ y → B (x , y))
  V-Σ-Structure .ΣTyNat A B σ           = refl
  V-Σ-Structure .ΣTmIso A B             = Σ-Π-Iso
  V-Σ-Structure .coerce A B a σ         = refl
  V-Σ-Structure .ΣTmIsoInvNat _ _ _ b σ =
    funExt λ x → ΣPathP (refl , sym (funExt⁻ (substRefl {B = Tm _} _) _))

module _ {ℓHom : Level} where

  open Algebraic
  open CwF {ℓHom = ℓHom} VCwF

  open Π-Structure

  V-Π-Structure : Π-Structure {ℓHom = ℓHom} (VCat _) VCwF
  V-Π-Structure .ΠTy {Γ = Γ} A B x    = Π⁰ (A x) λ y → B (x , y)

  V-Π-Structure .ΠTyNat _ _ _         = refl
  V-Π-Structure .ΠTmIso _ _           = invIso curryIso
  V-Π-Structure .ΠTmIsoInvNat _ _ _ _ = refl

module _ {ℓHom : Level} where

  open Algebraic
  open CwF {ℓHom = ℓHom} VCwF

  open Eq-Structure

  V-Eq-Structure : Eq-Structure {ℓHom = ℓHom} VCwF
  V-Eq-Structure .EqTy A a b x            = Id⁰ (A x) (a x) (b x)
  V-Eq-Structure .EqTyNat _ _ _ _         = refl
  V-Eq-Structure .EqTmIso _ _ _           = funExtIso
  V-Eq-Structure .EqTmIsoInvNat _ _ _ _ _ = refl

  V-⊥-Structure : ⊥-Structure {ℓHom = ℓHom} VCwF
  V-⊥-Structure .⊥-Structure.⊥Ty _         = empty⁰
  V-⊥-Structure .⊥-Structure.⊥TyNat _      = refl
  V-⊥-Structure .⊥-Structure.⊥-elim A (_ , lift ())
  V-⊥-Structure .⊥-Structure.⊥-elimNat A σ = funExt λ { (_ , lift ()) }

  V-Unit-Structure : Unit-Structure {ℓHom = ℓHom} VCwF
  V-Unit-Structure .Unit-Structure.UnitTy _               = unit⁰
  V-Unit-Structure .Unit-Structure.UnitTyNat _            = refl
  V-Unit-Structure .Unit-Structure.UnitTmIso .Iso.fun _   = tt
  V-Unit-Structure .Unit-Structure.UnitTmIso .Iso.inv _ _ = tt*
  V-Unit-Structure .Unit-Structure.UnitTmIso .Iso.sec tt  = refl
  V-Unit-Structure .Unit-Structure.UnitTmIso .Iso.ret _   = funExt (λ _ → refl)
  V-Unit-Structure .Unit-Structure.UnitTmIsoInvNat t σ    = refl

  private
    V-Bool-elim : ∀ {Γ} A
      → Tm Γ (A [ ⟨ (λ _ → true*) ⟩ ]Ty) × Tm Γ (A [ ⟨ (λ _ → false*) ⟩ ]Ty)
      → Tm (Γ ▹ (λ _ → bool⁰)) A
    V-Bool-elim _ (_ , af) (x , lift false) = af x
    V-Bool-elim _ (at , _) (x , lift true)  = at x

    V-Bool-elimβ : ∀ {Γ} A tf
      → (V-Bool-elim {Γ} A tf [ ⟨ (λ _ → true*) ⟩ ]Tm , V-Bool-elim A tf [ ⟨ (λ _ → false*) ⟩ ]Tm) ≡ tf
    V-Bool-elimβ _ _ = refl

    V-Bool-elimNat : ∀ {Δ Γ} A (σ : El Δ → El Γ) tf
      → let σ↑ = subst (λ X → El (Σ⁰ Δ X) → El (Σ⁰ Γ (λ _ → bool⁰))) refl (σ ⁺) in
          V-Bool-elim (A [ σ↑ ]Ty)
            ( V-Bool-elim A tf [ σ↑ ]Tm [ ⟨ (λ _ → true*) ⟩ ]Tm
            , V-Bool-elim A tf [ σ↑ ]Tm [ ⟨ (λ _ → false*) ⟩ ]Tm)
        ≡ V-Bool-elim A tf [ σ↑ ]Tm
    V-Bool-elimNat _ _ _ = funExt λ { (_ , lift false) → refl
                                    ; (_ , lift true)  → refl }

  V-Bool-Structure : Bool-Structure {ℓHom = ℓHom} VCwF
  V-Bool-Structure .Bool-Structure.BoolTy _       = bool⁰
  V-Bool-Structure .Bool-Structure.BoolTyNat _    = refl
  V-Bool-Structure .Bool-Structure.Btrue _        = true*
  V-Bool-Structure .Bool-Structure.Bfalse _       = false*
  V-Bool-Structure .Bool-Structure.BtrueNat       = refl
  V-Bool-Structure .Bool-Structure.BfalseNat      = refl
  V-Bool-Structure .Bool-Structure.Bool-elim      = V-Bool-elim
  V-Bool-Structure .Bool-Structure.Bool-elimβ     = V-Bool-elimβ
  V-Bool-Structure .Bool-Structure.Bool-elimNat   = V-Bool-elimNat

  -- | W-types.  `El (W⁰ A B)` *is* `W`, so the constructor is `sup-W`, the
  -- subtree at a branch is application of the subtree function, and the
  -- eliminator is structural recursion on the tree.  The paths `SubtreesTyNat`
  -- and `branchTy`, along which the record states `supSubNat` and
  -- `q[branchSub]`, are composites of `refl`s here: these two laws hold over
  -- `refl` and are moved onto those paths by `reindex⟶` / `reindex`.
  module _ where
    open Π-Structure (V-Π-Structure {ℓHom = ℓHom})

    WTyV : {Γ : V} (A : Ty Γ) (B : Ty (Γ ▹ A))
         → -------------------------------------
           Ty Γ
    WTyV A B x = W⁰ (A x) (λ a → B (x , a))

    -- the type of subtree functions of a node whose label is the variable of `Γ ▹ A`
    SubtreesTyV : {Γ : V} (A : Ty Γ) (B : Ty (Γ ▹ A))
                → -------------------------------------
             Ty (Γ ▹ A)
    SubtreesTyV A B = ΠTy B (WTyV A B [ p ]Ty [ p ]Ty)

    -- a node: a label with its subtree function
    NodeV : {Γ : V} (A : Ty Γ) (B : Ty (Γ ▹ A))
          → -------------------------------------
            V
    NodeV A B = _ ▹ A ▹ SubtreesTyV A B

    module _ {Γ : V} {A : Ty Γ} {B : Ty (Γ ▹ A)} where

      supSubV : El (NodeV A B) → El (Γ ▹ WTyV A B)
      supSubV ((x , a) , f) = x , sup-W a f

      branchSubV : El (NodeV A B ▹ B [ p ]Ty) → El (Γ ▹ WTyV A B)
      branchSubV (((x , _) , f) , b) = x , f b

      -- the type of the induction hypotheses at a node
      IHTyV : (P : Ty (Γ ▹ WTyV A B))
            → --------------------------
              Ty (NodeV A B)
      IHTyV P = ΠTy (B [ p ]Ty) (P [ branchSubV ]Ty)

      -- the induction hypotheses provided by a term of the motive
      ihV : {P : Ty (Γ ▹ WTyV A B)}
          → Tm (Γ ▹ WTyV A B) P
          → --------------------------
            Tm (NodeV A B) (IHTyV P)
      ihV s = ΠTmIso _ _ .Iso.inv (s [ branchSubV ]Tm)

      -- the subtree at a branch is the subtree function applied, over `refl`
      q[branchSubV] : {f' : Tm (NodeV A B) (ΠTy (B [ p {A = SubtreesTyV A B} ]Ty)
                                                (WTyV A B [ p ]Ty [ p {A = B} ]Ty [ p {A = SubtreesTyV A B} ⁺ ]Ty))}
                    → q {A = SubtreesTyV A B} ≡ f'
                    → ------------------------------------------------------------
                      q [ branchSubV ]Tm ≡ ΠTmIso _ _ .Iso.fun f'
      q[branchSubV] e = cong (ΠTmIso _ _ .Iso.fun) e

      module _ (P : Ty (Γ ▹ WTyV A B)) (m : Tm (NodeV A B ▹ IHTyV P) (P [ supSubV ]Ty [ p ]Ty)) where

        -- the eliminator, by structural recursion on the tree
        elimV : (x : El Γ) (w : El (WTyV A B x))
              → ----------------------------------
                El (P (x , w))
        elimV x (sup-W a f) = m (((x , a) , f) , λ b → elimV x (f b))

        -- `s` is `m` at every node: the record's `isWElim`, whose path `stepTy` is `refl` here
        isWElimV : Tm (Γ ▹ WTyV A B) P → Type ℓHom
        isWElimV s = s [ supSubV ]Tm ≡ m [ ⟨ ihV s ⟩ ]Tm

        -- any eliminator is `elimV`, by induction on the tree
        elimV-η : (s : Tm (Γ ▹ WTyV A B) P) → isWElimV s
                → (x : El Γ) (w : El (WTyV A B x))
                → ----------------------------------
                  elimV x w ≡ s (x , w)
        elimV-η s h x (sup-W a f) =
            cong (λ ih → m (((x , a) , f) , ih)) (funExt λ b → elimV-η s h x (f b))
          ∙ sym (funExt⁻ h ((x , a) , f))

        -- `elimV` is the unique eliminator; β holds by definition
        isContrWElimV : isContr (Σ[ s ∈ Tm (Γ ▹ WTyV A B) P ] isWElimV s)
        isContrWElimV .fst = (λ (x , w) → elimV x w) , refl
        isContrWElimV .snd (s , h) =
          Σ≡Prop (λ _ → isSetTm _ _ _ _) (funExt λ (x , w) → elimV-η s h x w)

    open W-Structure

    V-W-Structure : W-Structure VCwF V-Π-Structure
    V-W-Structure .WTy                  = WTyV
    V-W-Structure .WTyNat _ _ _         = refl
    V-W-Structure .wkW σ                = σ ⁺
    V-W-Structure .wkW≡ _               = refl
    V-W-Structure .supSub               = supSubV
    V-W-Structure .p∘supSub             = refl
    V-W-Structure .supSubNat _          = reindex⟶ {e = refl} refl
    V-W-Structure .branchSub            = branchSubV
    V-W-Structure .p∘branchSub          = refl
    V-W-Structure .q[branchSub] e       = reindex {e = refl} (q[branchSubV] e)
    V-W-Structure .isContrWElim _ _ P m = isContrWElimV P m
