module ACwF.Bool where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Categories.Category
open import Cubical.Data.Bool
open import Cubical.Data.Sigma
open import ACwF.Base
open import ACwF.Eq

module _ {ℓOb ℓHom ℓTy ℓTm : Level} {C : Category ℓOb ℓHom} (cwf : Algebraic.CwF C ℓTy ℓTm) where

  open Algebraic C
  open CwF cwf

  private level = ℓ-max ℓOb (ℓ-max ℓHom (ℓ-max ℓTy ℓTm))

  private variable
    Θ Δ Γ : Ctx

  record Bool-Structure : Type level where
    field
      BoolTy : Ty Γ
      BoolTyNat : (σ : Δ ⟶ Γ) → BoolTy [ σ ]Ty ≡ BoolTy
      Btrue : {Γ : Ctx} → Tm Γ BoolTy
      Bfalse : {Γ : Ctx} → Tm Γ BoolTy
      BtrueNat : {σ : Δ ⟶ Γ} → PathP (λ i → Tm _ (BoolTyNat σ i)) (Btrue [ σ ]Tm) Btrue
      BfalseNat : {σ : Δ ⟶ Γ} → PathP (λ i → Tm _ (BoolTyNat σ i)) (Bfalse [ σ ]Tm) Bfalse
    BoolCases : ∀ A → Tm (Γ ▹ BoolTy) A → Tm Γ (A [ ⟨ Btrue ⟩ ]Ty) × Tm Γ (A [ ⟨ Bfalse ⟩ ]Ty)
    BoolCases A a = a [ ⟨ Btrue ⟩ ]Tm , a [ ⟨ Bfalse ⟩ ]Tm

    _↑ : (σ : Δ ⟶ Γ) → Δ ▹ BoolTy ⟶ Γ ▹ BoolTy
    σ ↑ = subst (λ X → _ ▹ X ⟶ _ ▹ BoolTy) (BoolTyNat σ) (σ ⁺)
    field
      Bool-elim : ∀ A → Tm Γ (A [ ⟨ Btrue ⟩ ]Ty) × Tm Γ (A [ ⟨ Bfalse ⟩ ]Ty) → Tm (Γ ▹ BoolTy) A
      Bool-elimβ : ∀ A → section (BoolCases {Γ} A) (Bool-elim A)
      -- this signature is a bit weird. The inned `BoolCases (Bool-elim tf)` is,
      -- by β, equal to tf, so this is correct. This version avoids a transport
      -- and some wrapping/unwrapping. To see that it is equivalent to the
      -- version we would have expected, we need a little commutation lemma
      -- `elim (t, f) [σ ↑] ≡ elim (t[σ], f[σ])` (modulo some transports). TODO
      -- actually do this.
      Bool-elimNat : ∀ A (σ : Δ ⟶ Γ) (tf : _) →
          Bool-elim (A [ σ ↑ ]Ty) (BoolCases (A [ σ ↑ ]Ty) (Bool-elim A tf [ σ ↑ ]Tm))
        ≡ Bool-elim A tf [ σ ↑ ]Tm

  record BoolStrong (B : Bool-Structure) : Type level where
    open Bool-Structure B
    field
      Bool-elimη : ∀ A → retract (BoolCases {Γ} A) (Bool-elim A)

  Bool-Eq+Weak→Strong : Eq-Structure cwf → (B : Bool-Structure) → BoolStrong B
  Bool-Eq+Weak→Strong E B .BoolStrong.Bool-elimη A a =
    -- funny reasoning in the model
    EqTmIso A a' a .Iso.fun                   -- equality reflection
      (Bool-elim Eq (true-case , false-case)) -- elimination of bool
    where
      open Bool-Structure B
      open Eq-Structure E
      a' = Bool-elim A (BoolCases A a)
      β = Bool-elimβ A (BoolCases A a)
      Eq = EqTy A a' a
      -- reason on each case, true or false.
      -- each case is refl.
      case : (b : Tm _ BoolTy) → a' [ ⟨ b ⟩ ]Tm ≡ a [ ⟨ b ⟩ ]Tm → Tm _ (Eq [ ⟨ b ⟩ ]Ty)
      case b eq = subst⁻ (Tm _) (EqTyNat _ _ _ ⟨ b ⟩) (EqTmIso _ _ _ .Iso.inv eq)
      true-case : Tm _ (EqTy A a' a [ ⟨ Btrue ⟩ ]Ty)
      true-case = case Btrue (cong fst β)
      false-case : Tm _ (EqTy A a' a [ ⟨ Bfalse ⟩ ]Ty)
      false-case = case Bfalse (cong snd β)
