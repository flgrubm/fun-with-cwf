module ACwF.Universe where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma

open import Cubical.Categories.Category

open import ACwF.Base
open import ACwF.Pi
open import ACwF.Sigma

module _ {ℓOb ℓHom ℓTy ℓTm : Level} {C : Category ℓOb ℓHom} (cwf : Algebraic.CwF C ℓTy ℓTm) where

  open Algebraic C
  open CwF cwf

  private variable
    Δ Γ : Ctx

  -- | A universe (Angiuli–Gratzer, Structure 6.4.17, first two points): a type
  -- `UTy` of codes, stable under substitution, together with a *family*
  -- `ElTy` over it, stable under the weakening of a substitution.  A code
  -- `c : Tm Γ UTy` decodes to the instance `El c = ElTy [ ⟨ c ⟩ ]Ty`.
  --
  -- Taking the family rather than a decoding function on terms as primitive
  -- keeps its naturality (`ElTyNat`) a `PathP` over the context `Δ ▹ UTy`
  -- moved along `UTyNat`, with no transport in its type.  Closure under type
  -- formers is extra structure: `Univ-Π-Structure`, `Univ-Σ-Structure`.
  record Univ-Structure : Type (ℓ-max ℓOb (ℓ-max ℓHom (ℓ-max ℓTy ℓTm))) where
    field
      UTy : Ty Γ

      UTyNat : (σ : Δ ⟶ Γ)
             → --------------------
               UTy [ σ ]Ty ≡ UTy

      ElTy : Ty (Γ ▹ UTy)

      ElTyNat : (σ : Δ ⟶ Γ)
              → -------------------------------------------------------------------
                PathP (λ i → Ty (Δ ▹ UTyNat σ i)) (ElTy [ σ ⁺ ]Ty) (ElTy {Δ})

    El : Tm Γ UTy → Ty Γ
    El c = ElTy [ ⟨ c ⟩ ]Ty

    -- `c [ σ ]U≈ c'`: `c'` is `c [ σ ]Tm`, over `UTyNat σ`.  Stating
    -- naturality through this relation avoids transporting `c [ σ ]Tm` into
    -- `Tm Δ UTy`.
    _[_]U≈_ : Tm Γ UTy → (σ : Δ ⟶ Γ) → Tm Δ UTy → Type ℓTm
    c [ σ ]U≈ c' = PathP (λ i → Tm _ (UTyNat σ i)) (c [ σ ]Tm) c'

    -- Decoding commutes with substitution.  This follows from `ElTyNat`
    -- (`ElNat-default`), but is a field so that a model can choose the path
    -- over which `_[_]Fam≈_` is stated, e.g. the decoding applied pointwise
    -- to the path between the codes.
    field
      ElNat : (σ : Δ ⟶ Γ) {c : Tm Γ UTy} {c' : Tm Δ UTy}
            → c [ σ ]U≈ c'
            → ---------------------------
              El c [ σ ]Ty ≡ El c'

    -- `d [ σ , e ]Fam≈ d'`: the family of codes `d'` is `d [ σ ⁺ ]Tm`.  The
    -- two live over different contexts, `Δ ▹ El c'` and `Δ ▹ El c [ σ ]Ty`,
    -- so they are related through an intermediate `d₀`: first along
    -- `UTyNat (σ ⁺)`, then along the context `Δ ▹ ElNat σ e i`.  Each step is
    -- a `PathP` over a single path.
    _[_]Fam≈_ : {c : Tm Γ UTy} {c' : Tm Δ UTy} (d : Tm (Γ ▹ El c) UTy)
              → (σe : Σ[ σ ∈ Δ ⟶ Γ ] c [ σ ]U≈ c')
              → Tm (Δ ▹ El c') UTy → Type ℓTm
    _[_]Fam≈_ {Δ = Δ} {c = c} d (σ , e) d' =
      Σ[ d₀ ∈ Tm (Δ ▹ El c [ σ ]Ty) UTy ]
          (d [ σ ⁺ ]U≈ d₀)
        × PathP (λ i → Tm (Δ ▹ ElNat σ e i) UTy) d₀ d'

  -- | `ElNat` follows from the other fields: rewrite `⟨ c ⟩ ∘ σ` as
  -- `σ ⁺ ∘ ⟨ c [ σ ]Tm ⟩` (`⟨⟩∘`), then move along `ElTyNat σ` and the path
  -- between the codes at once.  The other fields are parameters, so that a
  -- model can use this to fill the field `ElNat`.
  module _ (UTy : {Γ : Ctx} → Ty Γ)
           (UTyNat : {Δ Γ : Ctx} (σ : Δ ⟶ Γ) → UTy [ σ ]Ty ≡ UTy)
           (ElTy : {Γ : Ctx} → Ty (Γ ▹ UTy))
           (ElTyNat : {Δ Γ : Ctx} (σ : Δ ⟶ Γ)
                    → PathP (λ i → Ty (Δ ▹ UTyNat σ i)) (ElTy [ σ ⁺ ]Ty) (ElTy {Δ}))
           where

    ElNat-default : (σ : Δ ⟶ Γ) {c : Tm Γ UTy} {c' : Tm Δ UTy}
                  → PathP (λ i → Tm Δ (UTyNat σ i)) (c [ σ ]Tm) c'
                  → -----------------------------------------------------
                    ElTy [ ⟨ c ⟩ ]Ty [ σ ]Ty ≡ ElTy [ ⟨ c' ⟩ ]Ty
    ElNat-default σ {c} e =
        sym ([][]Ty ElTy σ ⟨ c ⟩)
      ∙ cong (ElTy [_]Ty) (⟨⟩∘ c σ)
      ∙ [][]Ty ElTy ⟨ c [ σ ]Tm ⟩ (σ ⁺)
      ∙ λ i → ElTyNat σ i [ ⟨ e i ⟩ ]Ty

  -- | Closure of a universe under Π and Σ (Angiuli–Gratzer, Structure 6.4.17,
  -- last three points, for these two connectives): a code for the Π (Σ) of a
  -- code and a family of codes over its decoding, which decodes to the Π (Σ)
  -- of the decodings and is stable under substitution.
  module _ (U : Univ-Structure) where
    open Univ-Structure U

    module _ (Πs : Π-Structure C cwf) where
      open Π-Structure Πs

      record Univ-Π-Structure : Type (ℓ-max ℓOb (ℓ-max ℓHom (ℓ-max ℓTy ℓTm))) where
        field
          piU : (c : Tm Γ UTy) (d : Tm (Γ ▹ El c) UTy)
              → ----------------------------------------
                Tm Γ UTy

          El-piU : (c : Tm Γ UTy) (d : Tm (Γ ▹ El c) UTy)
                 → ------------------------------------------
                   El (piU c d) ≡ ΠTy (El c) (El d)

          piUNat : (σ : Δ ⟶ Γ) {c : Tm Γ UTy} {c' : Tm Δ UTy} (e : c [ σ ]U≈ c')
                   {d : Tm (Γ ▹ El c) UTy} {d' : Tm (Δ ▹ El c') UTy}
                 → d [ σ , e ]Fam≈ d'
                 → -----------------------------------------
                   piU c d [ σ ]U≈ piU c' d'

    module _ (Σs : Σ-Structure C cwf) where
      open Σ-Structure Σs

      record Univ-Σ-Structure : Type (ℓ-max ℓOb (ℓ-max ℓHom (ℓ-max ℓTy ℓTm))) where
        field
          sigU : (c : Tm Γ UTy) (d : Tm (Γ ▹ El c) UTy)
               → ----------------------------------------
                 Tm Γ UTy

          El-sigU : (c : Tm Γ UTy) (d : Tm (Γ ▹ El c) UTy)
                  → ------------------------------------------
                    El (sigU c d) ≡ ΣTy (El c) (El d)

          sigUNat : (σ : Δ ⟶ Γ) {c : Tm Γ UTy} {c' : Tm Δ UTy} (e : c [ σ ]U≈ c')
                    {d : Tm (Γ ▹ El c) UTy} {d' : Tm (Δ ▹ El c') UTy}
                  → d [ σ , e ]Fam≈ d'
                  → -----------------------------------------
                    sigU c d [ σ ]U≈ sigU c' d'
