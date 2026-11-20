module ACwF.Quotient where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism using (Iso ; isoToIsEquiv)
open import Cubical.Data.Sigma

open import Cubical.Categories.Category

open import ACwF.Base

-- | A map `f` into a subtype `Σ M Resp` is an equivalence if its first
-- component has an inverse `elim` that needs only a weaker condition `Resp'`.
-- The models prove `isEquivQuotCases` this way: `f` is `QuotCases`, `Resp'`
-- is the model's own statement that a term respects the relation, and `β`,
-- `η` are the laws of its eliminator.
isEquivCases : {ℓT ℓM ℓR ℓR' : Level} {T : Type ℓT} {M : Type ℓM}
               {Resp : M → Type ℓR} {Resp' : M → Type ℓR'} {f : T → Σ M Resp}
               (elim : (m : M) → Resp' m → T)
             → ((m : M) (r : Resp' m) → f (elim m r) .fst ≡ m)
             → ((t : T) (r : Resp' (f t .fst)) → elim (f t .fst) r ≡ t)
             → ((m : M) → isProp (Resp m))
             → ((m : M) → Resp m → Resp' m)
             → --------------------------------------------------------
               isEquiv f
isEquivCases {f = f} elim β η isPropResp weaken = isoToIsEquiv casesIso
  where
    casesIso : Iso _ _
    casesIso .Iso.fun         = f
    casesIso .Iso.inv (m , r) = elim m (weaken m r)
    casesIso .Iso.sec (m , r) = Σ≡Prop isPropResp (β m (weaken m r))
    casesIso .Iso.ret t       = η t (weaken _ (f t .snd))

module _ {ℓOb ℓHom ℓTy ℓTm : Level} {C : Category ℓOb ℓHom} (cwf : Algebraic.CwF C ℓTy ℓTm) where

  open Algebraic C
  open CwF cwf
  open Category C using (_∘_)

  private variable
    Δ Γ : Ctx

  -- | Quotient types.  A relation on `A : Ty Γ` is a type `R` over two
  -- variables of type `A`; `QTy A R` is the quotient.  Its terms are
  -- introduced as classes (`classTm`, and generically `classSub`), related
  -- terms have equal classes (`classSubSound`), and a term over a variable of
  -- the quotient is the same as a term over a variable of `A` that respects
  -- `R` (`isEquivQuotCases`: dependent elimination with its β- and η-laws,
  -- in the style of Angiuli–Gratzer, Structure 6.3.2 for booleans).
  --
  -- The naturality of the eliminator is not a field: it is the inverse of
  -- `QuotCases`, which is precomposition with `classSub` and hence natural.
  record Quot-Structure : Type (ℓ-max ℓOb (ℓ-max ℓHom (ℓ-max ℓTy ℓTm))) where
    field
      QTy : (A : Ty Γ) (R : Ty (Γ ▹ A ▹ A [ p ]Ty))
          → -----------------------------------------
            Ty Γ

      -- The weakening of σ past two variables of type `A`.  It is `(σ ⁺) ⁺`
      -- moved along `[p][⁺]Ty` (that is `⁺²≡`), and so derivable, but a field
      -- (Fording) so that a model can give one that computes; the relation of
      -- a substituted quotient is then `R [ σ ⁺² ]Ty`, without transport.
      _⁺² : {A : Ty Γ} (σ : Δ ⟶ Γ)
          → --------------------------------------------------------
            Δ ▹ A [ σ ]Ty ▹ A [ σ ]Ty [ p ]Ty ⟶ Γ ▹ A ▹ A [ p ]Ty

      ⁺²≡ : {A : Ty Γ} (σ : Δ ⟶ Γ)
          → --------------------------------------------------------------------
            PathP (λ i → Δ ▹ A [ σ ]Ty ▹ [p][⁺]Ty A σ i ⟶ Γ ▹ A ▹ A [ p ]Ty)
                  ((σ ⁺) ⁺) (σ ⁺²)

      QTyNat : (A : Ty Γ) (R : Ty (Γ ▹ A ▹ A [ p ]Ty)) (σ : Δ ⟶ Γ)
             → ----------------------------------------------------
               QTy A R [ σ ]Ty ≡ QTy (A [ σ ]Ty) (R [ σ ⁺² ]Ty)

      -- | Introduction: the class of a term.
      classTm : {A : Ty Γ} {R : Ty (Γ ▹ A ▹ A [ p ]Ty)}
              → Tm Γ A
              → ----------------
                Tm Γ (QTy A R)

      classTmNat : {A : Ty Γ} {R : Ty (Γ ▹ A ▹ A [ p ]Ty)} (a : Tm Γ A) (σ : Δ ⟶ Γ)
                 → -----------------------------------------------------------------
                   PathP (λ i → Tm Δ (QTyNat A R σ i))
                         (classTm a [ σ ]Tm) (classTm (a [ σ ]Tm))

      -- The class of the last variable as a substitution,
      -- `(γ , a) ↦ (γ , [ a ])`.  It is determined by `p∘classSub` and
      -- `q[classSub]`, but is a field (Fording) so that a model can supply one
      -- that computes.
      classSub : {A : Ty Γ} {R : Ty (Γ ▹ A ▹ A [ p ]Ty)}
               → -------------------------
                 Γ ▹ A ⟶ Γ ▹ QTy A R

      p∘classSub : {A : Ty Γ} {R : Ty (Γ ▹ A ▹ A [ p ]Ty)}
                 → -----------------------------------
                   p ∘ classSub {A = A} {R = R} ≡ p

    -- the type of `q [ classSub ]Tm` is that of `classTm q`; `q[classSub]` lies
    -- over this path
    classSubTy : (A : Ty Γ) (R : Ty (Γ ▹ A ▹ A [ p ]Ty))
               → ----------------------------------------------------------------
                 QTy A R [ p ]Ty [ classSub {A = A} {R = R} ]Ty ≡ QTy (A [ p ]Ty) (R [ p ⁺² ]Ty)
    classSubTy A R =
        sym ([][]Ty (QTy A R) classSub p)
      ∙ cong (QTy A R [_]Ty) p∘classSub
      ∙ QTyNat A R p

    -- | The context of two variables of type `A` related by `R`, and its
    -- projections to the first and to the second variable.
    RelCtx : (A : Ty Γ) (R : Ty (Γ ▹ A ▹ A [ p ]Ty)) → Ctx
    RelCtx A R = _ ▹ A ▹ A [ p ]Ty ▹ R

    fstVar : (A : Ty Γ) (R : Ty (Γ ▹ A ▹ A [ p ]Ty)) → RelCtx A R ⟶ Γ ▹ A
    fstVar A R = p {A = A [ p ]Ty} ∘ p {A = R}

    sndVar : (A : Ty Γ) (R : Ty (Γ ▹ A ▹ A [ p ]Ty)) → RelCtx A R ⟶ Γ ▹ A
    sndVar A R = (p {A = A}) ⁺ ∘ p {A = R}

    field
      -- the last component of `classSub` is the class of the variable
      q[classSub] : {A : Ty Γ} {R : Ty (Γ ▹ A ▹ A [ p ]Ty)}
                  → ------------------------------------------------------------------
                    PathP (λ i → Tm (Γ ▹ A) (classSubTy A R i)) (q [ classSub ]Tm) (classTm q)

      -- | Related elements have equal classes.
      classSubSound : {A : Ty Γ} {R : Ty (Γ ▹ A ▹ A [ p ]Ty)}
                    → ---------------------------------------------------------
                      classSub {A = A} {R = R} ∘ fstVar A R ≡ classSub ∘ sndVar A R

    -- | Elimination.

    -- `P` at the class of the first related variable is `P` at the class of
    -- the second, by `classSubSound`
    respectsTy : (A : Ty Γ) (R : Ty (Γ ▹ A ▹ A [ p ]Ty)) (P : Ty (Γ ▹ QTy A R))
               → ---------------------------------------------------------------------
                 P [ classSub {A = A} {R = R} ]Ty [ fstVar A R ]Ty ≡ P [ classSub ]Ty [ sndVar A R ]Ty
    respectsTy A R P =
        sym ([][]Ty P (fstVar A R) classSub)
      ∙ cong (P [_]Ty) classSubSound
      ∙ [][]Ty P (sndVar A R) classSub

    -- `m` respects `R`: its instances at two related variables agree
    respects : (A : Ty Γ) (R : Ty (Γ ▹ A ▹ A [ p ]Ty)) (P : Ty (Γ ▹ QTy A R))
             → Tm (Γ ▹ A) (P [ classSub {A = A} {R = R} ]Ty)
             → -----------------------------
               Type ℓTm
    respects A R P m =
      PathP (λ i → Tm (RelCtx A R) (respectsTy A R P i)) (m [ fstVar A R ]Tm) (m [ sndVar A R ]Tm)

    -- the cases of a term over a variable of the quotient: its instance at
    -- the class of a variable of `A`, which respects `R` because of
    -- `classSubSound`
    QuotCases : (A : Ty Γ) (R : Ty (Γ ▹ A ▹ A [ p ]Ty)) (P : Ty (Γ ▹ QTy A R))
              → Tm (Γ ▹ QTy A R) P
              → ------------------------------------------------
                Σ[ m ∈ Tm (Γ ▹ A) (P [ classSub {A = A} {R = R} ]Ty) ] respects A R P m
    QuotCases A R P t =
        t [ classSub ]Tm
      ,     symP ([][]Tm t (fstVar A R) classSub)
        ∙Tm (λ i → t [ classSubSound i ]Tm)
        ∙Tm [][]Tm t (sndVar A R) classSub

    field
      isEquivQuotCases : (A : Ty Γ) (R : Ty (Γ ▹ A ▹ A [ p ]Ty)) (P : Ty (Γ ▹ QTy A R))
                       → -----------------------------------------------------------
                         isEquiv (QuotCases A R P)

    -- | The eliminator with its β- and η-laws.

    quotElim : (A : Ty Γ) (R : Ty (Γ ▹ A ▹ A [ p ]Ty)) (P : Ty (Γ ▹ QTy A R))
               (m : Tm (Γ ▹ A) (P [ classSub {A = A} {R = R} ]Ty))
             → respects A R P m
             → --------------------
               Tm (Γ ▹ QTy A R) P
    quotElim A R P m r = invEq (_ , isEquivQuotCases A R P) (m , r)

    quotElim-β : (A : Ty Γ) (R : Ty (Γ ▹ A ▹ A [ p ]Ty)) (P : Ty (Γ ▹ QTy A R))
                 (m : Tm (Γ ▹ A) (P [ classSub {A = A} {R = R} ]Ty)) (r : respects A R P m)
               → ------------------------------------------------------------
                 quotElim A R P m r [ classSub {A = A} {R = R} ]Tm ≡ m
    quotElim-β A R P m r = cong fst (secEq (_ , isEquivQuotCases A R P) (m , r))

    quotElim-η : (A : Ty Γ) (R : Ty (Γ ▹ A ▹ A [ p ]Ty)) (P : Ty (Γ ▹ QTy A R))
                 (t : Tm (Γ ▹ QTy A R) P)
               → -------------------------------------------------------------
                 quotElim A R P (t [ classSub {A = A} {R = R} ]Tm) (QuotCases A R P t .snd) ≡ t
    quotElim-η A R P t = retEq (_ , isEquivQuotCases A R P) t
