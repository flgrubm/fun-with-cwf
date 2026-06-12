module ACwF.Instances.IterativePresheaf where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Unit
open import Cubical.Data.Sigma
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Limits.Terminal
open import Cubical.Data.IterativeSets.Base renaming (V⁰ to V ; El⁰ to El)
open import Cubical.Data.IterativeSets.Unit
open import Cubical.Data.IterativeSets.Sigma
open import Utils.IterativePresheaf
open import Utils.VCat
open import ACwF.Base

open Category
open Functor
open NatTrans

module _ {ℓob ℓhom ℓV : Level} (C : Category ℓob ℓhom) where
  open Algebraic (PRESHEAFV C ℓV)
  open CwF

  private
    PSH-TerminalObject : PresheafV C ℓV
    PSH-TerminalObject .F-ob x = unit⁰
    PSH-TerminalObject .F-hom _ x = x
    PSH-TerminalObject .F-id = refl
    PSH-TerminalObject .F-seq _ _ = refl

    PSH-Terminal : Terminal (PRESHEAFV C ℓV)
    PSH-Terminal .fst = PSH-TerminalObject
    PSH-Terminal .snd _ .fst .NatTrans.N-ob _ _ = isContrUnit* .fst
    PSH-Terminal .snd _ .fst .NatTrans.N-hom _ = refl
    PSH-Terminal .snd _ .snd η = makeNatTransPath (funExt (λ I → funExt λ x → isContrUnit* .snd (η .NatTrans.N-ob I x)))

  module _ (Γ : PresheafV C ℓV) (A : Functor (∫V Γ) (VCat ℓV)) where
    preTm : Type (ℓ-max ℓob ℓV)
    preTm = (I : C .Category.ob) (x : El (Γ ⟅ I ⟆)) → El (A ⟅ I , x ⟆)
    isTm : preTm → Type (ℓ-max (ℓ-max ℓob ℓhom) ℓV)
    isTm M = {I J : C .Category.ob} {x : El (Γ ⟅ I ⟆)} {y : El (Γ ⟅ J ⟆)}
        → (u : (∫V Γ) [ (J , y) , (I , x) ])
        → A .F-hom u (M J y) ≡ M I x
    -Tm : Type (ℓ-max (ℓ-max ℓob ℓhom) ℓV)
    -Tm = Σ preTm isTm
    isProp-isTm : (M : preTm) → isProp (isTm M)
    isProp-isTm M p1 p2 i {I} {J} {x} {y} u = isSetEl⁰ (A .F-ob (I , x)) _ _ (p1 u) (p2 u) i
    -isSetTm : isSet -Tm
    -isSetTm = isSetΣSndProp (isSetΠ λ I → isSetΠ λ x → isSetEl⁰ (A .F-ob (I , x))) isProp-isTm


  Psh-CwF : CwF (ℓ-max (ℓ-max ℓob ℓhom) (ℓ-suc ℓV)) (ℓ-max (ℓ-max ℓob ℓhom) ℓV)
  Psh-CwF .⟨⟩ = PSH-Terminal
  Psh-CwF .Ty Γ = Functor (∫V Γ) (VCat ℓV)
  Psh-CwF .isSetTy Γ = isSetFunctor isSetV⁰
  Psh-CwF ._[_]Ty A σ = A ∘F ∫V-hom σ
  Psh-CwF .[id]Ty A =
    A ∘F ∫V-hom (id (PRESHEAFV C ℓV)) ≡⟨ cong (λ F → A ∘F F) ∫V-id ⟩
    A ∘F Id                           ≡⟨ F-lUnit ⟩
    A                                 ∎
  Psh-CwF .[][]Ty A σ' σ =
    A ∘F ∫V-hom ((PRESHEAFV C ℓV ∘ σ) σ') ≡⟨ cong (λ F → A ∘F F) ∫V-seq ⟩
    A ∘F ((∫V-hom σ) ∘F (∫V-hom σ'))      ≡⟨ F-assoc ⟩
    (A ∘F ∫V-hom σ) ∘F ∫V-hom σ'          ∎
  Psh-CwF .Tm Γ A = -Tm Γ A
  Psh-CwF .isSetTm = -isSetTm
  Psh-CwF ._[_]Tm M σ .fst = λ I x → M .fst I (σ .N-ob I x)
  Psh-CwF ._[_]Tm {Γ} {Δ} {A} M σ .snd {I} {J} {x} {y} (f , p) =
    (A ∘F ∫V-hom σ) .F-hom (f , p) (M .fst J (σ .N-ob J y)) ≡⟨ {!!} ⟩
    M .fst I (σ .N-ob I x)                                  ∎
  Psh-CwF .[id]Tm {Γ} {A} M = {!!}
  Psh-CwF .[][]Tm = {!!}
  Psh-CwF ._⋆_ Γ A .F-ob I = Σ⁰ (Γ .F-ob I) (λ x → A .F-ob (I , x))
  Psh-CwF ._⋆_ Γ A .F-hom {I} {J} f (x , y) = (Γ .F-hom f x) ,  A .F-hom (f , refl) y
  Psh-CwF ._⋆_ Γ A .F-id {I} = funExt λ x → ΣPathP ((funExt⁻ (Γ .F-id) (x .fst)) , cong₂ ? ? ?)
  Psh-CwF ._⋆_ Γ A .F-seq = {!!}
  Psh-CwF .p = {!!}
  Psh-CwF .q = {!!}
  Psh-CwF ._⁺ = {!!}
  Psh-CwF .⟨_⟩ = {!!}
  Psh-CwF .⟨⟩∘ = {!!}
  Psh-CwF .p⁺∘⟨q⟩≡id = {!!}
  Psh-CwF .∘⁺ = {!!}
  Psh-CwF .id⁺ = {!!}
  Psh-CwF .p∘⁺ = {!!}
  Psh-CwF .[p][⁺]Ty = {!!}
  Psh-CwF .q[⁺]Tm = {!!}
  Psh-CwF .p∘⟨⟩≡id = {!!}
  Psh-CwF .[p][⟨⟩]Ty = {!!}
  Psh-CwF .q[⟨⟩]Tm = {!!}
