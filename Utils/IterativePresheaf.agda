module Utils.IterativePresheaf where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Instances.Functors
open import Cubical.Data.IterativeSets.Base renaming (V⁰ to V ; El⁰ to El ; isSetEl⁰ to isSetEl)
open import Utils.VCat

open Category
open Functor

module _ {ℓob ℓhom : Level} (C : Category ℓob ℓhom) (ℓV : Level) where
  PresheafV = Functor (C ^op) (VCat ℓV)
  PRESHEAFV = FUNCTOR (C ^op) (VCat ℓV)

module _ {ℓob ℓhom : Level} {C : Category ℓob ℓhom} {ℓV : Level} where
  module Base (F : PresheafV C ℓV) where

    private
      ∫ob : Type (ℓ-max ℓob ℓV)
      ∫ob = Σ[ c ∈ C .ob ] (El (F ⟅ c ⟆))

    private
      ∫Hom[_,_] : ∫ob → ∫ob → Type (ℓ-max ℓhom ℓV)
      ∫Hom[_,_] (c , x) (d , y) = Σ[ f ∈ C [ d , c ] ] (F ⟪ f ⟫) x ≡ y

      _∫⋆_ : {x y z : ∫ob} → ∫Hom[ x , y ] → ∫Hom[ y , z ] → ∫Hom[ x , z ]
      _∫⋆_ f g .fst = (g .fst) ⋆⟨ C ⟩ (f .fst)
      _∫⋆_ {x} {y} {z} (f , p) (g , q) .snd =
        funExt⁻ (F-seq F f g) (x .snd) ∙ cong (F .F-hom g) p ∙ q

      ∫Hom≡ : {x y : ∫ob} {f g : ∫Hom[ x , y ]} → f .fst ≡ g .fst → f ≡ g
      ∫Hom≡ {x} {y} {f = (f , p)} {g = (g , q)} eq =
        ΣPathP (eq , (isProp→PathP (λ i → isSetEl (F-ob F (y .fst)) _ _) p q))
      ∫HomPathP : ∀ {x} {x'} {y} {y'} (f : ∫Hom[ x , y ]) (g : ∫Hom[ x' , y' ])
        → (x≡x' : x ≡ x') → (y≡y' : y ≡ y')
        → PathP (λ i → C [ y≡y' i .fst , x≡x' i .fst ]) (f .fst) (g .fst)
        → PathP (λ i → ∫Hom[ x≡x' i , y≡y' i ]) f g
      ∫HomPathP {y = y} f g x≡x' y≡y' path =
        ΣPathP (path , isProp→PathP (λ j → isSetEl (F .F-ob (y≡y' j .fst)) _ _) (f .snd) (g .snd))

    ∫V : Category _ _
    ∫V .ob = ∫ob
    ∫V .Hom[_,_] = ∫Hom[_,_]
    ∫V .id .fst = C .id
    ∫V .id {x} .snd = funExt⁻ (F-id F) (x .snd)
    ∫V ._⋆_ = _∫⋆_
    ∫V .⋆IdL {x} {y} f = ∫Hom≡ (C .⋆IdR (f .fst))
    ∫V .⋆IdR {x} {y} f = ∫Hom≡ (C .⋆IdL (f .fst))
    ∫V .⋆Assoc f g h =
      ∫Hom≡ ((C ^op) .⋆Assoc (f .fst) (g .fst) (h .fst))
    ∫V .isSetHom {a} {b} =
      isSetΣSndProp (C .isSetHom) λ f → isSetEl (F-ob F (b .fst)) _ _

    ∫V-Hom-PathP : ∀ {x} {x'} {y} {y'} (f : ∫V [ x , y ]) (g : ∫V [ x' , y' ])
      → (x≡x' : x ≡ x') → (y≡y' : y ≡ y')
      → PathP (λ i → C [ y≡y' i .fst , x≡x' i .fst ]) (f .fst) (g .fst)
      → PathP (λ i → ∫V [ x≡x' i , y≡y' i ]) f g
    ∫V-Hom-PathP = ∫HomPathP

  open Base public

  module Properties where
    ∫V-hom : {Γ Δ : PresheafV C ℓV} → NatTrans Δ Γ → Functor (∫V Δ) (∫V Γ)
    ∫V-hom {Γ} {Δ} η .F-ob (I , x) = I , η . NatTrans.N-ob I x
    ∫V-hom {Γ} {Δ} η .F-hom {I , x} {J , y} (f , p) = f , proof
      where
        proof : (Γ ⟪ f ⟫) (NatTrans.N-ob η I x) ≡ NatTrans.N-ob η J y
        proof =
              (Γ ⟪ f ⟫) (NatTrans.N-ob η I x)
            ≡⟨ funExt⁻ (sym (η .NatTrans.N-hom f)) x ⟩
              η .NatTrans.N-ob J (Δ .F-hom f x)
            ≡⟨ cong _ p ⟩
              η .NatTrans.N-ob J y
            ∎
    ∫V-hom {Γ} {Δ} η .F-id {c , _} = ΣPathP ( refl , isSetEl (Γ ⟅ c ⟆) _ _ _ _)
    ∫V-hom {Γ} {Δ} η .F-seq {z = c , _} f g = ΣPathP ( refl , isSetEl (Γ ⟅ c ⟆) _ _ _ _)

    ∫V-id : {Γ : PresheafV C ℓV} → ∫V-hom (idTrans Γ) ≡ Id
    ∫V-id {Γ} = Functor≡
      (λ _ → refl)
      (λ {_} {c'} (f , p) → ΣPathP (refl , isSetEl (Γ .F-ob (c' .fst)) _ _ _ _))

    ∫V-seq : {Γ Δ Ε : PresheafV C ℓV } {f : NatTrans Γ Δ} {g : NatTrans Δ Ε}
      → ∫V-hom (f ⋆⟨ PRESHEAFV C ℓV ⟩ g) ≡ (∫V-hom g) ∘F (∫V-hom f)
    ∫V-seq {_} {_} {Ε}= Functor≡
      (λ _ → refl)
      (λ {_} {c'} (f , p) → ΣPathP (refl , isSetEl (Ε .F-ob (c' .fst)) _ _ _ _))

  open Properties public

module _ {ℓob ℓhom ℓV : Level} {C : Category ℓob ℓhom} {Γ : PresheafV C ℓV}
         (A : Functor (∫V Γ) (VCat ℓV)) where

  -- A.F-hom depends only on the C-morphism, not the proof in ∫V Γ
  F-hom-PathP : {x x' y y' : (∫V Γ) .ob}
              → (f : ∫V Γ [ x , y ]) (g : ∫V Γ [ x' , y' ])
              → (x≡x' : x ≡ x') (y≡y' : y ≡ y')
              → PathP (λ i → Hom[ C , y≡y' i .fst ] (x≡x' i .fst)) (f .fst) (g .fst)   -- always refl when same C-arrow
              → PathP (λ i → El (A .F-ob (x≡x' i)) → El (A .F-ob (y≡y' i)))
                      (A .F-hom f) (A .F-hom g)
  F-hom-PathP f g x≡x' y≡y' p i = A .F-hom (∫V-Hom-PathP Γ f g x≡x' y≡y' p i)
