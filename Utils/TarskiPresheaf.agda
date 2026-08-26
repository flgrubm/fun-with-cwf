module Utils.TarskiPresheaf where

open import TarskiUniverse.Base

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Instances.Functors

open import TarskiUniverse.Base
open import TarskiUniverse.Properties

open Category
open Functor

module _ {ℓob ℓhom ℓU ℓEl : Level} (C : Category ℓob ℓhom) {U : Type ℓU} (TU : BareTarskiUniverse ℓEl U) where
  PresheafU = Functor (C ^op) (UCat TU)
  PRESHEAFU = FUNCTOR (C ^op) (UCat TU)

module _ {ℓob ℓhom ℓU ℓEl : Level} {C : Category ℓob ℓhom} {U : Type ℓU} {TU : BareTarskiUniverse ℓEl U} where
  open BareTarskiUniverse TU
  module Base (F : PresheafU C TU) where

    private
      ∫ob : Type (ℓ-max ℓob ℓEl)
      ∫ob = Σ[ c ∈ C .ob ] (El (F ⟅ c ⟆))

    private
      ∫Hom[_,_] : ∫ob → ∫ob → Type (ℓ-max ℓhom ℓEl)
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

    ∫U : Category _ _
    ∫U .ob = ∫ob
    ∫U .Hom[_,_] = ∫Hom[_,_]
    ∫U .id .fst = C .id
    ∫U .id {x} .snd = funExt⁻ (F-id F) (x .snd)
    ∫U ._⋆_ = _∫⋆_
    ∫U .⋆IdL {x} {y} f = ∫Hom≡ (C .⋆IdR (f .fst))
    ∫U .⋆IdR {x} {y} f = ∫Hom≡ (C .⋆IdL (f .fst))
    ∫U .⋆Assoc f g h =
      ∫Hom≡ ((C ^op) .⋆Assoc (f .fst) (g .fst) (h .fst))
    ∫U .isSetHom {a} {b} =
      isSetΣSndProp (C .isSetHom) λ f → isSetEl (F-ob F (b .fst)) _ _

    ∫U-Hom-PathP : ∀ {x} {x'} {y} {y'} (f : ∫U [ x , y ]) (g : ∫U [ x' , y' ])
      → (x≡x' : x ≡ x') → (y≡y' : y ≡ y')
      → PathP (λ i → C [ y≡y' i .fst , x≡x' i .fst ]) (f .fst) (g .fst)
      → PathP (λ i → ∫U [ x≡x' i , y≡y' i ]) f g
    ∫U-Hom-PathP = ∫HomPathP

  open Base public

  module Properties where
    ∫U-hom : {Γ Δ : PresheafU C TU} → NatTrans Δ Γ → Functor (∫U Δ) (∫U Γ)
    ∫U-hom {Γ} {Δ} η .F-ob (I , x) = I , η . NatTrans.N-ob I x
    ∫U-hom {Γ} {Δ} η .F-hom {I , x} {J , y} (f , p) = f , proof
      where
        proof : (Γ ⟪ f ⟫) (NatTrans.N-ob η I x) ≡ NatTrans.N-ob η J y
        proof =
              (Γ ⟪ f ⟫) (NatTrans.N-ob η I x)
            ≡⟨ funExt⁻ (sym (η .NatTrans.N-hom f)) x ⟩
              η .NatTrans.N-ob J (Δ .F-hom f x)
            ≡⟨ cong _ p ⟩
              η .NatTrans.N-ob J y
            ∎
    ∫U-hom {Γ} {Δ} η .F-id {c , _} = ΣPathP ( refl , isSetEl (Γ ⟅ c ⟆) _ _ _ _)
    ∫U-hom {Γ} {Δ} η .F-seq {z = c , _} f g = ΣPathP ( refl , isSetEl (Γ ⟅ c ⟆) _ _ _ _)

    ∫U-id : {Γ : PresheafU C TU} → ∫U-hom (idTrans Γ) ≡ Id
    ∫U-id {Γ} = Functor≡
      (λ _ → refl)
      (λ {_} {c'} (f , p) → ΣPathP (refl , isSetEl (Γ .F-ob (c' .fst)) _ _ _ _))

    ∫U-seq : {Γ Δ Ε : PresheafU C TU} {f : NatTrans Γ Δ} {g : NatTrans Δ Ε}
      → ∫U-hom (f ⋆⟨ PRESHEAFU C TU ⟩ g) ≡ (∫U-hom g) ∘F (∫U-hom f)
    ∫U-seq {_} {_} {Ε}= Functor≡
      (λ _ → refl)
      (λ {_} {c'} (f , p) → ΣPathP (refl , isSetEl (Ε .F-ob (c' .fst)) _ _ _ _))

  open Properties public

module _ {ℓob ℓhom ℓU ℓEl : Level} {C : Category ℓob ℓhom} {U : Type ℓU} {TU : BareTarskiUniverse ℓEl U} {Γ : PresheafU C TU}
         (A : Functor (∫U Γ) (UCat TU)) where
  open BareTarskiUniverse TU

  -- A.F-hom depends only on the C-morphism, not the proof in ∫V Γ
  F-hom-PathP : {x x' y y' : (∫U Γ) .ob}
              → (f : ∫U Γ [ x , y ]) (g : ∫U Γ [ x' , y' ])
              → (x≡x' : x ≡ x') (y≡y' : y ≡ y')
              → PathP (λ i → Hom[ C , y≡y' i .fst ] (x≡x' i .fst)) (f .fst) (g .fst)   -- always refl when same C-arrow
              → PathP (λ i → El (A .F-ob (x≡x' i)) → El (A .F-ob (y≡y' i)))
                      (A .F-hom f) (A .F-hom g)
  F-hom-PathP f g x≡x' y≡y' p i = A .F-hom (∫U-Hom-PathP Γ f g x≡x' y≡y' p i)

  F-id-PathP : ∀ {ob} proof → A .F-hom {ob} (C .id , proof) ≡ λ x → x
  F-id-PathP proof = F-hom-PathP (C .id , proof) _ refl refl refl ∙ A .F-id
