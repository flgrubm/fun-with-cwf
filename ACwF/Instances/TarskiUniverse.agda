module ACwF.Instances.TarskiUniverse where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Function
open import Cubical.Functions.FunExtEquiv
open import Cubical.Data.Sigma
open import Cubical.Data.Empty as ⊥ using (⊥)
open import Cubical.Data.W.W using (sup-W) renaming (W to 𝕎)

open import Cubical.Categories.Category

open import ACwF.Base
open import ACwF.Sigma
open import ACwF.Pi
open import ACwF.Eq
open import ACwF.Unit
open import ACwF.Empty
open import ACwF.W

open import TarskiUniverse.Base
open import TarskiUniverse.Properties
open import Utils.TarskiHEq

open import Agda.Builtin.Unit

open Iso
open Category

module _ {ℓU ℓEl : Level} {U : Type ℓU} (Univ : TarskiUniverse ℓEl U) where

  open Algebraic
  open TarskiUniverse Univ

  module _ where
    open CwF

    UCwF : CwF (UCat TU) (ℓ-max ℓU ℓEl) ℓEl
    UCwF .⟨⟩ .fst          = Unit
    UCwF .⟨⟩ .snd _ .fst _ = isContrElUnit .fst
    UCwF .⟨⟩ .snd Γ .snd σ = funExt (λ x → isContrElUnit .snd (σ x))
    UCwF .Ty Γ             = El Γ → U
    UCwF .isSetTy Γ        = isSet→ isSetU
    UCwF ._[_]Ty A σ x     = A (σ x)
    UCwF .[id]Ty _         = refl
    UCwF .[][]Ty _ _ _     = refl
    UCwF .Tm Γ A           = (x : El Γ) → El (A x)
    UCwF .isSetTm _ A      = isSetΠ (λ x → isSetEl (A x))
    UCwF ._[_]Tm a σ x     = a (σ x)
    UCwF .[id]Tm _         = refl
    UCwF .[][]Tm _ _ _     = refl
    UCwF ._▹_              = Sigma
    UCwF .p                = fstSigma
    UCwF .q                = sndSigma
    UCwF ._⁺ σ s           = pairSigma (σ (fstSigma s)) (sndSigma s)
    UCwF .⟨_⟩ a x          = pairSigma x (a x)
    UCwF .⟨⟩∘ a σ          = funExt (λ x → cong₂ pairSigma (sym (cong σ (fstPairSigma x (a (σ x))))) (symP (sndPairSigma x (a (σ x)))))
    UCwF .p⁺∘⟨q⟩≡id        = funExt λ x → cong₂ pairSigma (cong fstSigma (fstPairSigma _ _)) (sndPairSigma _ _) ∙ ηSigma _
    UCwF .∘⁺ σ τ           = funExt λ x → cong₂ pairSigma (cong τ (sym (fstPairSigma _ _))) (symP (sndPairSigma _ _))
    UCwF .id⁺              = funExt λ x → ηSigma _
    UCwF .p∘⁺ σ            = funExt λ x → fstPairSigma _ _
    UCwF .[p][⁺]Ty B σ     = funExt λ x → cong B (fstPairSigma _ _)
    UCwF .q[⁺]Tm σ         = funExt λ x → sndPairSigma _ _
    UCwF .p∘⟨⟩≡id a        = funExt λ x → fstPairSigma _ _
    UCwF .[p][⟨⟩]Ty B a    = funExt λ x → cong B (fstPairSigma _ _)
    UCwF .q[⟨⟩]Tm a        = funExt λ x → sndPairSigma _ _

  module U-Σ
    where

    open Algebraic
    open CwF UCwF

    U-Σ-Structure : Σ-Structure (UCat TU) UCwF
    U-Σ-Structure .Σ-Structure.ΣTy A B x                      = Sigma (A x) λ y → B (pairSigma x y)
    U-Σ-Structure .Σ-Structure.ΣTyNat A B σ                   = funExt λ x → cong (Sigma (A (σ x))) (funExt λ y → cong B (cong₂ pairSigma (cong σ (sym (fstPairSigma _ _))) (symP (sndPairSigma _ _))))
    U-Σ-Structure .Σ-Structure.ΣTmIso A B                     = compIso (codomainIsoDep (λ _ → SigmaIso _ _)) Σ-Π-Iso
    U-Σ-Structure .Σ-Structure.coerce A B a σ                 = funExt λ x → cong B (cong₂ pairSigma (cong σ (sym (fstPairSigma _ _))) (symP (sndPairSigma _ _)))
    U-Σ-Structure .Σ-Structure.ΣTmIsoInvNat {Γ} {Δ} A B a b σ = funExt λ x → congP (λ _ z → uncurry pairSigma (a (σ x) , z)) (symP (toPathP (let
      -- don't look at this
      goal :
        transp (λ i → El (B (pairSigma (σ (fstPairSigma {B = λ v → A (σ v)} x (a (σ x)) i)) (sndPairSigma {B = λ v → A (σ v)} x (a (σ x)) i))))
        i0
        (transp (λ i → El (B (pairSigma (σ (fstPairSigma {B = λ v → A (σ v)} (transp (λ j → El Δ) i x) (a (σ (transp (λ j → El Δ) i x))) (~ i))) (sndPairSigma {B = λ v → A (σ v)} (transp (λ j → El Δ) i x) (a (σ (transp (λ j → El Δ) i x))) (~ i)))))
         i0
         (b (σ (transp (λ j → El Δ) i0 x))))
        ≡
          b (σ x)
      goal j = transp (λ i → El (B (pairSigma (σ (fstPairSigma {B = λ v → A (σ v)} x (a (σ x)) (i ∨ j))) (sndPairSigma {B = λ v → A (σ v)} x (a (σ x)) (i ∨ j)))))
        j
        (transp (λ i → El (B (pairSigma (σ (fstPairSigma {B = λ v → A (σ v)} (transp (λ _ → El Δ) (i ∨ j) x) (a (σ (transp (λ _ → El Δ) (i ∨ j) x))) (~ i ∨ j))) (sndPairSigma {B = λ v → A (σ v)} (transp (λ j → El Δ) (i ∨ j) x) (a (σ (transp (λ _ → El Δ) (i ∨ j) x))) (~ i ∨ j)))))
          j
         (b (σ (transp (λ _ → El Δ) j x))))
      in goal)))

  module U-Π (TU-Pi : hasPi TU) where
    open hasPi TU-Pi
    open Algebraic
    open CwF UCwF

    U-Π-Structure : Π-Structure (UCat TU) UCwF
    U-Π-Structure .Π-Structure.ΠTy A B x                = Pi (A x) (λ y → B (pairSigma x y))
    U-Π-Structure .Π-Structure.ΠTyNat A B σ             = funExt (λ x → cong (Pi (A (σ x))) (funExt (λ y → cong B (cong₂ pairSigma (cong σ (sym (fstPairSigma x y))) (symP (sndPairSigma x y))))))
    U-Π-Structure .Π-Structure.ΠTmIso {Γ} A B           =
      ((a : El Γ) → El (Pi (A a) (λ y → B (pairSigma a y))))           Iso⟨ codomainIsoDep (λ x → PiIso (A x) (λ y → B (pairSigma x y))) ⟩
      (∀ a b → El (B (pairSigma a b)))                                 Iso⟨ invIso curryIso ⟩
      (((a , b) : Σ (El Γ) (λ z → El (A z))) → El (B (pairSigma a b))) Iso⟨ invIso (domIsoDep (invIso (SigmaIso _ _))) ⟩
      (((x : El (Sigma Γ A)) → El (B x)))                              ∎Iso
    U-Π-Structure .Π-Structure.ΠTmIsoInvNat A B M σ i x =
      lamPi
        (λ y → M (pairSigma (σ (fstPairSigma x y (~ i))) (sndPairSigma {B = A [ σ ]Ty} x y (~ i))))

  module U-Eq (TU-Eq : hasEq TU) where
    open hasEq TU-Eq
    open Algebraic
    open CwF UCwF

    U-Eq-Structure : Eq-Structure UCwF
    U-Eq-Structure .Eq-Structure.EqTy A a b x            = Eq (A x) (a x) (b x)
    U-Eq-Structure .Eq-Structure.EqTyNat _ _ _ _         = refl
    U-Eq-Structure .Eq-Structure.EqTmIso {Γ} A a b       =
      ((x : El Γ) → El (Eq (A x) (a x) (b x))) Iso⟨ codomainIsoDep (λ x → EqIso (A x) (a x) (b x)) ⟩
      ((x : El Γ) → a x ≡ b x)                 Iso⟨ funExtIso ⟩
      (a ≡ b)                                  ∎Iso
    U-Eq-Structure .Eq-Structure.EqTmIsoInvNat _ _ _ _ _ = refl

  module U-Unit where
    U-Unit-Structure : Unit-Structure UCwF
    U-Unit-Structure .Unit-Structure.UnitTy _             = Unit
    U-Unit-Structure .Unit-Structure.UnitTyNat _          = refl
    U-Unit-Structure .Unit-Structure.UnitTmIso .fun _     = tt
    U-Unit-Structure .Unit-Structure.UnitTmIso .inv _ _   = isContrElUnit .fst
    U-Unit-Structure .Unit-Structure.UnitTmIso .sec _     = refl
    U-Unit-Structure .Unit-Structure.UnitTmIso .ret a i x = isContrElUnit .snd (a x) i
    U-Unit-Structure .Unit-Structure.UnitTmIsoInvNat _ _  = refl

  module U-⊥ (hasEmptyTU : hasEmpty TU) where
    open hasEmpty hasEmptyTU
    U-⊥-Structure : ⊥-Structure UCwF
    U-⊥-Structure .⊥-Structure.⊥Ty _         = Empty
    U-⊥-Structure .⊥-Structure.⊥TyNat _      = refl
    U-⊥-Structure .⊥-Structure.⊥-elim _ x    = ⊥.rec (EmptyIso .fun (sndSigma x))
    U-⊥-Structure .⊥-Structure.⊥-elimNat _ _ = funExt λ x → ⊥.rec (EmptyIso .fun (sndSigma x))

  -- | W-types.  Here the elements of `Γ ▹ A` are pairs only up to
  -- `SigmaIso`, and those of `W A B` are trees only up to `WIso`; every law
  -- is an equation between elements of sets, so the proofs are chains of
  -- heterogeneous equations (`Utils.TarskiHEq`): a function of the
  -- components of a pair is computed at a pair by `Sigma-β`, and a point of
  -- `Γ ▹ A` has exactly one splitting into a pair (`isPropSplitting`).
  --
  -- The constructor `supSub` splits the label of a node and turns the
  -- subtree function into trees, the eliminator is structural recursion on
  -- those trees, and `wkW` is `σ ⁺` transported along `WTyNat`.
  module U-W (TU-Pi : hasPi TU) (TU-W : hasW TU) where
    open hasPi TU-Pi
    open hasW TU-W
    open Algebraic
    open CwF UCwF
    open U-Π TU-Pi
    open Π-Structure U-Π-Structure
    open TarskiHEq Univ

    -- the result of an application, along a path of codomains
    appPiHEq : {D : U} {Y Y' : El D → U} (eY : Y ≡ Y') {f : El (Pi D Y)} {f' : El (Pi D Y')}
             → ⟪ f ⟫ ≡ ⟪ f' ⟫
             → (c : El D)
             → ---------------------------------
               ⟪ appPi f c ⟫ ≡ ⟪ appPi f' c ⟫
    appPiHEq eY h c i = eY i c , appPi (fromHEq (cong (Pi _) eY) h i) c

    -- `ΠTmIso`'s `fun` is application
    ΠTmIso-fun : {Γ : U} (A : Ty Γ) (B : Ty (Γ ▹ A)) (f : Tm Γ (ΠTy A B)) (s : El (Γ ▹ A))
               → ------------------------------------------------------------------
                 ⟪ appPi (f (fstSigma s)) (sndSigma s) ⟫ ≡ ⟪ ΠTmIso A B .fun f s ⟫
    ΠTmIso-fun A B f s =
        cong (λ φ → ⟪ appPi (φ (fstSigma s)) (sndSigma s) ⟫) (sym (ΠTmIso A B .ret f))
      ∙ cong ⟪_⟫ (funExt⁻ (βPi _) (sndSigma s))
      ∙ cong (λ s → ⟪ ΠTmIso A B .fun f s ⟫) (ηSigma s)

    -- | Trees, nodes and branches for labels `A` and branching `B`.
    module WU {Γ : U} (A : Ty Γ) (B : Ty (Γ ▹ A)) where

      WTy' : Ty Γ
      WTy' x = W (A x) (λ a → B (pairSigma x a))

      -- the trees at a point of Γ
      Tree : El Γ → Type ℓEl
      Tree x = 𝕎 (El (A x)) (λ a → El (B (pairSigma x a)))

      pt : (x : El Γ) → Tree x → El (Γ ▹ WTy')
      pt x t = pairSigma x (WIso _ _ .inv t)

      ptη : (w : El (Γ ▹ WTy'))
          → -------------------------------------------------
            pt (fstSigma w) (WIso _ _ .fun (sndSigma w)) ≡ w
      ptη w = cong (pairSigma (fstSigma w)) (WIso _ _ .ret (sndSigma w)) ∙ ηSigma w

      SubTy' : Ty (Γ ▹ A)
      SubTy' = ΠTy B (WTy' [ p ]Ty [ p ]Ty)

      Node : U
      Node = Γ ▹ A ▹ SubTy'

      Branch : U
      Branch = Node ▹ B [ p ]Ty

      fst²pair : (xa : El (Γ ▹ A)) (b : El (B xa))
               → ----------------------------------------------------------
                 fstSigma (fstSigma (pairSigma {B = B} xa b)) ≡ fstSigma xa
      fst²pair xa b = cong fstSigma (fstPairSigma {B = B} xa b)

      -- where the subtree at a branch lives, for a label `xa` split as `(x , a)`
      subtreePos : (x : El Γ) (a : El (A x)) (xa : El (Γ ▹ A)) (e : pairSigma x a ≡ xa) (b : El (B (pairSigma x a)))
                 → ----------------------------------------------------------------------------
                   fstSigma (fstSigma (pairSigma {B = B} xa (subst (λ z → El (B z)) e b))) ≡ x
      subtreePos x a xa e b =
        fst²pair xa (subst (λ z → El (B z)) e b) ∙ cong fstSigma (sym e) ∙ fstPairSigma {B = A} x a

      -- the subtrees of a node whose label `xa` is split as `(x , a)`
      subtrees : (x : El Γ) (a : El (A x)) (xa : El (Γ ▹ A)) → pairSigma x a ≡ xa
               → El (SubTy' xa)
               → --------------------------------------------------------------
                 El (B (pairSigma x a)) → Tree x
      subtrees x a xa e f b =
        WIso _ _ .fun (subst (λ y → El (WTy' y)) (subtreePos x a xa e b) (appPi f (subst (λ z → El (B z)) e b)))

      supAt : (x : El Γ) (a : El (A x)) (xa : El (Γ ▹ A)) → pairSigma x a ≡ xa
            → El (SubTy' xa)
            → -------------------------------------------------------------
              El (Γ ▹ WTy')
      supAt x a xa e f = pt x (sup-W a (subtrees x a xa e f))

      -- the position, label and subtrees of a node
      posOf : El Node → El Γ
      posOf n = fstSigma (fstSigma n)

      labelOf : (n : El Node) → El (A (posOf n))
      labelOf n = sndSigma (fstSigma n)

      subtreesOf : (n : El Node) → El (B (pairSigma (posOf n) (labelOf n))) → Tree (posOf n)
      subtreesOf n = subtrees (posOf n) (labelOf n) (fstSigma n) (ηSigma (fstSigma n)) (sndSigma n)

      supSub' : El Node → El (Γ ▹ WTy')
      supSub' n = pt (posOf n) (sup-W (labelOf n) (subtreesOf n))

      branchAt : (xa : El (Γ ▹ A)) → El (SubTy' xa) → El (B xa) → El (Γ ▹ WTy')
      branchAt xa f b = pairSigma (fstSigma (fstSigma (pairSigma {B = B} xa b))) (appPi f b)

      branchSub' : El Branch → El (Γ ▹ WTy')
      branchSub' s = branchAt (fstSigma (fstSigma s)) (sndSigma (fstSigma s)) (sndSigma s)

      -- | Nodes with a label that is a pair.
      subtreesC : (x : El Γ) (a : El (A x))
                → El (SubTy' (pairSigma x a))
                → --------------------------------
                  El (B (pairSigma x a)) → Tree x
      subtreesC x a = subtrees x a (pairSigma x a) refl

      supSub-pair : (x : El Γ) (a : El (A x)) (f : El (SubTy' (pairSigma x a)))
                  → --------------------------------------------------------------------------
                    supSub' (pairSigma (pairSigma x a) f) ≡ pt x (sup-W a (subtreesC x a f))
      supSub-pair x a f =
          Sigma-β (λ xa f → supAt (fstSigma xa) (sndSigma xa) xa (ηSigma xa) f) (pairSigma x a) f
        ∙ cong (λ (s : Splitting (pairSigma x a)) → supAt (s .fst .fst) (s .fst .snd) (pairSigma x a) (s .snd) f)
               (isPropSplitting _ ((fstSigma (pairSigma {B = A} x a) , sndSigma (pairSigma {B = A} x a)) , ηSigma (pairSigma x a))
                                  ((x , a) , refl))

      -- the subtree function of a node, from trees
      nodeSub : (x : El Γ) (a : El (A x))
              → (El (B (pairSigma x a)) → Tree x)
              → ---------------------------------
                El (SubTy' (pairSigma x a))
      nodeSub x a g = lamPi λ b →
        subst (λ y → El (WTy' y)) (sym (fst²pair (pairSigma x a) b ∙ fstPairSigma {B = A} x a)) (WIso _ _ .inv (g b))

      node : (x : El Γ) (a : El (A x))
           → (El (B (pairSigma x a)) → Tree x)
           → ---------------------------------
             El Node
      node x a g = pairSigma (pairSigma x a) (nodeSub x a g)

      subtrees-node : (x : El Γ) (a : El (A x)) (g : El (B (pairSigma x a)) → Tree x)
                    → ----------------------------------
                      subtreesC x a (nodeSub x a g) ≡ g
      subtrees-node x a g = funExt λ b →
          cong (WIso _ _ .fun)
            (HEq→≡ ( substHEq WTy' _ _
                   ∙ cong (λ c → ⟪ appPi (nodeSub x a g) c ⟫) (transportRefl b)
                   ∙ cong ⟪_⟫ (funExt⁻ (βPi _) b)
                   ∙ substHEq WTy' _ _))
        ∙ WIso _ _ .sec (g b)

      nodeSub-subtrees : (x : El Γ) (a : El (A x)) (f : El (SubTy' (pairSigma x a)))
                       → ------------------------------------
                         nodeSub x a (subtreesC x a f) ≡ f
      nodeSub-subtrees x a f =
          cong lamPi (funExt λ b →
            HEq→≡ ( substHEq WTy' _ _
                  ∙ cong ⟪_⟫ (WIso _ _ .ret _)
                  ∙ substHEq WTy' _ _
                  ∙ cong (λ c → ⟪ appPi f c ⟫) (transportRefl b)))
        ∙ ηPi f

      node-pair : (x : El Γ) (a : El (A x)) (f : El (SubTy' (pairSigma x a)))
                → -----------------------------------------------------
                  node x a (subtreesC x a f) ≡ pairSigma (pairSigma x a) f
      node-pair x a f = cong (pairSigma (pairSigma x a)) (nodeSub-subtrees x a f)

      -- every node is the node of its label and subtrees
      node-split : (x : El Γ) (a : El (A x)) (xa : El (Γ ▹ A)) (e : pairSigma x a ≡ xa) (f : El (SubTy' xa))
                 → -------------------------------------------------------
                   node x a (subtrees x a xa e f) ≡ pairSigma xa f
      node-split x a xa e =
        J (λ xa e → (f : El (SubTy' xa)) → node x a (subtrees x a xa e f) ≡ pairSigma xa f) (node-pair x a) e

      node-η : (n : El Node)
             → --------------------------------------------------
               node (posOf n) (labelOf n) (subtreesOf n) ≡ n
      node-η n = node-split _ _ (fstSigma n) (ηSigma (fstSigma n)) (sndSigma n) ∙ ηSigma n

      supSub-node : (x : El Γ) (a : El (A x)) (g : El (B (pairSigma x a)) → Tree x)
                  → ------------------------------------------
                    supSub' (node x a g) ≡ pt x (sup-W a g)
      supSub-node x a g =
        supSub-pair x a (nodeSub x a g) ∙ cong (λ G → pt x (sup-W a G)) (subtrees-node x a g)

      -- a branch at a node with label `(x , a)`, as a branch of `B (x , a)`
      down : (x : El Γ) (a : El (A x)) (f : El (SubTy' (pairSigma x a)))
           → El (B (fstSigma (pairSigma {B = SubTy'} (pairSigma x a) f)))
           → ------------------------------------------------------------
             El (B (pairSigma x a))
      down x a f = subst (λ z → El (B z)) (fstPairSigma {B = SubTy'} (pairSigma x a) f)

      branchSub-pair : (x : El Γ) (a : El (A x)) (f : El (SubTy' (pairSigma x a)))
                       (c : El (B (fstSigma (pairSigma {B = SubTy'} (pairSigma x a) f))))
                     → ------------------------------------------------------------------------
                       branchSub' (pairSigma (pairSigma (pairSigma x a) f) c)
                     ≡ pt x (subtreesC x a f (down x a f c))
      branchSub-pair x a f c =
          Sigma-β (λ n c → branchAt (fstSigma n) (sndSigma n) c) (pairSigma (pairSigma x a) f) c
        ∙ Sigma-β-dep {D = λ xa → El (B xa)} branchAt (pairSigma x a) f c
        ∙ pair≡ (fst²pair (pairSigma x a) (down x a f c) ∙ fstPairSigma {B = A} x a)
                ( cong (λ c → ⟪ appPi f c ⟫) (sym (transportRefl _))
                ∙ sym (substHEq WTy' _ _)
                ∙ cong ⟪_⟫ (sym (WIso _ _ .ret _)))

      branchSub-node : (x : El Γ) (a : El (A x)) (g : El (B (pairSigma x a)) → Tree x)
                       (c : El (B (fstSigma (pairSigma {B = SubTy'} (pairSigma x a) (nodeSub x a g)))))
                     → ------------------------------------------------------------------------------
                       branchSub' (pairSigma (node x a g) c) ≡ pt x (g (down x a (nodeSub x a g) c))
      branchSub-node x a g c =
          branchSub-pair x a (nodeSub x a g) c
        ∙ cong (λ G → pt x (G (down x a (nodeSub x a g) c))) (subtrees-node x a g)

      -- | Elimination
      IHTy' : Ty (Γ ▹ WTy') → Ty Node
      IHTy' P = ΠTy (B [ p ]Ty) (P [ branchSub' ]Ty)

      ih' : {P : Ty (Γ ▹ WTy')} → Tm (Γ ▹ WTy') P → Tm Node (IHTy' P)
      ih' {P} s = ΠTmIso (B [ p ]Ty) (P [ branchSub' ]Ty) .inv (s [ branchSub' ]Tm)

      module _ (P : Ty (Γ ▹ WTy')) (m : Tm (Node ▹ IHTy' P) (λ t → P (supSub' (fstSigma t)))) where

        private
          ElP : El (Γ ▹ WTy') → Type ℓEl
          ElP w = El (P w)

        -- the induction hypotheses at `node x a g`, from values at its subtrees
        nodeIH : (x : El Γ) (a : El (A x)) (g : El (B (pairSigma x a)) → Tree x)
               → ((b : El (B (pairSigma x a))) → El (P (pt x (g b))))
               → ----------------------------------------------------
                 El (IHTy' P (node x a g))
        nodeIH x a g r = lamPi λ c →
          subst ElP (sym (branchSub-node x a g c)) (r (down x a (nodeSub x a g) c))

        step : (x : El Γ) (a : El (A x)) (g : El (B (pairSigma x a)) → Tree x)
             → ((b : El (B (pairSigma x a))) → El (P (pt x (g b))))
             → ----------------------------------------------------
               El (P (pt x (sup-W a g)))
        step x a g r =
          subst ElP (cong supSub' (fstPairSigma {B = IHTy' P} (node x a g) (nodeIH x a g r)) ∙ supSub-node x a g)
                (m (pairSigma (node x a g) (nodeIH x a g r)))

        elimU : (x : El Γ) (t : Tree x)
              → -----------------------
                El (P (pt x t))
        elimU x (sup-W a g) = step x a g (λ b → elimU x (g b))

        s₀ : Tm (Γ ▹ WTy') P
        s₀ w = subst ElP (ptη w) (elimU (fstSigma w) (WIso _ _ .fun (sndSigma w)))

        s₀-pt : (x : El Γ) (t : Tree x)
              → ---------------------------------
                ⟪ s₀ (pt x t) ⟫ ≡ ⟪ elimU x t ⟫
        s₀-pt x t =
            substHEq P _ _
          ∙ cong (λ (y , t') → ⟪ elimU y t' ⟫)
                 ( Sigma-β (λ y u → (y , WIso (A y) (λ a → B (pairSigma y a)) .fun u)) x (WIso _ _ .inv t)
                 ∙ cong (x ,_) (WIso _ _ .sec t))

        -- the induction hypotheses at `node x a g` from values that agree with `s`
        ih-node : (s : Tm (Γ ▹ WTy') P) (x : El Γ) (a : El (A x)) (g : El (B (pairSigma x a)) → Tree x)
                  (r : (b : El (B (pairSigma x a))) → El (P (pt x (g b))))
                → ((b : El (B (pairSigma x a))) → ⟪ r b ⟫ ≡ ⟪ s (pt x (g b)) ⟫)
                → ---------------------------------------------------------
                  nodeIH x a g r ≡ ih' s (node x a g)
        ih-node s x a g r h = cong lamPi (funExt λ c →
          HEq→≡ ( substHEq P _ _
                ∙ h _
                ∙ cong (λ w → ⟪ s w ⟫) (sym (branchSub-node x a g c))))

        -- the method at the induction hypotheses provided by `s`
        mAt : Tm (Γ ▹ WTy') P → El Node → ∫El
        mAt s n = ⟪ m (pairSigma n (ih' s n)) ⟫

        -- `s` is the method at the node `n` (`isWElim`, pointwise and up to its type path)
        isElimU : Tm (Γ ▹ WTy') P → El Node → Type (ℓ-max ℓU ℓEl)
        isElimU s n = ⟪ s (supSub' n) ⟫ ≡ mAt s n

        -- any eliminator is `elimU`, by induction on the tree
        elimU-η : (s : Tm (Γ ▹ WTy') P)
                → ((n : El Node) → isElimU s n)
                → (x : El Γ) (t : Tree x)
                → ---------------------------------
                  ⟪ elimU x t ⟫ ≡ ⟪ s (pt x t) ⟫
        elimU-η s h x (sup-W a g) =
            substHEq P _ _
          ∙ cong (λ ι → ⟪ m (pairSigma (node x a g) ι) ⟫) (ih-node s x a g _ λ b → elimU-η s h x (g b))
          ∙ sym (h (node x a g))
          ∙ cong (λ w → ⟪ s w ⟫) (supSub-node x a g)

        -- `s₀` is an eliminator: `supSub'` builds a tree, on which `elimU`
        -- computes, at the node of its subtrees, which is the given node
        module _ (n : El Node) where

          elimU-β₁ : ⟪ s₀ (supSub' n) ⟫ ≡ ⟪ elimU (posOf n) (sup-W (labelOf n) (subtreesOf n)) ⟫
          elimU-β₁ = s₀-pt (posOf n) (sup-W (labelOf n) (subtreesOf n))

          elimU-β₂ : ⟪ elimU (posOf n) (sup-W (labelOf n) (subtreesOf n)) ⟫
                   ≡ mAt s₀ (node (posOf n) (labelOf n) (subtreesOf n))
          elimU-β₂ =
              substHEq P _ _
            ∙ cong (λ ι → ⟪ m (pairSigma (node (posOf n) (labelOf n) (subtreesOf n)) ι) ⟫)
                   (ih-node s₀ (posOf n) (labelOf n) (subtreesOf n) _ λ b → sym (s₀-pt (posOf n) _))

          elimU-β : isElimU s₀ n
          elimU-β = elimU-β₁ ∙ elimU-β₂ ∙ cong (mAt s₀) (node-η n)

        -- `s₀` is the unique eliminator, along any path of types
        isContrWElimU : {e : (s : Tm (Γ ▹ WTy') P)
                           → P [ supSub' ]Ty ≡ P [ (λ t → supSub' (fstSigma t)) ]Ty [ ⟨ ih' s ⟩ ]Ty}
                      → ----------------------------------------------------------------------------
                        isContr (Σ[ s ∈ Tm (Γ ▹ WTy') P ]
                                   PathP (λ i → Tm Node (e s i)) (s [ supSub' ]Tm) (m [ ⟨ ih' s ⟩ ]Tm))
        isContrWElimU {e} .fst = s₀ , ΠPathP (e s₀) elimU-β
        isContrWElimU {e} .snd (s , h) =
          Σ≡Prop (λ _ → isOfHLevelPathP' 1 (isSetTm _ _) _ _)
                 (funExt λ w → subst (λ w → s₀ w ≡ s w) (ptη w)
                                     (HEq→≡ (s₀-pt _ _ ∙ elimU-η s (λ n → toHEq (λ i → h i n)) _ _)))

    -- | Substitution
    module WNat {Δ Γ : U} (A : Ty Γ) (B : Ty (Γ ▹ A)) (σ : El Δ → El Γ) where
      private
        module Γ' = WU A B
        module Δ' = WU (A [ σ ]Ty) (B [ _⁺ {A = A} σ ]Ty)

      σ⁺ : El (Δ ▹ A [ σ ]Ty) → El (Γ ▹ A)
      σ⁺ = _⁺ {A = A} σ

      ⁺pair : (x : El Δ) (a : El (A (σ x)))
            → -----------------------------------------
              σ⁺ (pairSigma x a) ≡ pairSigma (σ x) a
      ⁺pair x a = Sigma-β (λ y a → pairSigma {B = A} (σ y) a) x a

      -- the branching of `WTy' A B [ σ ]Ty` and of `WTy' (A [ σ ]Ty) (B [ σ ⁺ ]Ty)`
      eB : (x : El Δ)
         → -------------------------------------------------------------------
           (λ a → B (pairSigma (σ x) a)) ≡ (λ a → B (σ⁺ (pairSigma x a)))
      eB x = funExt λ a → cong B (sym (⁺pair x a))

      WTyNatU : Γ'.WTy' [ σ ]Ty ≡ Δ'.WTy'
      WTyNatU = funExt λ x → cong (W (A (σ x))) (eB x)

      wkWU : El (Δ ▹ Δ'.WTy') → El (Γ ▹ Γ'.WTy')
      wkWU = subst (λ T → El (Δ ▹ T) → El (Γ ▹ Γ'.WTy')) WTyNatU (_⁺ {A = Γ'.WTy'} σ)

      wkWU≡ : PathP (λ i → El (Δ ▹ WTyNatU i) → El (Γ ▹ Γ'.WTy')) (_⁺ {A = Γ'.WTy'} σ) wkWU
      wkWU≡ = subst-filler (λ T → El (Δ ▹ T) → El (Γ ▹ Γ'.WTy')) WTyNatU (_⁺ {A = Γ'.WTy'} σ)

      wkWU-pair : (x : El Δ) {u : El (Γ'.WTy' (σ x))} {u' : El (Δ'.WTy' x)}
                → ⟪ u ⟫ ≡ ⟪ u' ⟫
                → ----------------------------------------------
                  pairSigma (σ x) u ≡ wkWU (pairSigma x u')
      wkWU-pair x {u} h =
          sym (Sigma-β (λ y v → pairSigma {B = Γ'.WTy'} (σ y) v) x u)
        ∙ λ i → wkWU≡ i (pairSigma x (fromHEq (λ j → WTyNatU j x) h i))

      -- the codomains of the subtree functions at `σ ⁺ xa` and at `xa`
      eY : (xa : El (Δ ▹ A [ σ ]Ty))
         → -------------------------------------------------------------------------
           (λ c → Γ'.WTy' (fstSigma (fstSigma (pairSigma {B = B} (σ⁺ xa) c))))
         ≡ (λ c → Δ'.WTy' (fstSigma (fstSigma (pairSigma {B = λ z → B (σ⁺ z)} xa c))))
      eY xa = funExt λ c →
          cong Γ'.WTy' ( Γ'.fst²pair (σ⁺ xa) c
                       ∙ fstPairSigma {B = A} (σ (fstSigma xa)) (sndSigma xa)
                       ∙ cong (λ z → σ (fstSigma z)) (sym (fstPairSigma {B = λ z → B (σ⁺ z)} xa c)))
        ∙ funExt⁻ WTyNatU _

      -- the nodes built by `supSub` at `σ ⁺ xa` and at `xa` agree
      module _ (xa : El (Δ ▹ A [ σ ]Ty)) (f : El (Γ'.SubTy' (σ⁺ xa))) (f' : El (Δ'.SubTy' xa))
               (h : ⟪ f ⟫ ≡ ⟪ f' ⟫) where

        subtreesP : PathP (λ i → El (eB (fstSigma xa) i (sndSigma xa))
                               → 𝕎 (El (A (σ (fstSigma xa)))) (λ a → El (eB (fstSigma xa) i a)))
                          (Γ'.subtrees (σ (fstSigma xa)) (sndSigma xa) (σ⁺ xa) refl f)
                          (Δ'.subtrees (fstSigma xa) (sndSigma xa) xa (ηSigma xa) f')
        subtreesP = funExtDep λ {b} {b'} pb i →
          WIso (A (σ (fstSigma xa))) (eB (fstSigma xa) i) .fun
            (fromHEq (λ i → W (A (σ (fstSigma xa))) (eB (fstSigma xa) i))
              ( substHEq Γ'.WTy' (Γ'.subtreePos _ _ _ refl b) _
              ∙ appPiHEq (eY xa) h _
              ∙ cong (λ c → ⟪ appPi f' c ⟫)
                     (HEq→≡ ( substHEq B refl b
                            ∙ toHEq pb
                            ∙ sym (substHEq (λ z → B (σ⁺ z)) (ηSigma xa) b')))
              ∙ sym (substHEq Δ'.WTy' (Δ'.subtreePos _ _ _ (ηSigma xa) b') _))
              i)

        supHEq : ⟪ WIso (A (σ (fstSigma xa))) (eB (fstSigma xa) i0) .inv
                     (sup-W (sndSigma xa) (Γ'.subtrees (σ (fstSigma xa)) (sndSigma xa) (σ⁺ xa) refl f)) ⟫
               ≡ ⟪ WIso (A (σ (fstSigma xa))) (eB (fstSigma xa) i1) .inv
                     (sup-W (sndSigma xa) (Δ'.subtrees (fstSigma xa) (sndSigma xa) xa (ηSigma xa) f')) ⟫
        supHEq = toHEq λ i → WIso (A (σ (fstSigma xa))) (eB (fstSigma xa) i) .inv (sup-W (sndSigma xa) (subtreesP i))

      supSubNatU : {e : Γ'.SubTy' [ σ⁺ ]Ty ≡ Δ'.SubTy'}
                 → ------------------------------------------------------------------------
                   PathP (λ i → El (Δ ▹ A [ σ ]Ty ▹ e i) → El (Γ ▹ Γ'.WTy'))
                         (λ n → Γ'.supSub' (_⁺ {A = Γ'.SubTy'} σ⁺ n)) (λ n → wkWU (Δ'.supSub' n))
      supSubNatU {e} = SigmaMapPathP e λ xa f f' h →
          cong Γ'.supSub' (Sigma-β (λ y v → pairSigma {B = Γ'.SubTy'} (σ⁺ y) v) xa f)
        ∙ Sigma-β (λ y f → Γ'.supAt (fstSigma y) (sndSigma y) y (ηSigma y) f) (σ⁺ xa) f
        ∙ cong (λ (s : Splitting (σ⁺ xa)) → Γ'.supAt (s .fst .fst) (s .fst .snd) (σ⁺ xa) (s .snd) f)
               (isPropSplitting _ ((fstSigma (σ⁺ xa) , sndSigma (σ⁺ xa)) , ηSigma (σ⁺ xa))
                                  ((σ (fstSigma xa) , sndSigma xa) , refl))
        ∙ wkWU-pair (fstSigma xa) (supHEq xa f f' h)
        ∙ cong wkWU (sym (Sigma-β (λ y f → Δ'.supAt (fstSigma y) (sndSigma y) y (ηSigma y) f) xa f'))

    -- the subtree at a branch is the subtree function applied
    q[branchSub]U : {Γ : U} {A : Ty Γ} {B : Ty (Γ ▹ A)}
                    {f' : Tm (WU.Node A B) (ΠTy (B [ p ]Ty) (WU.WTy' A B [ p ]Ty [ p ]Ty [ _⁺ {A = B} p ]Ty))}
                  → PathP (λ i → Tm (WU.Node A B) (ΠTyNat B (WU.WTy' A B [ p ]Ty [ p ]Ty) p i)) q f'
                  → {e : WU.WTy' A B [ p ]Ty [ WU.branchSub' A B ]Ty
                       ≡ WU.WTy' A B [ p ]Ty [ p ]Ty [ _⁺ {A = B} (p {A = WU.SubTy' A B}) ]Ty}
                  → ---------------------------------------------------------------------------
                    PathP (λ i → Tm (WU.Branch A B) (e i))
                          (q [ WU.branchSub' A B ]Tm)
                          (ΠTmIso (B [ p ]Ty) (WU.WTy' A B [ p ]Ty [ p ]Ty [ _⁺ {A = B} p ]Ty) .fun f')
    q[branchSub]U {A = A} {B = B} {f' = f'} H = ΠPathP _ λ s →
        sndHEq _ _
      ∙ toHEq (λ i → appPi (H i (fstSigma s)) (sndSigma s))
      ∙ ΠTmIso-fun (B [ p ]Ty) (WU.WTy' A B [ p ]Ty [ p ]Ty [ _⁺ {A = B} p ]Ty) f' s

    open W-Structure

    U-W-Structure : W-Structure UCwF U-Π-Structure
    U-W-Structure .WTy                         = WU.WTy'
    U-W-Structure .WTyNat A B σ                = WNat.WTyNatU A B σ
    U-W-Structure .wkW {A = A} {B = B} σ       = WNat.wkWU A B σ
    U-W-Structure .wkW≡ {A = A} {B = B} σ      = WNat.wkWU≡ A B σ
    U-W-Structure .supSub {A = A} {B = B}      = WU.supSub' A B
    U-W-Structure .p∘supSub                    = funExt λ _ → fstPairSigma _ _
    U-W-Structure .supSubNat {A = A} {B = B} σ = WNat.supSubNatU A B σ
    U-W-Structure .branchSub {A = A} {B = B}   = WU.branchSub' A B
    U-W-Structure .p∘branchSub {A = A} {B = B} = funExt λ s → fstPairSigma _ _ ∙ WU.fst²pair A B _ _
    U-W-Structure .q[branchSub] {f' = f'} H    = q[branchSub]U {f' = f'} H
    U-W-Structure .isContrWElim A B P m        = WU.isContrWElimU A B P m
