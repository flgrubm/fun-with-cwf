module Utils.TarskiQuotient where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv using (fiber)
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT using (∥_∥₁)
open import Cubical.HITs.SetQuotients as SQ using (_/_ ; [_] ; eq/)

open import TarskiUniverse.Base

open Iso

-- | Set quotients in a Tarski universe, fibrewise over a base: the common
-- core of the quotient types in the families model
-- (`ACwF.Instances.TarskiUniverse`) and, stage by stage, in the presheaf
-- model (`ACwF.Instances.TarskiPresheaf.Quotient`).  Contexts there are
-- iterated `Sigma`s, so a variable of a quotient over a base `X` is an
-- element of `Sigma X (λ x → Quot (A x) (rel x))`, and elimination is a
-- statement about functions out of it.
module Fibrewise {ℓU ℓEl : Level} {U : Type ℓU} (Univ : TarskiUniverse ℓEl U) where
  open TarskiUniverse Univ

  -- | Dependent paths in a family of codes over *some* path of the base.
  -- The base is a set, so these compose freely (`_∙O_`) and can be put over
  -- any path with the same endpoints (`over`).  (A record rather than a Σ,
  -- so that the family is inferred from the type.)
  record Over {X : U} (F : El X → U) {x y : El X} (u : El (F x)) (v : El (F y)) : Type ℓEl where
    constructor overPath
    field
      base : x ≡ y
      path : PathP (λ i → El (F (base i))) u v

  module _ {X : U} (F : El X → U) where

    over : {x y : El X} {u : El (F x)} {v : El (F y)} → Over F u v
         → (e : x ≡ y) → PathP (λ i → El (F (e i))) u v
    over {u = u} {v} (overPath e h) e' = subst (λ e → PathP (λ i → El (F (e i))) u v) (isSetEl X _ _ e e') h

    -- a dependent path along a loop is a path
    over≡ : {x : El X} {u v : El (F x)} → Over F u v → u ≡ v
    over≡ o = over o refl

  module _ {X : U} {F : El X → U} where

    infixr 30 _∙O_
    _∙O_ : {x y z : El X} {u : El (F x)} {v : El (F y)} {w : El (F z)}
         → Over F u v → Over F v w → Over F u w
    overPath e h ∙O overPath e' h' = overPath (e ∙ e') (compPathP' {B = λ x → El (F x)} h h')

    symO : {x y : El X} {u : El (F x)} {v : El (F y)} → Over F u v → Over F v u
    symO (overPath e h) = overPath (sym e) (symP h)

  module _ {X : U} (F : El X → U) where

    -- a function applied along a path of its domain
    congO : {Y : U} {f : El Y → El X} (g : (y : El Y) → El (F (f y))) {y y' : El Y} (e : y ≡ y')
          → Over F (g y) (g y')
    congO {f = f} g e = overPath (cong f e) (λ i → g (e i))

    -- an element and its transport along `e` form a dependent path
    substO : {x y : El X} (e : x ≡ y) (u : El (F x)) → Over F u (subst (λ x → El (F x)) e u)
    substO e u = overPath e (subst-filler (λ x → El (F x)) e u)

    -- the β-law of the second component
    sndPairO : (x : El X) (u : El (F x)) → Over F (sndSigma (pairSigma {B = F} x u)) u
    sndPairO x u = overPath (fstPairSigma x u) (sndPairSigma x u)

    -- canonical pairs are equal if their second components are related by a dependent path
    pairO : {x y : El X} {u : El (F x)} {v : El (F y)} → Over F u v → pairSigma {B = F} x u ≡ pairSigma y v
    pairO (overPath e h) i = pairSigma (e i) (h i)

  -- a fibrewise map applied along a dependent path
  mapO : {X : U} {F G : El X → U} (h : (x : El X) → El (F x) → El (G x))
         {x y : El X} {u : El (F x)} {v : El (F y)}
       → Over F u v → Over G (h x u) (h y v)
  mapO h (overPath e k) = overPath e (λ i → h (e i) (k i))

  -- | Two variables of type `A` over a point of `X`: the context
  -- `X ▹ A ▹ A [ p ]` as a code, and its elements as triples.  The third
  -- component has to be moved along the β-law of the inner pair.
  module _ {X : U} (A : El X → U) where

    Sigma² : U
    Sigma² = Sigma (Sigma X A) (λ s → A (fstSigma s))

    Triple : Type ℓEl
    Triple = Σ[ x ∈ El X ] El (A x) × El (A x)

    pair² : Triple → El Sigma²
    pair² (x , a , b) = pairSigma (pairSigma x a) (subst (λ y → El (A y)) (sym (fstPairSigma x a)) b)

    unpair² : El Sigma² → Triple
    unpair² w = fstSigma (fstSigma w) , sndSigma (fstSigma w) , sndSigma w

    unpair²-pair² : (t : Triple) → unpair² (pair² t) ≡ t
    unpair²-pair² (x , a , b) i = base i , a≡ i , b≡ i
      where
        γ : fstSigma (pair² (x , a , b)) ≡ pairSigma x a
        γ = fstPairSigma {B = λ s → A (fstSigma s)} _ _
        β : fstSigma (pairSigma {B = A} x a) ≡ x
        β = fstPairSigma x a
        base : fstSigma (fstSigma (pair² (x , a , b))) ≡ x
        base = cong fstSigma γ ∙ β
        a≡ : PathP (λ i → El (A (base i))) (sndSigma (fstSigma (pair² (x , a , b)))) a
        a≡ = compPathP' {B = λ y → El (A y)} (congP (λ _ → sndSigma) γ) (sndPairSigma x a)
        b≡ : PathP (λ i → El (A (base i))) (sndSigma (pair² (x , a , b))) b
        b≡ = compPathP' {B = λ y → El (A y)} (sndPairSigma {B = λ s → A (fstSigma s)} _ _)
                                              (symP (subst-filler (λ y → El (A y)) (sym β) b))

    -- the second and the third component of `unpair²-pair²`
    unpair²-pair²O₂ : (t : Triple) → Over A (unpair² (pair² t) .snd .fst) (t .snd .fst)
    unpair²-pair²O₂ t = overPath (cong fst (unpair²-pair² t)) (cong (λ s → s .snd .fst) (unpair²-pair² t))

    unpair²-pair²O₃ : (t : Triple) → Over A (unpair² (pair² t) .snd .snd) (t .snd .snd)
    unpair²-pair²O₃ t = overPath (cong fst (unpair²-pair² t)) (cong (λ s → s .snd .snd) (unpair²-pair² t))

    pair²-unpair² : (w : El Sigma²) → pair² (unpair² w) ≡ w
    pair²-unpair² w =
      pairSigma≡ (ηSigma (fstSigma w))
        (over A (symO (substO A (sym (fstPairSigma (fstSigma (fstSigma w)) (sndSigma (fstSigma w)))) (sndSigma w)))
                (cong fstSigma (ηSigma (fstSigma w))))

  -- | Substitution under two variables: `σ ⁺²` on codes.
  module _ {X Y : U} (A : El X → U) (σ : El Y → El X) where

    -- unpair, apply `σ` to the first component, re-pair
    sub² : El (Sigma² (λ y → A (σ y))) → El (Sigma² A)
    sub² w = pair² A (σ (t .fst) , t .snd)
      where t = unpair² (λ y → A (σ y)) w

    -- Plain pairing at `i0`, `sub²` at `i1`.  The two differ in the third
    -- component, which `sub²` moves back along the β-law of the inner pair;
    -- at `i` it lies over that law at `i`.
    sub²-filler : (i : I) (y : El Y) (a : El (A (σ y)))
                → El (A (fstPairSigma {B = A} (σ y) a i))
                → --------------------------------------
                  El (Sigma² A)
    sub²-filler i y a b =
      pairSigma (pairSigma (σ y) a) (transp (λ j → El (A (fstPairSigma {B = A} (σ y) a (i ∧ ~ j)))) (~ i) b)

    -- `R` at the re-paired triple with `σ` applied is `R` at `sub²` of the
    -- re-paired triple
    relSub² : (R : El (Sigma² A) → U) (y : El Y)
            → ------------------------------------------------------------
              Path (El (A (σ y)) → El (A (σ y)) → U)
                   (λ a b → R (pair² A (σ y , a , b)))
                   (λ a b → R (sub² (pair² (λ z → A (σ z)) (y , a , b))))
    relSub² R y = funExt λ a → funExt λ b →
      cong (λ t → R (pair² A (σ (t .fst) , t .snd))) (sym (unpair²-pair² (λ z → A (σ z)) (y , a , b)))

  -- | Constructions that need codes for set quotients.
  module _ (TU-Quot : hasQuotient TU) where
    open hasQuotient TU-Quot

    -- related elements have equal classes
    classQuot≡ : {A : U} {R : El A → El A → U} (a b : El A) → El (R a b)
               → classQuot {R = R} a ≡ classQuot b
    classQuot≡ a b r = cong (QuotIso _ _ .inv) (eq/ a b r)

    -- `g` sends related elements to equal classes.  This is a proposition
    -- (`isPropPreserves`), so `quotMap g` does not depend on its proof.
    Preserves : {X Y : U} (RX : El X → El X → U) (RY : El Y → El Y → U) (g : El X → El Y) → Type ℓEl
    Preserves {X} {Y} RX RY g =
      (a b : El X) → El (RX a b) → Path (El Y / (λ a b → El (RY a b))) [ g a ] [ g b ]

    isPropPreserves : {X Y : U} {RX : El X → El X → U} {RY : El Y → El Y → U} {g : El X → El Y}
                    → ----------------------------
                      isProp (Preserves RX RY g)
    isPropPreserves {g = g} = isPropΠ3 λ a b _ → SQ.squash/ [ g a ] [ g b ]

    -- | The action of a relation-preserving map on quotients, and how it
    -- acts on classes, identities and composites.
    module _ {X Y : U} {RX : El X → El X → U} {RY : El Y → El Y → U} where

      -- `quotMap` on the set quotients
      quotMap/ : (g : El X → El Y) → Preserves RX RY g
               → ------------------------------------------------------------
                 El X / (λ a b → El (RX a b)) → El Y / (λ a b → El (RY a b))
      quotMap/ g h = SQ.rec SQ.squash/ (λ a → [ g a ]) h

      quotMap : (g : El X → El Y) → Preserves RX RY g
              → ---------------------------------
                El (Quot X RX) → El (Quot Y RY)
      quotMap g h u = QuotIso _ _ .inv (quotMap/ g h (QuotIso _ _ .fun u))

      quotMap-class : (g : El X → El Y) (h : Preserves RX RY g) (a : El X)
                    → ---------------------------------------------
                      quotMap g h (classQuot a) ≡ classQuot (g a)
      quotMap-class g h a = cong (λ v → QuotIso _ _ .inv (quotMap/ g h v)) (QuotIso _ _ .sec [ a ])

    -- along paths of relations, the maps `quotMap g` at the two ends form a
    -- dependent path, for any two proofs of preservation
    quotMap-PathP : {X Y : U} {RX : I → El X → El X → U} {RY : I → El Y → El Y → U} (g : El X → El Y)
                    (h₀ : Preserves (RX i0) (RY i0) g) (h₁ : Preserves (RX i1) (RY i1) g)
                  → ------------------------------------------------------------------
                    PathP (λ i → El (Quot X (RX i)) → El (Quot Y (RY i))) (quotMap g h₀) (quotMap g h₁)
    quotMap-PathP {RX = RX} {RY} g h₀ h₁ i = quotMap {RX = RX i} {RY = RY i} g (hs i)
      where
        hs : PathP (λ i → Preserves (RX i) (RY i) g) h₀ h₁
        hs = isProp→PathP (λ i → isPropPreserves {RX = RX i} {RY = RY i} {g = g}) h₀ h₁

    -- `quotMap` of a map that is pointwise the identity is the identity
    quotMap-id : {X : U} {R : El X → El X → U} {g : El X → El X} {h : Preserves R R g}
               → ((a : El X) → g a ≡ a)
               → ---------------------------------------
                 (u : El (Quot X R)) → quotMap g h u ≡ u
    quotMap-id {g = g} {h} e u = goal (QuotIso _ _ .fun u) ∙ QuotIso _ _ .ret u
      where
        goal : (v : _) → QuotIso _ _ .inv (quotMap/ g h v) ≡ QuotIso _ _ .inv v
        goal = SQ.elimProp (λ _ → isSetEl _ _ _) (λ a → cong (λ a → QuotIso _ _ .inv [ a ]) (e a))

    -- `quotMap` of a map that is pointwise a composite is the composite
    quotMap-seq : {X Y Z : U} {RX : El X → El X → U} {RY : El Y → El Y → U} {RZ : El Z → El Z → U}
                  {g₁ : El X → El Y} {h₁ : Preserves RX RY g₁}
                  {g₂ : El Y → El Z} {h₂ : Preserves RY RZ g₂}
                  {g : El X → El Z} {h : Preserves RX RZ g}
                → ((a : El X) → g a ≡ g₂ (g₁ a))
                → ----------------------------------------------------------------------
                  (u : El (Quot X RX)) → quotMap g h u ≡ quotMap g₂ h₂ (quotMap g₁ h₁ u)
    quotMap-seq {g₁ = g₁} {h₁} {g₂} {h₂} {g} {h} e u = goal (QuotIso _ _ .fun u)
      where
        goal : (v : _) → QuotIso _ _ .inv (quotMap/ g h v)
                       ≡ quotMap g₂ h₂ (QuotIso _ _ .inv (quotMap/ g₁ h₁ v))
        goal = SQ.elimProp (λ _ → isSetEl _ _ _) (λ a →
          cong (λ c → QuotIso _ _ .inv [ c ]) (e a) ∙ sym (quotMap-class g₂ h₂ (g₁ a)))

    -- | Quotients, fibrewise over a base `X`: `Q x` is the quotient of `A x`
    -- by `rel x`, and `cls` takes the class of the second component of a pair.
    module QuotFibres {X : U} (A : El X → U) (rel : (x : El X) → El (A x) → El (A x) → U) where

      Q : El X → U
      Q x = Quot (A x) (rel x)

      -- the class of the second component
      cls : El (Sigma X A) → El (Sigma X Q)
      cls w = pairSigma (fstSigma w) (classQuot (sndSigma w))

      -- `cls` of a canonical pair is the canonical pair with the class
      cls-pair : (x : El X) (a : El (A x)) → cls (pairSigma x a) ≡ pairSigma x (classQuot a)
      cls-pair x a i = pairSigma {B = Q} (fstPairSigma {B = A} x a i) (classQuot (sndPairSigma {B = A} x a i))

      -- related elements have equal classes
      cls-eq : (x : El X) (a b : El (A x)) → El (rel x a b) → cls (pairSigma x a) ≡ cls (pairSigma x b)
      cls-eq x a b r = cls-pair x a ∙∙ cong (pairSigma x) (classQuot≡ a b r) ∙∙ sym (cls-pair x b)

      -- every element is merely a class
      cls-surj : (s : El (Sigma X Q)) → ∥ fiber cls s ∥₁
      cls-surj s = PT.map (λ (a , [a]≡) → pairSigma x a ,
                              cls-pair x a
                            ∙ cong (λ v → pairSigma x (QuotIso _ _ .inv v)) [a]≡
                            ∙ cong (pairSigma x) (QuotIso _ _ .ret u)
                            ∙ ηSigma s)
                          (SQ.[]surjective (QuotIso _ _ .fun u))
        where
          x = fstSigma s
          u = sndSigma s

      module _ (P : El (Sigma X Q) → U) where

        -- `m` respects the relation: its values at related elements agree
        Respects : ((w : El (Sigma X A)) → El (P (cls w))) → Type ℓEl
        Respects m = (x : El X) (a b : El (A x)) (r : El (rel x a b))
                   → PathP (λ i → El (P (cls-eq x a b r i))) (m (pairSigma x a)) (m (pairSigma x b))

        -- two sections agreeing on classes agree
        cls-ext : (t t' : (s : El (Sigma X Q)) → El (P s))
                → ((w : El (Sigma X A)) → t (cls w) ≡ t' (cls w))
                → t ≡ t'
        cls-ext t t' h = funExt λ s →
          PT.rec (isSetEl (P s) _ _) (λ (w , cw≡s) → subst (λ s → t s ≡ t' s) cw≡s (h w)) (cls-surj s)

        module _ (m : (w : El (Sigma X A)) → El (P (cls w))) (resp : Respects m) where

          -- the eliminator on the set quotient in the fibre over `x` (`elimQ`), and on its code (`elimFib`)
          private
            elimQ : (x : El X) (v : El (A x) / (λ a b → El (rel x a b)))
                  → El (P (pairSigma x (QuotIso _ _ .inv v)))
            elimQ x = SQ.elim (λ v → isSetEl (P (pairSigma x (QuotIso _ _ .inv v))))
              (λ a → subst (λ s → El (P s)) (cls-pair x a) (m (pairSigma x a)))
              (λ a b r → over P (symO (substO P (cls-pair x a) (m (pairSigma x a)))
                                 ∙O overPath (cls-eq x a b r) (resp x a b r)
                                 ∙O substO P (cls-pair x b) (m (pairSigma x b)))
                                (λ i → pairSigma x (QuotIso _ _ .inv (eq/ a b r i))))

            elimFib : (x : El X) (u : El (Q x)) → El (P (pairSigma x u))
            elimFib x u = subst (λ u → El (P (pairSigma x u))) (QuotIso _ _ .ret u) (elimQ x (QuotIso _ _ .fun u))

          -- | The eliminator, and its β-law.
          elim : (s : El (Sigma X Q)) → El (P s)
          elim s = subst (λ s → El (P s)) (ηSigma s) (elimFib (fstSigma s) (sndSigma s))

          -- `elimFib` at a class is `m` at the canonical pair
          private
            elimFib-class : (x : El X) (a : El (A x)) → Over P (elimFib x (classQuot a)) (m (pairSigma x a))
            elimFib-class x a =
                symO (substO P (λ i → pairSigma x (QuotIso _ _ .ret (classQuot a) i))
                             (elimQ x (QuotIso _ _ .fun (classQuot a))))
              ∙O overPath (λ i → pairSigma x (QuotIso _ _ .inv (QuotIso _ _ .sec [ a ] i)))
                          (λ i → elimQ x (QuotIso _ _ .sec [ a ] i))
              ∙O symO (substO P (cls-pair x a) (m (pairSigma x a)))

          elim-β : (w : El (Sigma X A)) → elim (cls w) ≡ m w
          elim-β w = over≡ P
            ( symO (substO P (ηSigma (cls w)) (elimFib (fstSigma (cls w)) (sndSigma (cls w))))
            ∙O overPath (λ i → pairSigma (fstPairSigma {B = Q} x c i) (sndPairSigma {B = Q} x c i))
                        (λ i → elimFib (fstPairSigma {B = Q} x c i) (sndPairSigma {B = Q} x c i))
            ∙O elimFib-class x (sndSigma w)
            ∙O congO P m (ηSigma w))
            where
              x = fstSigma w
              c = classQuot {R = rel x} (sndSigma w)

        -- the η-law: a section is the eliminator of its restriction to classes
        elim-η : (t : (s : El (Sigma X Q)) → El (P s)) (resp : Respects (λ w → t (cls w)))
               → ---------------------------------------------------------------
                 elim (λ w → t (cls w)) resp ≡ t
        elim-η t resp = cls-ext (elim (λ w → t (cls w)) resp) t (elim-β (λ w → t (cls w)) resp)

    -- | The relation is a code `R` over two variables: the context
    -- `X ▹ A ▹ A [ p ] ▹ R` with its projections to the first and to the
    -- second variable, whose classes agree.
    module QuotRel {X : U} (A : El X → U) (R : El (Sigma² A) → U) where
      open QuotFibres A (λ x a b → R (pair² A (x , a , b))) public

      RelCtx : U
      RelCtx = Sigma (Sigma² A) R

      fstVar sndVar : El RelCtx → El (Sigma X A)
      fstVar z = fstSigma (fstSigma z)
      sndVar z = pairSigma (fstSigma (fstSigma (fstSigma z))) (sndSigma (fstSigma z))

      cls-sound : (z : El RelCtx) → cls (fstVar z) ≡ cls (sndVar z)
      cls-sound z =
          cong cls (sym (ηSigma (fstSigma (fstSigma z))))
        ∙ cls-eq _ _ _ (subst (λ w → El (R w)) (sym (pair²-unpair² A (fstSigma z))) (sndSigma z))

      -- a map that respects `R` at every element of `RelCtx` respects it at
      -- every related pair (`Respects`)
      toRespects : (P : El (Sigma X Q) → U) (m : (w : El (Sigma X A)) → El (P (cls w)))
                 → ((z : El RelCtx) → PathP (λ i → El (P (cls-sound z i))) (m (fstVar z)) (m (sndVar z)))
                 → ---------------------------------------------------------------------------------
                   Respects P m
      toRespects P m resp x a b r =
        over P (congO P m (sym e₁) ∙O overPath (cls-sound z) (resp z) ∙O congO P m e₂) (cls-eq x a b r)
        where
          z = pairSigma {B = R} (pair² A (x , a , b)) r
          e₁ : fstVar z ≡ pairSigma x a
          e₁ = cong fstSigma (fstPairSigma {B = R} _ r) ∙ fstPairSigma {B = λ s → A (fstSigma s)} _ _
          e₂ : sndVar z ≡ pairSigma x b
          e₂ =  cong (λ w → pairSigma {B = A} (fstSigma (fstSigma w)) (sndSigma w)) (fstPairSigma {B = R} _ r)
              ∙ cong (λ t → pairSigma {B = A} (t .fst) (t .snd .snd)) (unpair²-pair² A (x , a , b))
