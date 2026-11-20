module Utils.TarskiQuotient where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv using (isEquiv ; fiber)
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT using (∥_∥₁ ; ∣_∣₁)
open import Cubical.HITs.SetQuotients as SQ using (_/_ ; [_] ; eq/)

open import TarskiUniverse.Base

open Iso

-- | Set quotients in a Tarski universe, fibrewise over a base: the common
-- core of the quotient types in the families model (`ACwF.Instances.
-- TarskiUniverse`) and, stage by stage, in the presheaf model
-- (`ACwF.Instances.TarskiPresheaf.Quotient`).  Contexts there are iterated
-- `Sigma`s, so a variable of a quotient over a base `X` is an element of
-- `Sigma X (λ x → Quot (A x) (rel x))`, and elimination is a statement about
-- functions out of it.
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

    -- moving along a path of the base
    substO : {x y : El X} (e : x ≡ y) (u : El (F x)) → Over F u (subst (λ x → El (F x)) e u)
    substO e u = overPath e (subst-filler (λ x → El (F x)) e u)

  -- | Two variables of type `A` over a point of `X`: the context
  -- `X ▹ A ▹ A [ p ]` as a code, and its elements as triples.  The third
  -- component has to be moved along the β-law of the inner pair.
  module _ {X : U} (A : El X → U) where

    Sigma² : U
    Sigma² = Sigma (Sigma X A) (λ s → A (fstSigma s))

    Two : Type ℓEl
    Two = Σ[ x ∈ El X ] El (A x) × El (A x)

    pair² : Two → El Sigma²
    pair² (x , a , b) = pairSigma (pairSigma x a) (subst (λ y → El (A y)) (sym (fstPairSigma x a)) b)

    unpair² : El Sigma² → Two
    unpair² w = fstSigma (fstSigma w) , sndSigma (fstSigma w) , sndSigma w

    unpair²-pair² : (t : Two) → unpair² (pair² t) ≡ t
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

    pair²-unpair² : (w : El Sigma²) → pair² (unpair² w) ≡ w
    pair²-unpair² w =
      pairSigma≡ (ηSigma (fstSigma w))
        (over A (symO (substO A (sym (fstPairSigma (fstSigma (fstSigma w)) (sndSigma (fstSigma w)))) (sndSigma w)))
                (cong fstSigma (ηSigma (fstSigma w))))

  -- | Quotients, fibrewise over a base `X`.
  module _ (TU-Quot : hasQuotient TU) where
    open hasQuotient TU-Quot

    -- related elements have equal classes
    classQuot≡ : {A : U} {R : El A → El A → U} (a b : El A) → El (R a b)
               → classQuot {R = R} a ≡ classQuot b
    classQuot≡ a b r = cong (QuotIso _ _ .inv) (eq/ a b r)

    module QuotFibres {X : U} (A : El X → U) (rel : (x : El X) → El (A x) → El (A x) → U) where

      Q : El X → U
      Q x = Quot (A x) (rel x)

      -- the class of the second component
      cls : El (Sigma X A) → El (Sigma X Q)
      cls w = pairSigma (fstSigma w) (classQuot (sndSigma w))

      -- on a canonical pair
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

          -- in the fibre over `x`, on the set quotient
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

        -- | Precomposition with `cls` is an equivalence onto the respecting
        -- maps, for any propositional notion of respecting that implies
        -- `Respects`.  (Stated for an arbitrary `f` whose first component is
        -- precomposition, so that a model can pass its own `QuotCases`.)
        isEquivPrecompCls : (Resp : ((w : El (Sigma X A)) → El (P (cls w))) → Type ℓEl)
                            (isPropResp : (m : (w : El (Sigma X A)) → El (P (cls w))) → isProp (Resp m))
                            (toRespects : (m : (w : El (Sigma X A)) → El (P (cls w))) → Resp m → Respects m)
                            (f : ((s : El (Sigma X Q)) → El (P s)) → Σ ((w : El (Sigma X A)) → El (P (cls w))) Resp)
                          → ((t : (s : El (Sigma X Q)) → El (P s)) → f t .fst ≡ (λ w → t (cls w)))
                          → ----------------------------------------------------------------------
                            isEquiv f
        isEquivPrecompCls Resp isPropResp toRespects f f≡ = isoToIsEquiv precompIso
          where
            precompIso : Iso _ _
            precompIso .fun         = f
            precompIso .inv (m , r) = elim m (toRespects m r)
            precompIso .sec (m , r) = Σ≡Prop isPropResp (f≡ _ ∙ funExt (elim-β m (toRespects m r)))
            precompIso .ret t       = cls-ext (elim (f t .fst) (toRespects _ (f t .snd))) t
              (λ w → elim-β (f t .fst) (toRespects _ (f t .snd)) w ∙ funExt⁻ (f≡ t) w)

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

      -- respecting `R` at each element of `RelCtx` is respecting it at each
      -- related pair: instantiate at the re-paired pair
      toRespects : (P : El (Sigma X Q) → U) (m : (w : El (Sigma X A)) → El (P (cls w)))
                 → ((z : El RelCtx) → PathP (λ i → El (P (cls-sound z i))) (m (fstVar z)) (m (sndVar z)))
                 → ---------------------------------------------------------------------------------
                   Respects P m
      toRespects P m r x a b rel =
        over P (congO P m (sym e₁) ∙O overPath (cls-sound z) (r z) ∙O congO P m e₂) (cls-eq x a b rel)
        where
          z = pairSigma {B = R} (pair² A (x , a , b)) rel
          e₁ : fstVar z ≡ pairSigma x a
          e₁ = cong fstSigma (fstPairSigma {B = R} _ rel) ∙ fstPairSigma {B = λ s → A (fstSigma s)} _ _
          e₂ : sndVar z ≡ pairSigma x b
          e₂ =  cong (λ w → pairSigma {B = A} (fstSigma (fstSigma w)) (sndSigma w)) (fstPairSigma {B = R} _ rel)
              ∙ cong (λ t → pairSigma {B = A} (t .fst) (t .snd .snd)) (unpair²-pair² A (x , a , b))
