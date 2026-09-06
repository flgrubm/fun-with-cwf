-- A reflection solver for `TU hasCodeFor X`.
--
-- The five introduction rules of `TarskiUniverse.Properties` are syntax
-- directed on the type `X`, so building a code by hand is pure drudgery.  The
-- macro `solveCode` reads the goal, decomposes `X`, and emits the nested rule
-- applications:
--
--   Σ A B          ->  _hasCodeForΣ      (needs a `hasSigma TU` hint)
--   (x : A) → B x  ->  _hasCodeForΠ      (needs a `hasPi TU` hint)
--   a ≡ b          ->  _hasCodeForEq     (needs a `hasEq TU` hint)
--   Unit           ->  _hasCodeForUnit   (needs a `hasUnit TU` hint)
--   El a           ->  _hasCodeForEl
--
-- Recursion bottoms out at types that are not built from these -- `C .ob`,
-- `C [ x , y ]` -- whose codes have to come from elsewhere.  Those, and the
-- structure witnesses above, are passed to the macro as one `◂`-separated list:
--
--   ∫-Coded .isSmallOb      = solveCode (hasSigmaTU ◂ coded .isSmallOb ◂ ε)
--   ∫-Coded .isSmallHom x y = solveCode (hasSigmaTU ◂ hasEqTU ◂ coded .isSmallHom ◂ ε)
--
-- A hint may be Π-shaped (`∀ x y → TU hasCodeFor (C [ x , y ])`); it is applied
-- to metavariables and its conclusion unified with the goal, so it behaves like
-- a one-step instance search.  Hints are tried *before* the structural rules,
-- so a hint on an abstract atom is never defeated by that atom happening to
-- reduce to a Σ.
--
-- Instance search would not do: it matches on a head `Name`, and a Π type has
-- none, so `_hasCodeForΠ` could never be an instance.
--
-- One caveat, inherent to macros rather than to this one: a macro's arguments
-- are elaborated *before* it runs, so a hint that still has an unsolved
-- metavariable in it -- typically the universe level of a level-polymorphic
-- definition, which nothing in the hint list can determine -- blocks the macro.
-- Give such a hint its level explicitly (`hasSigmaU {ℓ}`).
module TarskiUniverse.Solver where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool.Base
open import Cubical.Data.List.Base
open import Cubical.Data.Maybe.Base
open import Cubical.Data.Nat.Base
open import Cubical.Data.Sigma.Base
open import Cubical.Data.Unit.Base
open import Agda.Builtin.String using (String)

import Agda.Builtin.Reflection as R
open import Agda.Builtin.Reflection using (primQNameEquality)

open import Cubical.Reflection.Base
open import Utils.Reflection

open import TarskiUniverse.Base
open import TarskiUniverse.Properties

-- Hints are handed to the macro as a `◂`-separated list.  A nested tuple will
-- not do: elaborating `h₁ , h₂ , h₃` against an unknown type leaves the second
-- component's family undetermined and the whole argument gets stuck.  `_◂_`
-- sidesteps that -- every hint carries its own implicit level and type, and the
-- result type is always the same closed `HintList`.
data HintList : Type where
  ε : HintList

infixr 5 _◂_

_◂_ : ∀ {ℓ} {A : Type ℓ} → A → HintList → HintList
_ ◂ hs = hs

private
  isJust : {A : Type} → Maybe A → Bool
  isJust (just _) = true
  isJust nothing  = false

  --------------------------------------------------------------------------
  -- Hints

  record Hints : Type where
    constructor mkHints
    field
      sigmaH piH eqH unitH : Maybe R.Term
      atoms                : List R.Term

  noHints : Hints
  noHints = mkHints nothing nothing nothing nothing []

  raiseHints : ℕ → Hints → Hints
  raiseHints n (mkHints s p e u as) =
    mkHints (map-Maybe (raise n) s) (map-Maybe (raise n) p)
            (map-Maybe (raise n) e) (map-Maybe (raise n) u)
            (map (raise n) as)

  -- Split the macro's argument at its `◂`s.  A lone hint needs no `ε`, so
  -- `solveCode ε`, `solveCode h` and `solveCode (h₁ ◂ h₂ ◂ ε)` all work.
  peelHints : ℕ → R.Term → List R.Term
  peelHintsStep : ℕ → R.Term → Maybe (List R.Term) → List R.Term

  peelHints zero    t = [ t ]
  peelHints (suc n) t = peelHintsStep n t (matchDef (quote _◂_) t)

  peelHintsStep n t (just (h ∷ rest ∷ [])) = h ∷ peelHints n rest
  peelHintsStep n t _ = if isJust (matchCon (quote ε) t) then [] else [ t ]

  addHint : R.Term → R.Term → Hints → Hints
  addHint h ty hs =
    if hasHead (quote hasSigma) then record hs { sigmaH = just h } else
    if hasHead (quote hasPi)    then record hs { piH    = just h } else
    if hasHead (quote hasEq)    then record hs { eqH    = just h } else
    if hasHead (quote hasUnit)  then record hs { unitH  = just h } else
    record hs { atoms = Hints.atoms hs ++ [ h ] }
    where
      hasHead : R.Name → Bool
      hasHead f = isJust (matchDef f (conclusion 50 ty))

  --------------------------------------------------------------------------
  -- Reduction that keeps the two definitions the solver matches on folded.
  -- `_hasCodeFor_` would unfold to a Σ and `El` to whatever the universe
  -- decodes to, destroying exactly the information we are matching on.

  reduceKeep : R.Term → R.TC R.Term
  reduceKeep t =
    R.withReduceDefs (false , (quote _hasCodeFor_ ∷ quote BareTarskiUniverse.El ∷ []))
                     (R.reduce t)

  classify : Hints → R.Term → R.TC Hints
  classify hs h = R.inferType h >>= reduceKeep >>= λ ty → R.returnTC (addHint h ty hs)

  classifyAll : Hints → List R.Term → R.TC Hints
  classifyAll hs []       = R.returnTC hs
  classifyAll hs (h ∷ tl) = classify hs h >>= λ hs' → classifyAll hs' tl

  --------------------------------------------------------------------------
  -- The goal

  getGoal : R.Term → R.TC (R.Term × R.Term)
  getGoal goal = go (matchDef (quote _hasCodeFor_) goal)
    where
      fail : R.TC (R.Term × R.Term)
      fail = R.typeError ( R.strErr "solveCode: the goal is not of the form `TU hasCodeFor X`:"
                         ∷ R.termErr goal ∷ [])
      retry : Maybe (List R.Term) → R.TC (R.Term × R.Term)
      retry (just (TU ∷ X ∷ [])) = R.returnTC (TU , X)
      retry _ = fail
      go : Maybe (List R.Term) → R.TC (R.Term × R.Term)
      go (just (TU ∷ X ∷ [])) = R.returnTC (TU , X)
      go _ = reduceKeep goal >>= λ g → retry (matchDef (quote _hasCodeFor_) g)

  --------------------------------------------------------------------------
  -- Hint resolution: instantiate a hint's leading arguments with
  -- metavariables until its type is a `hasCodeFor`, then match the conclusion.

  -- A failed attempt must *throw*, not report failure: only then does the
  -- surrounding `catchTC` in `tryHints` roll the state back and discard the
  -- metavariables the attempt created.  Returning `nothing` instead would leave
  -- them behind as unsolved metas of the enclosing definition.
  tryHint      : ℕ → R.Term → R.Term → R.Term → R.TC R.Term
  tryHintStep  : ℕ → R.Term → R.Term → R.Term → R.Term → R.TC R.Term
  tryHintApply : ℕ → R.Term → R.Term → Maybe R.Term → R.TC R.Term
  tryHintConcl : R.Term → R.Term → R.Term → Maybe (List R.Term) → R.TC R.Term

  tryHint zero    TU X h = R.typeError (R.strErr "solveCode: hint takes too many arguments" ∷ [])
  tryHint (suc n) TU X h = R.inferType h >>= reduceKeep >>= tryHintStep n TU X h

  tryHintStep n TU X h (R.pi (R.arg i dom) (R.abs _ _)) =
    newMeta dom >>= λ m → tryHintApply n TU X (applyTerm h (R.arg i m))
  tryHintStep n TU X h ty = tryHintConcl TU X h (matchDef (quote _hasCodeFor_) ty)

  tryHintApply n TU X (just h) = tryHint n TU X h
  tryHintApply n TU X nothing  =
    R.typeError (R.strErr "solveCode: this hint cannot be applied to an argument" ∷ [])

  tryHintConcl TU X h (just (TU' ∷ Y ∷ [])) =
    R.noConstraints (R.unify TU' TU >> R.unify Y X) >> R.returnTC h
  tryHintConcl TU X h _ =
    R.typeError (R.strErr "solveCode: this hint does not conclude in `hasCodeFor`" ∷ [])

  tryHints : R.Term → R.Term → List R.Term → R.TC (Maybe R.Term)
  tryHints TU X [] = R.returnTC nothing
  tryHints TU X (h ∷ tl) =
    (tryHint 20 TU X h >>= λ t → R.returnTC (just t)) <|> tryHints TU X tl

  --------------------------------------------------------------------------
  -- The shape of the type being coded

  data Shape : Type where
    isEl    : Shape
    isSigma : Shape
    isPi    : R.Arg R.Type → R.Abs R.Type → Shape
    isEq    : R.Term → R.Term → Shape
    isUnit  : Shape
    isNone  : Shape

  shapeOf : R.Term → Shape
  shapeOf (R.pi a b) = isPi a b
  shapeOf (R.def f args) =
    if primQNameEquality f (quote BareTarskiUniverse.El) then isEl    else
    if primQNameEquality f (quote Σ)                     then isSigma else
    if primQNameEquality f (quote Σ-syntax)              then isSigma else
    if primQNameEquality f (quote Unit)                  then isUnit  else
    if primQNameEquality f (quote _≡_)                   then eqShape (visibleArgs args) else
    isNone
    where
      eqShape : List R.Term → Shape
      eqShape (a ∷ b ∷ []) = isEq a b
      eqShape _ = isNone
  shapeOf _ = isNone

  --------------------------------------------------------------------------
  -- Emitting a rule
  --
  -- `elabRule` builds the application with `unknown` in the recursive
  -- positions, elaborates it against the goal -- which turns those into
  -- metavariables of the right type, in the right context -- unifies it with
  -- the hole, and hands the metavariables back as fresh sub-goals.  This is
  -- what spares us from ever having to weaken a *goal* by hand.

  elabRule : R.Term → R.Term → R.Name → List R.Term → R.TC (List R.Term)
  elabRule goal hole f ts =
    mkApp f ts >>= λ t →
    R.checkType t goal >>= λ t' →
    R.unify hole t' >>
    R.returnTC (argsOf t')
    where
      argsOf : R.Term → List R.Term
      argsOf (R.def _ as) = visibleArgs as
      argsOf _ = []

  missing : {A : Type} → String → R.Term → R.TC A
  missing what X =
    R.typeError ( R.strErr "solveCode: no " ∷ R.strErr what ∷ R.strErr " hint was given, but the goal needs one for "
                ∷ R.termErr X ∷ [])

  -- `El` is a record projection, so in a concrete universe it may already have
  -- computed away by the time the solver sees the goal, and `shapeOf` cannot
  -- recognise it.  Unification recovers those cases: checking `_hasCodeForEl`
  -- against the goal succeeds exactly when `El ?a` can be made to match it.
  tryEl : R.Term → R.Term → R.Term → R.TC Bool
  tryEl goal TU hole =
    ( mkApp (quote _hasCodeForEl) (TU ∷ [])
      >>= λ t → R.noConstraints (R.checkType t goal)
      >>= λ t' → R.unify hole t'
      >> R.returnTC true )
      <|> R.returnTC false

  --------------------------------------------------------------------------
  -- The solver proper

  solve       : ℕ → Hints → R.Term → R.TC Unit
  solveGoal   : ℕ → Hints → R.Term → R.Term → R.Term → R.Term → R.TC Unit
  solveShape  : ℕ → ℕ → Hints → R.Term → R.Term → R.Term → R.Term → Shape → R.TC Unit
  solveSigma  : ℕ → Hints → R.Term → R.Term → R.Term → R.Term → Maybe R.Term → R.TC Unit
  solvePi     : ℕ → Hints → R.Term → R.Term → R.Term → R.Term → Maybe R.Term → R.TC Unit
  solveEq     : ℕ → Hints → R.Term → R.Term → R.Term → R.Term → R.Term → R.Term → Maybe R.Term → R.TC Unit
  solveUnit   : R.Term → R.Term → R.Term → R.Term → Maybe R.Term → R.TC Unit
  solveTwo    : ℕ → Hints → List R.Term → R.TC Unit
  solveUnder  : ℕ → Hints → R.Term → R.TC Unit
  solveUnderPi : ℕ → Hints → R.Term → R.Term → R.TC Unit

  solve zero hs hole = R.typeError (R.strErr "solveCode: out of fuel" ∷ [])
  solve (suc fuel) hs hole =
    R.inferType hole >>= λ goal →
    getGoal goal >>= λ TUX →
    tryHints (fst TUX) (snd TUX) (Hints.atoms hs) >>= λ where
      (just t) → R.unify hole t
      nothing  → solveGoal fuel hs goal (fst TUX) (snd TUX) hole

  solveGoal fuel hs goal TU X hole = solveShape 1 fuel hs goal TU X hole (shapeOf X)

  -- The `red` counter is how many times we may still reduce `X` looking for a
  -- shape.  `R.reduce` gives a weak head normal form, so one is enough.
  solveShape red fuel hs goal TU X hole isEl =
    mkApp (quote _hasCodeForEl) (TU ∷ []) >>= R.unify hole
  solveShape red fuel hs goal TU X hole isSigma =
    solveSigma fuel hs goal TU X hole (Hints.sigmaH hs)
  solveShape red fuel hs goal TU X hole (isPi _ _) =
    solvePi fuel hs goal TU X hole (Hints.piH hs)
  solveShape red fuel hs goal TU X hole (isEq a b) =
    solveEq fuel hs goal TU X a b hole (Hints.eqH hs)
  solveShape red fuel hs goal TU X hole isUnit =
    solveUnit goal TU X hole (Hints.unitH hs)
  solveShape red fuel hs goal TU X hole isNone =
    tryEl goal TU hole >>= λ where
      true  → R.returnTC tt
      false → retry red
    where
      retry : ℕ → R.TC Unit
      retry zero =
        R.typeError ( R.strErr "solveCode: no rule and no hint applies to "
                    ∷ R.termErr X ∷ R.strErr " in goal " ∷ R.termErr goal ∷ [])
      retry (suc k) =
        reduceKeep X >>= λ X' → solveShape k fuel hs goal TU X' hole (shapeOf X')

  solveSigma fuel hs goal TU X hole (just sig) =
    elabRule goal hole (quote _hasCodeForΣ) (TU ∷ sig ∷ R.unknown ∷ R.unknown ∷ [])
      >>= solveTwo fuel hs
  solveSigma fuel hs goal TU X hole nothing = missing "`hasSigma`" X

  solvePi fuel hs goal TU X hole (just piS) =
    elabRule goal hole (quote _hasCodeForΠ) (TU ∷ piS ∷ R.unknown ∷ R.unknown ∷ [])
      >>= solveTwo fuel hs
  solvePi fuel hs goal TU X hole nothing = missing "`hasPi`" X

  -- Only the domain is recursive here: `A` is recovered from the sub-goal.
  solveEq fuel hs goal TU X a b hole (just eq) =
    elabRule goal hole (quote _hasCodeForEq) (TU ∷ a ∷ b ∷ eq ∷ R.unknown ∷ []) >>= λ where
      (_ ∷ _ ∷ _ ∷ _ ∷ cA ∷ []) → solve fuel hs cA
      _ → R.typeError (R.strErr "solveCode: malformed `_hasCodeForEq` application" ∷ [])
  solveEq fuel hs goal TU X a b hole nothing = missing "`hasEq`" X

  solveUnit goal TU X hole (just u) =
    mkApp (quote _hasCodeForUnit) (TU ∷ u ∷ []) >>= R.unify hole
  solveUnit goal TU X hole nothing = missing "`hasUnit`" X

  -- The two recursive arguments shared by the Σ and Π rules: a code for the
  -- domain, and a family of codes for the codomain.
  solveTwo fuel hs (_ ∷ _ ∷ cA ∷ cB ∷ []) = solve fuel hs cA >> solveUnder fuel hs cB
  solveTwo fuel hs _ =
    R.typeError (R.strErr "solveCode: malformed rule application" ∷ [])

  solveUnder fuel hs cB = R.inferType cB >>= reduceKeep >>= solveUnderPi fuel hs cB

  -- `body` is created inside the extended context and only ever appears under
  -- `abs`, so it is well scoped.  The hints, on the other hand, come from the
  -- outer context and must be raised.
  solveUnderPi fuel hs cB (R.pi (R.arg i@(R.arg-info v _) dom) (R.abs s cod)) =
    R.extendContext s (R.arg i dom)
      (newMeta cod >>= λ m → solve fuel (raiseHints 1 hs) m >> R.returnTC m)
      >>= λ body → R.unify cB (R.lam v (R.abs s body))
  solveUnderPi fuel hs cB ty =
    R.typeError ( R.strErr "solveCode: expected a function type for the codomain codes, got"
                ∷ R.termErr ty ∷ [])

  solveMacro : R.Term → R.Term → R.TC Unit
  solveMacro hintArg hole =
    R.withNormalisation false
      (classifyAll noHints (peelHints 100 hintArg) >>= λ hs → solve 1000 hs hole)

macro
  solveCode : R.Term → R.Term → R.TC Unit
  solveCode = solveMacro
