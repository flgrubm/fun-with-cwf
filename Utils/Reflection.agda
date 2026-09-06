-- Generic reflection utilities.  Nothing here mentions Tarski universes; it is
-- the part of TarskiUniverse.Solver that the cubical library happens not to
-- provide.
module Utils.Reflection where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool.Base
open import Cubical.Data.List.Base
open import Cubical.Data.Maybe.Base
open import Cubical.Data.Nat.Base

import Agda.Builtin.Reflection as R
open import Agda.Builtin.Reflection using (primQNameEquality)

open import Cubical.Reflection.Base

--------------------------------------------------------------------------------
-- Weakening
--
-- `raise n t` shifts every *free* de Bruijn index of `t` up by `n`, leaving the
-- variables bound inside `t` alone.  A macro's arguments live in the context of
-- the goal, so they have to be raised before being reused underneath a binder
-- that the macro itself introduces.  The cubical library has no such helper:
-- `Cubical.Tactics.MonoidSolver.Reflection.adjustDeBruijnIndex` only handles a
-- bare `var` and maps everything else to `unknown`.

raiseFrom      : ℕ → ℕ → R.Term → R.Term
raiseFromSort  : ℕ → ℕ → R.Sort → R.Sort
raiseFromArgs  : ℕ → ℕ → List (R.Arg R.Term) → List (R.Arg R.Term)
raiseFromCl    : ℕ → ℕ → R.Clause → R.Clause
raiseFromCls   : ℕ → ℕ → List R.Clause → List R.Clause
raiseFromTel   : ℕ → ℕ → R.Telescope → R.Telescope
raiseFromPat   : ℕ → ℕ → R.Pattern → R.Pattern
raiseFromPats  : ℕ → ℕ → List (R.Arg R.Pattern) → List (R.Arg R.Pattern)

raiseFrom c n (R.var x args)     = R.var (if x <ᵇ c then x else x + n) (raiseFromArgs c n args)
raiseFrom c n (R.con f args)     = R.con f (raiseFromArgs c n args)
raiseFrom c n (R.def f args)     = R.def f (raiseFromArgs c n args)
raiseFrom c n (R.lam v (R.abs s t)) = R.lam v (R.abs s (raiseFrom (suc c) n t))
raiseFrom c n (R.pat-lam cs args) = R.pat-lam (raiseFromCls c n cs) (raiseFromArgs c n args)
raiseFrom c n (R.pi (R.arg i a) (R.abs s b)) =
  R.pi (R.arg i (raiseFrom c n a)) (R.abs s (raiseFrom (suc c) n b))
raiseFrom c n (R.agda-sort s)    = R.agda-sort (raiseFromSort c n s)
raiseFrom c n (R.lit l)          = R.lit l
raiseFrom c n (R.meta x args)    = R.meta x (raiseFromArgs c n args)
raiseFrom c n R.unknown          = R.unknown

raiseFromSort c n (R.set t)     = R.set (raiseFrom c n t)
raiseFromSort c n (R.lit k)     = R.lit k
raiseFromSort c n (R.prop t)    = R.prop (raiseFrom c n t)
raiseFromSort c n (R.propLit k) = R.propLit k
raiseFromSort c n (R.inf k)     = R.inf k
raiseFromSort c n R.unknown     = R.unknown

raiseFromArgs c n []                = []
raiseFromArgs c n (R.arg i t ∷ as)  = R.arg i (raiseFrom c n t) ∷ raiseFromArgs c n as

raiseFromCls c n []       = []
raiseFromCls c n (x ∷ xs) = raiseFromCl c n x ∷ raiseFromCls c n xs

-- A clause's patterns and body live under the variables bound by its telescope.
raiseFromCl c n (R.clause tel ps t) =
  R.clause (raiseFromTel c n tel)
           (raiseFromPats (c + length tel) n ps)
           (raiseFrom (c + length tel) n t)
raiseFromCl c n (R.absurd-clause tel ps) =
  R.absurd-clause (raiseFromTel c n tel) (raiseFromPats (c + length tel) n ps)

raiseFromTel c n []                    = []
raiseFromTel c n ((s , R.arg i t) ∷ tel) =
  (s , R.arg i (raiseFrom c n t)) ∷ raiseFromTel (suc c) n tel

raiseFromPat c n (R.con f ps) = R.con f (raiseFromPats c n ps)
raiseFromPat c n (R.dot t)    = R.dot (raiseFrom c n t)
raiseFromPat c n (R.var x)    = R.var x
raiseFromPat c n (R.lit l)    = R.lit l
raiseFromPat c n (R.proj f)   = R.proj f
raiseFromPat c n (R.absurd x) = R.absurd x

raiseFromPats c n []               = []
raiseFromPats c n (R.arg i p ∷ ps) = R.arg i (raiseFromPat c n p) ∷ raiseFromPats c n ps

raise : ℕ → R.Term → R.Term
raise = raiseFrom 0

--------------------------------------------------------------------------------
-- Building and taking apart applications
--
-- Record parameters are implicit in projections, and definitions in
-- parameterised modules pick up the module telescope, so counting hidden
-- arguments by hand is both tedious and fragile.  These helpers work with the
-- *visible* arguments only.

visibleArgs : List (R.Arg R.Term) → List R.Term
visibleArgs [] = []
visibleArgs (R.arg (R.arg-info R.visible _) t ∷ as) = t ∷ visibleArgs as
visibleArgs (_ ∷ as) = visibleArgs as

-- `matchDef f t` succeeds when `t` is an application of `f`, returning its
-- visible arguments.
matchDef : R.Name → R.Term → Maybe (List R.Term)
matchDef f (R.def g args) = if primQNameEquality f g then just (visibleArgs args) else nothing
matchDef f _ = nothing

matchCon : R.Name → R.Term → Maybe (List R.Term)
matchCon f (R.con g args) = if primQNameEquality f g then just (visibleArgs args) else nothing
matchCon f _ = nothing

private
  -- Walk the telescope of `f`, filling hidden and instance positions with
  -- `unknown` and taking the visible ones from `ts`.
  fillArgs : R.Type → List R.Term → List (R.Arg R.Term)
  fillArgs (R.pi (R.arg i@(R.arg-info R.visible _) _) (R.abs _ b)) (t ∷ ts) = R.arg i t ∷ fillArgs b ts
  fillArgs (R.pi (R.arg   (R.arg-info R.visible _) _) (R.abs _ b)) []       = []
  fillArgs (R.pi (R.arg i                          _) (R.abs _ b)) ts       = R.arg i R.unknown ∷ fillArgs b ts
  fillArgs _ ts = map varg ts

-- `mkApp f ts` applies `f` to the visible arguments `ts`, inserting `unknown`
-- for every implicit argument in between.
mkApp : R.Name → List R.Term → R.TC R.Term
mkApp f ts = R.getType f >>= λ ty → R.returnTC (R.def f (fillArgs ty ts))

-- Append one argument to an application.  There is no application node in
-- `Term`, so this only works for the head forms that carry an argument list --
-- which is all a macro argument can elaborate to in practice.
applyTerm : R.Term → R.Arg R.Term → Maybe R.Term
applyTerm (R.var x args)      a = just (R.var x (args ++ [ a ]))
applyTerm (R.con f args)      a = just (R.con f (args ++ [ a ]))
applyTerm (R.def f args)      a = just (R.def f (args ++ [ a ]))
applyTerm (R.meta x args)     a = just (R.meta x (args ++ [ a ]))
applyTerm (R.pat-lam cs args) a = just (R.pat-lam cs (args ++ [ a ]))
applyTerm _                   a = nothing

-- The conclusion of a (possibly dependent) function type.  The result lives
-- underneath the binders it was stripped from, so only its head is meaningful
-- -- which is all a classification by head symbol needs.
conclusion : ℕ → R.Term → R.Term
conclusion zero    t                    = t
conclusion (suc n) (R.pi _ (R.abs _ b)) = conclusion n b
conclusion (suc n) t                    = t
