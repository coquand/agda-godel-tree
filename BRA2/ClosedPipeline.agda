{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA2.ClosedPipeline -- end-to-end certified transformation
--   IndBTPackageAt Target  +  Eq (substEq zero O pkgE) pkgE  -->  DerivT0 Target
--
-- For any indBTB package whose underlying equation is closed in
-- var 0  (i.e.  substEq zero O pkgE = pkgE  by computation), the
-- premise  pkgBase : DerivT0 (atomic (substEq zero O pkgE))  IS
-- already a derivation of  atomic pkgE .  The eliminator's step
-- machinery is unnecessary: the indBT collapses to its base case,
-- which is plugged through the structural-rule path  pkgCtx  to
-- reach the eventual target.
--
-- This is the Case-B-finishing companion to BRA2.FindIndBT: every
-- pkg produced by  findIndBT  on a wrapped indBTB whose pkgE
-- happens to be closed (which is the typical configuration when
-- the wrapping eventually produces  bot  via paths that don't
-- introduce free variables) reduces to  DerivT0 bot  via this
-- handler.
--
-- For our two synthetic smoke-test scenarios:
--
--   * (C/E) input pkgE = botEqn = eqn O (Pair O O) — closed; refl
--           witnesses substEq zero O botEqn = botEqn.
--   * (D)   input pkgE = swappedBotEqn = eqn (Pair O O) O — closed;
--           refl witnesses substEq zero O swappedBotEqn = swappedBotEqn.
--
-- Both witnesses hold by computation.  The handler thus completes
-- the pipeline for these scenarios without invoking the demand-
-- equation extractor at all.
--
-- Open: pkgE with var 0 free.  Then substEq zero O pkgE != pkgE
-- (in general); the eliminator's step machinery is needed to
-- derive  DerivT0 (atomic (substEq zero t pkgE))  for some chosen
-- value t  whose substitution composes with pkgCtx to give the
-- target.  That's the doc's Case C territory and is deferred.

module BRA2.ClosedPipeline where

open import BRA2.Base
open import BRA2.Term
open import BRA2.Formula
import BRA2.DerivT0       as O
import BRA2.DerivTBounded as B
open import BRA2.DerivT0 using (bot)
open import BRA2.DerivTBounded using (DerivTBounded)
open import BRA2.IndBTContext0 using (IndBTContext0 ; plug0)
open import BRA2.FindIndBT using
  (IndBTPackageAt ; pkgE ; pkgV1 ; pkgV2 ; pkgWF
  ; pkgBase ; pkgStep ; pkgCtx
  ; IndBTPackage ; Or ; inl ; inr ; findIndBT)
open import BRA2.ExtractDemand using (Maybe ; just ; nothing)

------------------------------------------------------------------------
-- The core transform.

closedPipeline :
  {Target : Formula} ->
  (pkg : IndBTPackageAt Target) ->
  Eq (substEq zero O (pkgE pkg)) (pkgE pkg) ->
  O.DerivT0 Target
closedPipeline pkg inert =
  plug0 (pkgCtx pkg)
         (eqSubst (\ E -> O.DerivT0 (atomic E)) inert (pkgBase pkg))

------------------------------------------------------------------------
-- ClosedOracle: a partial decision procedure recognising those
-- equations on which we know  substEq zero O e = e .  Returns the
-- propositional witness when it does, nothing otherwise.

ClosedOracle : Set
ClosedOracle =
  (e : Equation) -> Maybe (Eq (substEq zero O e) e)

------------------------------------------------------------------------
-- defaultClosedOracle : recursive structural decision procedure on
-- terms / Fun1 / Fun2 / Equation.  Returns just refl whenever the
-- equation contains no  var 0 .  Conservative: returns nothing on
-- any composite Fun1 / Fun2 constructor whose arity exceeds zero
-- (Comp / Comp2 / Lift / Post / Fan / treeRec) -- closure of those
-- requires recursing INTO the Fun, which is sound but adds another
-- mutually-recursive layer.  The atomic Fun1 / Fun2 constructors
-- (I / Fst / Snd / Z / Pair / Const / IfLf / TreeEq) are recognised
-- as closed.  This covers the vast majority of equations arising
-- from value-shape closures.

defaultClosedFun1 : (f : Fun1) -> Maybe (Eq (substF1 zero O f) f)
defaultClosedFun1 I             = just refl
defaultClosedFun1 Fst           = just refl
defaultClosedFun1 Snd           = just refl
defaultClosedFun1 Z             = just refl
defaultClosedFun1 (Comp _ _)    = nothing
defaultClosedFun1 (Comp2 _ _ _) = nothing

defaultClosedFun2 : (g : Fun2) -> Maybe (Eq (substF2 zero O g) g)
defaultClosedFun2 Pair          = just refl
defaultClosedFun2 Const         = just refl
defaultClosedFun2 IfLf          = just refl
defaultClosedFun2 TreeEq        = just refl
defaultClosedFun2 (Lift _)      = nothing
defaultClosedFun2 (Post _ _)    = nothing
defaultClosedFun2 (Fan _ _ _)   = nothing
defaultClosedFun2 (treeRec _ _) = nothing

defaultClosedAp1 :
  (f : Fun1) {t : Term} ->
  Maybe (Eq (substF1 zero O f) f) ->
  Maybe (Eq (subst zero O t) t) ->
  Maybe (Eq (subst zero O (ap1 f t)) (ap1 f t))
defaultClosedAp1 _ nothing    _         = nothing
defaultClosedAp1 _ (just _)   nothing   = nothing
defaultClosedAp1 _ (just pf)  (just pt) = just (eqCong2 ap1 pf pt)

defaultClosedAp2 :
  (g : Fun2) {a b : Term} ->
  Maybe (Eq (substF2 zero O g) g) ->
  Maybe (Eq (subst zero O a) a) ->
  Maybe (Eq (subst zero O b) b) ->
  Maybe (Eq (subst zero O (ap2 g a b)) (ap2 g a b))
defaultClosedAp2 _ nothing   _         _         = nothing
defaultClosedAp2 _ (just _)  nothing   _         = nothing
defaultClosedAp2 _ (just _)  (just _)  nothing   = nothing
defaultClosedAp2 _ (just pg) (just pa) (just pb) = just (eqCong3 ap2 pg pa pb)

defaultClosedTerm : (t : Term) -> Maybe (Eq (subst zero O t) t)
defaultClosedTerm O             = just refl
defaultClosedTerm (var zero)    = nothing
defaultClosedTerm (var (suc _)) = just refl
defaultClosedTerm (ap1 f t)     =
  defaultClosedAp1 f (defaultClosedFun1 f) (defaultClosedTerm t)
defaultClosedTerm (ap2 g a b)   =
  defaultClosedAp2 g (defaultClosedFun2 g)
                     (defaultClosedTerm a) (defaultClosedTerm b)

defaultClosedEqn :
  {l r : Term} ->
  Maybe (Eq (subst zero O l) l) ->
  Maybe (Eq (subst zero O r) r) ->
  Maybe (Eq (substEq zero O (eqn l r)) (eqn l r))
defaultClosedEqn nothing   _         = nothing
defaultClosedEqn (just _)  nothing   = nothing
defaultClosedEqn (just pl) (just pr) = just (eqCong2 eqn pl pr)

defaultClosedOracle : ClosedOracle
defaultClosedOracle (eqn l r) =
  defaultClosedEqn (defaultClosedTerm l) (defaultClosedTerm r)

------------------------------------------------------------------------
-- Bot-target finalizer driven by a ClosedOracle.

closedFinalize :
  ClosedOracle ->
  Maybe (Or (O.DerivT0 bot) IndBTPackage) ->
  Maybe (O.DerivT0 bot)
closedFinalize _      nothing             = nothing
closedFinalize _      (just (inl d0))     = just d0
closedFinalize oracle (just (inr pkg))    =
  closedFinalizeStep oracle pkg (oracle (pkgE pkg))
  where
    closedFinalizeStep :
      ClosedOracle ->
      (pkg : IndBTPackage) ->
      Maybe (Eq (substEq zero O (pkgE pkg)) (pkgE pkg)) ->
      Maybe (O.DerivT0 bot)
    closedFinalizeStep _ _   nothing      = nothing
    closedFinalizeStep _ pkg (just inert) = just (closedPipeline pkg inert)

------------------------------------------------------------------------
-- Top-level pipeline:  DerivTBounded 1 l bot --> Maybe (DerivT0 bot)
-- driven by a ClosedOracle.  Composes  findIndBT  with
-- closedFinalize.

closedPipelineFromBounded :
  ClosedOracle ->
  {l : Nat} -> DerivTBounded (suc zero) l bot ->
  Maybe (O.DerivT0 bot)
closedPipelineFromBounded oracle d = closedFinalize oracle (findIndBT d)
