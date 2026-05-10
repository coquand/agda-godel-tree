{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA2.FullPipelineSmoke -- final smoke test composing the entire
-- partial pipeline:
--
--   DerivTBounded 1 l bot
--   --[ findIndBT ]-->          Maybe (Or (DerivT0 bot) IndBTPackage)
--   --[ extractDemandSimple ]-> Maybe (t, IsValue t, DemandEq e t)
--   --[ indBTElimDemo ]-->      DerivT0 bot
--
-- Synthetic input: a root-indBTB tree at rank 1 over botEqn with
-- v1 = 1, v2 = 2 .  Everything else (premises) is taken as a
-- parameter -- we cannot construct  DerivTBounded 0 _ bot
-- concretely (consistency!), so base/step are abstract.
--
-- The smoke test is twofold:
--
--   (A) smokeFullPipeline : the type-correct composition; if this
--       typechecks, the interfaces compose.
--   (B) smokeFullPipelineJust : a refl-witness that the composition
--       reduces to  just _  on the synthetic input.  This locks in
--       that the partial pipeline actually computes through.
--
-- After this checkpoint, the three known sources of `nothing` are
-- documented and we stop.

module BRA2.FullPipelineSmoke where

open import BRA2.Base
open import BRA2.Term
open import BRA2.Formula
import BRA2.DerivT0       as O
import BRA2.DerivTBounded as B
open import BRA2.DerivT0 using (bot)
open import BRA2.DerivTBounded using (DerivTBounded)
open import BRA2.UnfoldAtValue using (botEqn)
open import BRA2.ExtractDemand using (Maybe ; just ; nothing)
open import BRA2.IndBTHandlerWithCtx using (indBTHandlerWithCtx)
open import BRA2.FindIndBT using
  (findIndBT ; IndBTPackage ; pkgE ; pkgV1 ; pkgV2 ; pkgWF
  ; pkgBase ; pkgStep ; pkgCtx ; Or ; inl ; inr)

------------------------------------------------------------------------
-- finalizeFromFind: combine the findIndBT result with
-- indBTHandlerWithCtx to produce  Maybe (DerivT0 bot) .

finalizeFromFind :
  Maybe (Or (O.DerivT0 bot) IndBTPackage) ->
  Maybe (O.DerivT0 bot)
finalizeFromFind nothing             = nothing
finalizeFromFind (just (inl d0))     = just d0
finalizeFromFind (just (inr pkg))    =
  indBTHandlerWithCtx (pkgE pkg) (pkgV1 pkg) (pkgV2 pkg) (pkgWF pkg)
                       (pkgBase pkg) (pkgStep pkg) (pkgCtx pkg)

------------------------------------------------------------------------
-- fullPipeline: the top-level composition.

fullPipeline :
  {l : Nat} -> DerivTBounded (suc zero) l bot ->
  Maybe (O.DerivT0 bot)
fullPipeline d = finalizeFromFind (findIndBT d)

------------------------------------------------------------------------
-- isJust: discriminator for the smoke test.

isJust : {A : Set} -> Maybe A -> Bool
isJust (just _) = true
isJust nothing  = false

------------------------------------------------------------------------
-- (A) Synthetic root-indBTB pipeline test.
--
-- Input:  B.indBTB botEqn 1 2 base step   (rank 1, conclusion bot).
-- Output: Maybe (DerivT0 bot).
--
-- Premises are abstract parameters.  If this typechecks, the
-- interfaces (findIndBT -> extractDemandSimple -> indBTElimDemo)
-- compose end-to-end.

stepFormula : Formula
stepFormula =
  (atomic (substEq zero (var (suc zero)) botEqn))
  imp ((atomic (substEq zero (var (suc (suc zero))) botEqn))
       imp (atomic (substEq zero (ap2 Pair (var (suc zero)) (var (suc (suc zero)))) botEqn)))

smokeFullPipeline :
  (l1 l2 : Nat) ->
  DerivTBounded zero l1 (atomic (substEq zero O botEqn)) ->
  DerivTBounded zero l2 stepFormula ->
  Maybe (O.DerivT0 bot)
smokeFullPipeline _ _ base step =
  fullPipeline (B.indBTB botEqn (suc zero) (suc (suc zero)) base step)

------------------------------------------------------------------------
-- (B) refl-witness that the pipeline returns  just  on the synthetic
-- input.  v1 = 1, v2 = 2 ensure  natEq v2 v1 = false  reduces to
-- just refl  in decideNotEqNat ; FreshEq via geqZero (botEqn closed).

smokeFullPipelineJust :
  (l1 l2 : Nat) ->
  (base : DerivTBounded zero l1 (atomic (substEq zero O botEqn))) ->
  (step : DerivTBounded zero l2 stepFormula) ->
  Eq (isJust (smokeFullPipeline l1 l2 base step)) true
smokeFullPipelineJust _ _ _ _ = refl

------------------------------------------------------------------------
-- (C) Wrapped-indBTB smoke test for findIndBT (Case B).
--
-- Input:
--   ruleTransB
--     (indBTB botEqn 1 2 base step)         -- conclusion: atomic botEqn
--     (axReflB 0 0 (ap2 Pair O O))          -- conclusion: eqn (Pair O O) (Pair O O)
--   conclusion: atomic (eqn O (Pair O O)) = atomic botEqn = bot
--
-- Tests that findIndBT successfully descends through ruleTransB,
-- locates the indBTB on the left, and packages it with a transL
-- frame around the right (axReflB) lifted to DerivT0.  Returns
-- just (inr pkg) at the findIndBT level; the full pipeline still
-- returns nothing at this stage because Case C (extractor handling
-- of transL frames) is not yet implemented.

isJustOr : {l : Nat} ->
            Maybe (Or (O.DerivT0 bot) IndBTPackage) ->
            Bool
isJustOr (just _) = true
isJustOr nothing  = false

smokeWrappedTransFind :
  (l1 l2 : Nat) ->
  DerivTBounded zero l1 (atomic (substEq zero O botEqn)) ->
  DerivTBounded zero l2 stepFormula ->
  Maybe (Or (O.DerivT0 bot) IndBTPackage)
smokeWrappedTransFind _ _ base step =
  let core = B.indBTB botEqn (suc zero) (suc (suc zero)) base step
      reflRight = B.axReflB zero zero (ap2 Pair O O)
  in findIndBT (B.ruleTransB core reflRight)

smokeWrappedTransFindJust :
  (l1 l2 : Nat) ->
  (base : DerivTBounded zero l1 (atomic (substEq zero O botEqn))) ->
  (step : DerivTBounded zero l2 stepFormula) ->
  Eq (isJustOr {zero} (smokeWrappedTransFind l1 l2 base step)) true
smokeWrappedTransFindJust _ _ _ _ = refl

------------------------------------------------------------------------
-- (D) ruleSymB-wrapped indBTB.  Conclusion-of-indBTB is the swap of
-- botEqn ; ruleSymB then swaps back to bot.
--
-- This exercises the wrapSym helper and the IndBTContext0  sym  frame
-- on pkgCtx.

swappedBotEqn : Equation
swappedBotEqn = eqn (ap2 Pair O O) O

swappedStepFormula : Formula
swappedStepFormula =
  (atomic (substEq zero (var (suc zero)) swappedBotEqn))
  imp ((atomic (substEq zero (var (suc (suc zero))) swappedBotEqn))
       imp (atomic (substEq zero (ap2 Pair (var (suc zero)) (var (suc (suc zero)))) swappedBotEqn)))

smokeWrappedSymFind :
  (l1 l2 : Nat) ->
  DerivTBounded zero l1 (atomic (substEq zero O swappedBotEqn)) ->
  DerivTBounded zero l2 swappedStepFormula ->
  Maybe (Or (O.DerivT0 bot) IndBTPackage)
smokeWrappedSymFind _ _ base step =
  let core = B.indBTB swappedBotEqn (suc zero) (suc (suc zero)) base step
  in findIndBT (B.ruleSymB core)

smokeWrappedSymFindJust :
  (l1 l2 : Nat) ->
  (base : DerivTBounded zero l1 (atomic (substEq zero O swappedBotEqn))) ->
  (step : DerivTBounded zero l2 swappedStepFormula) ->
  Eq (isJustOr {zero} (smokeWrappedSymFind l1 l2 base step)) true
smokeWrappedSymFindJust _ _ _ _ = refl

------------------------------------------------------------------------
-- (E) Doubly-wrapped: ruleTransB (ruleSymB (indBTB swap_e ...))
--                                (axReflB (Pair O O))
--
-- Tests composition of multiple wrappers on the package's pkgCtx
-- (sym INSIDE transL).  The outermost conclusion is bot ; the
-- pkgCtx accumulates  transL (sym (hole _)) (axRefl (Pair O O)) .

smokeDoubleWrapFind :
  (l1 l2 : Nat) ->
  DerivTBounded zero l1 (atomic (substEq zero O swappedBotEqn)) ->
  DerivTBounded zero l2 swappedStepFormula ->
  Maybe (Or (O.DerivT0 bot) IndBTPackage)
smokeDoubleWrapFind _ _ base step =
  let core      = B.indBTB swappedBotEqn (suc zero) (suc (suc zero)) base step
      symCore   = B.ruleSymB core
      reflRight = B.axReflB zero zero (ap2 Pair O O)
  in findIndBT (B.ruleTransB symCore reflRight)

smokeDoubleWrapFindJust :
  (l1 l2 : Nat) ->
  (base : DerivTBounded zero l1 (atomic (substEq zero O swappedBotEqn))) ->
  (step : DerivTBounded zero l2 swappedStepFormula) ->
  Eq (isJustOr {zero} (smokeDoubleWrapFind l1 l2 base step)) true
smokeDoubleWrapFindJust _ _ _ _ = refl
