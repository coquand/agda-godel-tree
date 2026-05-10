{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA2.ExtractDemandSmoke -- concrete smoke tests for the
-- extractDemandSimple extractor, verifying that the (P1) refactor
-- of  IndBTContext0.inst  computationally solves the
-- `inst zero t (hole _)` case (not just typechecks abstractly).
--
-- Two `refl`-checked tests:
--
--   testHole : extractDemandSimple botEqn (hole bot)
--                == just (O, valO, refl)
--   testInst : extractDemandSimple botEqn (singleInstCtx botEqn O)
--                == just (O, valO, refl)
--
-- If these typecheck, the extractor reduces fully on the concrete
-- inputs — confirming the pipeline is not just type-correct but also
-- evaluates to the expected witnesses.

module BRA2.ExtractDemandSmoke where

open import BRA2.Base
open import BRA2.Term
open import BRA2.Formula
open import BRA2.DerivT0 using (bot)
open import BRA2.IndBTContext0 using (hole ; singleInstCtx)
open import BRA2.UnfoldAtValue using (botEqn)
open import BRA2.ExtractDemand using (Maybe ; just ; nothing ; ExtractedDemand ; extractDemandSimple)

------------------------------------------------------------------------
-- Expected witness for both tests: the extracted demand for
-- e = botEqn, t = O is (O, valO, refl) inside `just`.
--
-- substEq zero O botEqn = botEqn  by computation, so the demand
-- equation  Eq (substEq zero O botEqn) botEqn  is  refl .

expectedHoleAndInst : Maybe (ExtractedDemand botEqn)
expectedHoleAndInst = just (mkSigma O (mkSigma valO refl))

------------------------------------------------------------------------
-- Test 1: hole context for bot.

testHole :
  Eq (extractDemandSimple botEqn (hole bot)) expectedHoleAndInst
testHole = refl

------------------------------------------------------------------------
-- Test 2: singleInstCtx for botEqn at O.
--
-- singleInstCtx botEqn O : IndBTContext0 (atomic botEqn) (atomic (substEq 0 O botEqn))
--                        = IndBTContext0 (atomic botEqn) bot   (by computation)

testInst :
  Eq (extractDemandSimple botEqn (singleInstCtx botEqn O)) expectedHoleAndInst
testInst = refl
