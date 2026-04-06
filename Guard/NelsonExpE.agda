{-# OPTIONS --safe --without-K --exact-split #-}

-- NelsonExpE.agda
-- Experiment E failure: TreeEq(L, R) = O is the wrong predicate.
--
-- For axI applied to O:
--   thFunTFor(enc_axI(O)) = Pair(Pair(tagAp1T, Pair(codeIF, O)), O)
--   L = Pair(tagAp1T, Pair(codeIF, O))   -- code of I(O)
--   R = O                                 -- code of O
--   TreeEq(L, R) = Pair(O, O)            -- NOT O!
--
-- The equation I(O) = O is TRUE, but the CODES for I(O) and O
-- are different tree structures. TreeEq compares trees structurally,
-- so it returns Pair(O,O) (false), not O (true).
--
-- This proves that Good(p) := TreeEq(Fst(thFunTFor(p)), Snd(thFunTFor(p))) = O
-- fails at the simplest base case.

module Guard.NelsonExpE where

open import Guard.Base
open import Guard.Term
open import Guard.Step
open import Guard.StepReduce
open import Guard.ThFunTForDefs
open import Guard.ThFunTFor
open import Guard.NelsonDispatch
open import Guard.NelsonAxI

private
  poo : Term ; poo = ap2 Pair O O
  tag0T : Term ; tag0T = reify (natCode n0)
  codeIF : Term ; codeIF = reify (codeF1 I)

  -- The encoding of axI(O)
  enc : Term ; enc = ap2 Pair tag0T (ap2 Pair O O)

  -- The output of thFunTFor on this encoding
  resultL : Term ; resultL = ap2 Pair (reify tagAp1) (ap2 Pair codeIF O)
  resultR : Term ; resultR = O

------------------------------------------------------------------------
-- TreeEq(L, R) = Pair(O, O) — the "Good" predicate fails.
--
-- This is a proof INSIDE Deriv that the TreeEq test gives Pair(O,O),
-- meaning L and R are structurally different trees.

goodFailsAxI : {hyp : Equation} ->
  Deriv hyp (eqn (ap2 TreeEq (ap1 Fst (ap1 thFunTFor enc))
                              (ap1 Snd (ap1 thFunTFor enc)))
                 poo)
goodFailsAxI =
  let -- nelsonAxI O : thFunTFor(enc) = Pair(resultL, resultR)
      nai = nelsonAxI O

      -- Fst(thFunTFor(enc)) = Fst(Pair(resultL, O)) = resultL
      fstR = ruleTrans (cong1 Fst nai) (axFst resultL resultR)

      -- Snd(thFunTFor(enc)) = Snd(Pair(resultL, O)) = O
      sndR = ruleTrans (cong1 Snd nai) (axSnd resultL resultR)

      -- TreeEq(Fst(...), Snd(...)) = TreeEq(resultL, O)
      --                            = TreeEq(Pair(tagAp1T, Pair(codeIF, O)), O)
      --                            = Pair(O, O)
  in ruleTrans (congL TreeEq (ap1 Snd (ap1 thFunTFor enc)) fstR)
     (ruleTrans (congR TreeEq resultL sndR)
                (axTreeEqNL (reify tagAp1) (ap2 Pair codeIF O)))
