{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.Thm12RecCheckIndBTTest
--
-- Test: can we drive Theorem 12 (Rec case) through the encoded
-- ruleIndBT dispatcher (thmTDispRuleIndBT) at concrete toy inputs?
--
-- This is a smoke test for the architectural route via Guard's `ind`
-- combinator (our analog: the BRA primitive `ruleIndBT` dispatched
-- through `thmTDispRuleIndBT`).  If this typechecks, the dispatcher
-- composes cleanly at concrete inputs and we have a viable path for
-- the universal closure of Theorem 12 in the Rec case.  If it
-- doesn't, we stop and re-evaluate.
--
-- Toy choice: P = atomic (eqn O O).  Has no free var 0, so substF
-- is the identity on it.  This sidesteps closure-of-substitution
-- concerns; the test isolates whether the dispatcher's signature
-- composes at concrete (closed) sub-proof Trees.
--
-- y_base : Tree = encAxRefl O                  -- encoded "axRefl O"
-- y_step : Tree = encAxK P P                   -- encoded "axK P P"
-- thmTDispRuleIndBT P v1 v2 y_base y_step (...) (...)
--   should give  thmT(reify (encRuleIndBT P v1 v2 y_base y_step))
--               = reify (outRuleIndBT P) = reify (codeFormula P) .

module BRA.Thm12RecCheckIndBTTest where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Deriv
open import BRA.Thm.ThmT using
  ( thmT ; thmTDispAxRefl ; thmTDispAxK ; thmTDispRuleIndBT )
open import BRA.Thm.Parts.AxRefl  using (encAxRefl ; outAxRefl)
open import BRA.Thm.Parts.AxK     using (encAxK ; outAxK)
open import BRA.Thm.Parts.RuleIndBT using (encRuleIndBT ; outRuleIndBT)

------------------------------------------------------------------------
-- Toy P (no free var 0).

P : Formula
P = atomic (eqn O O)

v1 : Nat
v1 = suc zero

v2 : Nat
v2 = suc (suc zero)

------------------------------------------------------------------------
-- Sub-proof Trees.

y_base : Tree
y_base = encAxRefl O

y_step : Tree
y_step = encAxK P P

------------------------------------------------------------------------
-- Sub-proof input Derivs (required by thmTDispRuleIndBT's signature).
--
-- thmTDispAxRefl O : thmT(reify (encAxRefl O)) = reify (outAxRefl O)
--                  = reify (codeFormula (atomic (eqn O O)))
--                  = reify (codeFormula P)
--                  = reify (codeFormula (substF zero O P))     -- since P has no free var 0.

base_input :
  Deriv (atomic (eqn (ap1 thmT (reify y_base))
                     (reify (codeFormula (substF zero O P)))))
base_input = thmTDispAxRefl O

-- thmTDispAxK P P : thmT(reify (encAxK P P)) = reify (outAxK P P)
--                 = reify (codeFormula (P imp (P imp P)))
--                 = reify (codeFormula
--                          ((substF zero (var v1) P) imp
--                           ((substF zero (var v2) P) imp
--                            (substF zero (ap2 Pair (var v1) (var v2)) P))))
-- since substF on P leaves it unchanged.

step_input :
  Deriv (atomic (eqn (ap1 thmT (reify y_step))
                     (reify (codeFormula
                             ((substF zero (var v1) P) imp
                              ((substF zero (var v2) P) imp
                               (substF zero (ap2 Pair (var v1) (var v2)) P)))))))
step_input = thmTDispAxK P P

------------------------------------------------------------------------
-- The test result: apply thmTDispRuleIndBT.

test_result :
  Deriv (atomic (eqn (ap1 thmT (reify (encRuleIndBT P v1 v2 y_base y_step)))
                     (reify (outRuleIndBT P))))
test_result =
  thmTDispRuleIndBT P v1 v2 y_base y_step base_input step_input

-- If this file typechecks, the dispatcher works at concrete inputs and
-- the route via thmTDispRuleIndBT is viable for Theorem 12's Rec case.
