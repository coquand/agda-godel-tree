{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA2.Thm.Parts.RuleIndBT
--
-- Proof-code vocabulary for binary-tree induction (recursive, 2 sub-proofs):
--   ruleIndBT : (P : Formula) (v1 v2 : Nat) ->
--               Deriv (substF zero O P) ->
--               Deriv ((substF zero (var v1) P) imp
--                      ((substF zero (var v2) P) imp
--                       (substF zero (ap2 Pair (var v1) (var v2)) P))) ->
--               Deriv P .
--
-- The encoding records the formula  P  (so the conclusion's shape
-- is recoverable inside  thmT  without further extraction), the
-- two fresh variable indices  v1, v2 , and the two sub-proof trees.
-- Note: P is included explicitly in the encoding because the
-- conclusion is just  P  (not derivable from the sub-proofs alone
-- without knowing P, since substF zero - P collapses information).

module BRA2.Thm.Parts.RuleIndBT where

open import BRA2.Base
open import BRA2.Term
open import BRA2.Formula
open import BRA2.Thm.Tag using (tagRuleIndBT)

encRuleIndBT : Formula -> Nat -> Nat -> Tree -> Tree -> Tree
encRuleIndBT P v1 v2 y_base y_step =
  nd (natCode tagRuleIndBT)
     (nd (codeFormula P)
         (nd (code (var v1))
             (nd (code (var v2))
                 (nd y_base y_step))))

outRuleIndBT : Formula -> Tree
outRuleIndBT P = codeFormula P

open import BRA2.SoundRuleIndBTVProof using (body_ruleIndBT_v)

------------------------------------------------------------------------
-- body_ruleIndBT (alias for the verifying body in BRA2.SoundRuleIndBTVProof).

body_ruleIndBT : Fun2
body_ruleIndBT = body_ruleIndBT_v
