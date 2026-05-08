{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA2.Thm.Parts.RuleInst2
--
-- Proof-code vocabulary for the simultaneous double-substitution
-- dispatch in thmT.  Analog of BRA2.Thm.Parts.RuleInst, but with TWO
-- (variable, term) pairs in the payload:
--
--   encRuleInst2 (xA, tA, xB, tB) y_h =
--     nd (natCode tagRuleInst2)
--        (nd (code (var xA))
--            (nd (code (var xB))
--                (nd y_h
--                    (nd (code tA) (code tB)))))
--
-- where xA, xB are variable indices, tA, tB are the substituent Terms,
-- and y_h is the inner proof-code Tree.
--
-- Inside thmT, the conclusion's formula is recovered from
--   thmT(reify y_h)  (= reify (codeFormula P))
-- and the encoded xA, xB, tA, tB by an explicit substF-at-code-level
-- combinator analogous to subT2 (BRA2.Sb2).
--
-- Dispatch lemma signature (in BRA2.Thm.ThmT, to be added):
--   thmTDispRuleInst2 :
--     (xA xB : Nat) (tA tB : Term) (P : Formula) (y_h : Tree) ->
--     Deriv (atomic (eqn (ap1 thmT (reify y_h))
--                         (reify (codeFormula P)))) ->
--     Deriv (atomic (eqn (ap1 thmT (reify (encRuleInst2 xA xB tA tB y_h)))
--                         (reify (outRuleInst2 xA xB tA tB P))))

module BRA2.Thm.Parts.RuleInst2 where

open import BRA2.Base
open import BRA2.Term
open import BRA2.Formula
open import BRA2.Thm.Tag using (tagRuleInst2)

-- Payload structure.  Mirrors RuleInst's "y_h before code t" ordering:
-- the sub-proof code y_h sits in the inner-pair head so the second-level
-- inner-pair distribution can discharge via y_h's shape proof.
encRuleInst2 : Nat -> Nat -> Term -> Term -> Tree -> Tree
encRuleInst2 xA xB tA tB y_h =
  nd (natCode tagRuleInst2)
     (nd (code (var xA))
         (nd (code (var xB))
             (nd y_h
                 (nd (code tA) (code tB)))))

-- Output: code of the doubly-substituted formula.
outRuleInst2 : Nat -> Nat -> Term -> Term -> Formula -> Tree
outRuleInst2 xA xB tA tB P =
  codeFormula (substF xA tA (substF xB tB P))

open import BRA2.SoundRuleInst2VProof using (body_ruleInst2_v)

------------------------------------------------------------------------
-- body_ruleInst2 (alias for the verifying body in BRA2.SoundRuleInst2VProof).

body_ruleInst2 : Fun2
body_ruleInst2 = body_ruleInst2_v
