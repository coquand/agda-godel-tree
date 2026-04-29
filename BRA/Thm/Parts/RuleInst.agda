{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.Thm.Parts.RuleInst
--
-- Proof-code vocabulary for the substitution rule (recursive, 1 sub-proof + var + term):
--   ruleInst : (x : Nat) (t : Term) -> Deriv P -> Deriv (substF x t P) .
--
-- The encoding records the variable index  x  (as  code (var x)
-- which carries  natCode x ), the substituted term  t , and the
-- sub-proof tree  y_h .  Inside  thmT , the conclusion's formula
-- is recovered from  thmT(reify y_h)  (= reify (codeFormula P))
-- and the encoded  x , t  by an explicit  substF -at-code-level
-- combinator (analogous to  sub  in  BRA/Sub.agda  but at the
-- formula level instead of the term level).
--
-- Dispatch lemma signature (in BRA.Thm.ThmT):
--   thmTDispRuleInst :
--     (x : Nat) (t : Term) (P : Formula) (y_h : Tree) ->
--     Deriv (atomic (eqn (ap1 thmT (reify y_h))
--                        (reify (codeFormula P)))) ->
--     Deriv (atomic (eqn (ap1 thmT (reify (encRuleInst x t y_h)))
--                        (reify (outRuleInst x t P))))

module BRA.Thm.Parts.RuleInst where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Thm.Tag using (tagRuleInst)

-- Payload order: y_h sits in the inner-pair head so the second-level
-- inner-pair distribution discharges via y_h's shape proof.  Putting
-- code t  first would block distribution when  t = O .  See the
-- corresponding note in  BRA.Thm.Parts.CongL .
encRuleInst : Nat -> Term -> Tree -> Tree
encRuleInst x t y_h = nd (natCode tagRuleInst)
                         (nd (code (var x))
                             (nd y_h (code t)))

outRuleInst : Nat -> Term -> Formula -> Tree
outRuleInst x t P = codeFormula (substF x t P)
