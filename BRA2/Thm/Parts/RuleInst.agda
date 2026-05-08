{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA2.Thm.Parts.RuleInst
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
-- Dispatch lemma signature (in BRA2.Thm.ThmT):
--   thmTDispRuleInst :
--     (x : Nat) (t : Term) (P : Formula) (y_h : Tree) ->
--     Deriv (atomic (eqn (ap1 thmT (reify y_h))
--                        (reify (codeFormula P)))) ->
--     Deriv (atomic (eqn (ap1 thmT (reify (encRuleInst x t y_h)))
--                        (reify (outRuleInst x t P))))

module BRA2.Thm.Parts.RuleInst where

open import BRA2.Base
open import BRA2.Term
open import BRA2.Formula
open import BRA2.Thm.Tag using (tagRuleInst)

-- Payload order (refactor 2026-05-02 — see ARCHITECTURE-FINDINGS.md
-- Finding 1 analog for ruleInst):  closed (varCode, tCode) pair sits at
-- the inner-pair head, with the OPEN proof-index  y_h  at the outer Snd.
-- This way, thmT distributes through the inner pair (Pair shape on
-- (varCode, tCode) is closed via axFst), bringing  thmT y_h  out as
-- Snd of the recs-image directly — no shape obligation on  y_h .
-- Cf. body_ruleInst in BRA2.Thm.ThmT and Definition 12 line 2 (Guard
-- p.16) which Holds Parametrically in y_h under this layout.
encRuleInst : Nat -> Term -> Tree -> Tree
encRuleInst x t y_h = nd (natCode tagRuleInst)
                         (nd (nd (code (var x)) (code t))
                             y_h)

outRuleInst : Nat -> Term -> Formula -> Tree
outRuleInst x t P = codeFormula (substF x t P)

open import BRA2.SoundRuleInstVProof using (body_ruleInst_v)

------------------------------------------------------------------------
-- body_ruleInst (alias for the verifying body in BRA2.SoundRuleInstVProof).

body_ruleInst : Fun2
body_ruleInst = body_ruleInst_v
