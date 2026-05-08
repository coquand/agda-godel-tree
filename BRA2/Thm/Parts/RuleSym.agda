{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA2.Thm.Parts.RuleSym
--
-- Proof-code vocabulary for the symmetry rule (recursive, 1 sub-proof):
--   ruleSym : Deriv (atomic (eqn t u)) -> Deriv (atomic (eqn u t)) .
--
-- Encoding splices the sub-proof  y_h  under the tag.  The conclusion's
-- t and u are recovered inside  thmT  from  thmT(reify y_h)  by Fst /
-- Snd extraction on the reified  codeEqn  payload.
--
-- Dispatch lemma signature (in BRA2.Thm.ThmT):
--   thmTDispRuleSym :
--     (t u : Term) (y_h : Tree) ->
--     Deriv (atomic (eqn (ap1 thmT (reify y_h))
--                        (reify (codeFormula (atomic (eqn t u)))))) ->
--     Deriv (atomic (eqn (ap1 thmT (reify (encRuleSym y_h)))
--                        (reify (outRuleSym t u))))

module BRA2.Thm.Parts.RuleSym where

open import BRA2.Base
open import BRA2.Term
open import BRA2.Formula
open import BRA2.Thm.Tag using (tagRuleSym)
open import BRA2.SoundRuleSymVProof using (body_ruleSym_v)

encRuleSym : Tree -> Tree
encRuleSym y_h = nd (natCode tagRuleSym) y_h

outRuleSym : Term -> Term -> Tree
outRuleSym t u = codeFormula (atomic (eqn u t))

------------------------------------------------------------------------
-- body_ruleSym (alias for the verifying body in SoundRuleSymVProof).

body_ruleSym : Fun2
body_ruleSym = body_ruleSym_v
