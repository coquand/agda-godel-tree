{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.Thm.Parts.RuleSym
--
-- Proof-code vocabulary for the symmetry rule (recursive, 1 sub-proof):
--   ruleSym : Deriv (atomic (eqn t u)) -> Deriv (atomic (eqn u t)) .
--
-- Encoding splices the sub-proof  y_h  under the tag.  The conclusion's
-- t and u are recovered inside  thmT  from  thmT(reify y_h)  by Fst /
-- Snd extraction on the reified  codeEqn  payload.
--
-- Dispatch lemma signature (in BRA.Thm.ThmT):
--   thmTDispRuleSym :
--     (t u : Term) (y_h : Tree) ->
--     Deriv (atomic (eqn (ap1 thmT (reify y_h))
--                        (reify (codeFormula (atomic (eqn t u)))))) ->
--     Deriv (atomic (eqn (ap1 thmT (reify (encRuleSym y_h)))
--                        (reify (outRuleSym t u))))

module BRA.Thm.Parts.RuleSym where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Thm.Tag using (tagRuleSym)

encRuleSym : Tree -> Tree
encRuleSym y_h = nd (natCode tagRuleSym) y_h

outRuleSym : Term -> Term -> Tree
outRuleSym t u = codeFormula (atomic (eqn u t))
