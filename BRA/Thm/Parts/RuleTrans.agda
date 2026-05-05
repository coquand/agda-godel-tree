{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.Thm.Parts.RuleTrans
--
-- Proof-code vocabulary for the transitivity rule (recursive, 2 sub-proofs):
--   ruleTrans : Deriv (atomic (eqn t u))
--             -> Deriv (atomic (eqn u v))
--             -> Deriv (atomic (eqn t v)) .
--
-- Encoding splices both sub-proof encodings under the tag.  Inside
--  thmT , the conclusion (eqn t v) is recovered from  thmT(reify y1)
-- (= code of eqn t u) and  thmT(reify y2)  (= code of eqn u v) via
-- Fst/Snd extraction.

module BRA.Thm.Parts.RuleTrans where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Thm.Tag using (tagRuleTrans)

encRuleTrans : Tree -> Tree -> Tree
encRuleTrans y1 y2 = nd (natCode tagRuleTrans) (nd y1 y2)

outRuleTrans : Term -> Term -> Tree
outRuleTrans t v = codeFormula (atomic (eqn t v))

open import BRA.SoundRuleTransVProof using (body_ruleTrans_v)

------------------------------------------------------------------------
-- body_ruleTrans (alias for the verifying body in BRA.SoundRuleTransVProof).

body_ruleTrans : Fun2
body_ruleTrans = body_ruleTrans_v
