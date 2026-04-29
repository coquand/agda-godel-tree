{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.Thm.Parts.Mp
--
-- Proof-code vocabulary for the recursive inference rule
--   mp : Deriv (P imp Q) -> Deriv P -> Deriv Q .
--
-- This is the first RECURSIVE primitive.  Unlike the axiom Parts
-- files (whose outX is a function of the primitive's syntactic
-- arguments only), outMp depends on the formula Q that is recovered
-- inside  thmT  from the first sub-proof's dispatch result.  The
-- encoding  encMp y1 y2  splices two sub-proof encodings under a tag.
--
-- Architectural note:  Parts files export only  encX  and  outX .
-- The dispatch-lemma for mp is stated in  BRA.Thm.ThmT  as
--
--   thmTDispMp :
--     (P Q : Formula) (y1 y2 : Tree) ->
--     Deriv (atomic (eqn (ap1 thmT (reify y1))
--                        (reify (codeFormula (P imp Q))))) ->
--     Deriv (atomic (eqn (ap1 thmT (reify y2))
--                        (reify (codeFormula P)))) ->
--     Deriv (atomic (eqn (ap1 thmT (reify (encMp y1 y2)))
--                        (reify (codeFormula Q))))
--
-- and consumed in  BRA.Thm.Encode  at the mp pattern-match by the
-- one-liner
--
--   encode Q (mp {P' = P} h1 h2) =
--     let (mkSigma y1 d1) = encode (P imp Q) h1
--         (mkSigma y2 d2) = encode P h2
--     in  mkSigma (encMp y1 y2) (thmTDispMp P Q y1 y2 d1 d2) .
--
-- The recursive structure lives in  Encode.agda ; Parts/Mp.agda is
-- pure vocabulary.

module BRA.Thm.Parts.Mp where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Thm.Tag using (tagMp)

------------------------------------------------------------------------
-- Encoding: tag plus the pair of sub-proof encodings.
--
--   encMp y1 y2  encodes  mp h1 h2  where
--     y1 encodes h1 : Deriv (P imp Q)
--     y2 encodes h2 : Deriv P

encMp : Tree -> Tree -> Tree
encMp y1 y2 = nd (natCode tagMp) (nd y1 y2)

------------------------------------------------------------------------
-- Expected thmT output: code of Q (the conclusion of mp h1 h2).
--
-- Q is NOT a subtree of  encMp y1 y2 .  Inside  thmT  it is recovered
-- from  thmT(reify y1) = reify (codeFormula (P imp Q))  by a
-- combinator-level  mpF  (see BRA/Mp.agda).  outMp just states the
-- result type.

outMp : Formula -> Tree
outMp Q = codeFormula Q
