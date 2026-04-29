{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.Thm.Parts.AxI
--
-- Proof-code vocabulary for the primitive  axI : Deriv (ap1 I t = t) .
--
-- Two exports:
--   encAxI : Term -> Tree           -- tree-level encoding of the step
--   outAxI : Term -> Tree           -- expected  thmT  output for that encoding
--
-- The dispatch lemma  thmTDispAxI  and the Encode.agda case using it
-- live outside this file (in  BRA.Thm.ThmT  and  BRA.Thm.Encode
-- respectively).  Parts files export only pure vocabulary.

module BRA.Thm.Parts.AxI where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Thm.Tag using (tagAxI)

encAxI : Term -> Tree
encAxI t = nd (natCode tagAxI) (code t)

outAxI : Term -> Tree
outAxI t = codeFormula (atomic (eqn (ap1 I t) t))
