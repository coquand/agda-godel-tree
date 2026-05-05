{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.Thm.Parts.CongL
--
-- Proof-code vocabulary for the binary left congruence rule (recursive, 1 sub-proof):
--   congL : (g : Fun2) (x : Term) -> Deriv (atomic (eqn t u))
--                                  -> Deriv (atomic (eqn (ap2 g t x) (ap2 g u x))) .

module BRA.Thm.Parts.CongL where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Thm.Tag using (tagCongL)

-- New layout (Finding 1): the open sub-proof tree y_h sits at the outer
-- Snd, and the closed pair (codeF2 g, code x) sits at the inner Fst.
-- This lets thmT's distribution walk go through closed Pair-shaped
-- subterms (provable from axFst/fstReifyCodeF2) without any shape
-- obligation on y_h.
encCongL : Fun2 -> Term -> Tree -> Tree
encCongL g x y_h = nd (natCode tagCongL)
                      (nd (nd (codeF2 g) (code x))
                          y_h)

outCongL : Fun2 -> Term -> Term -> Term -> Tree
outCongL g x t u = codeFormula (atomic (eqn (ap2 g t x) (ap2 g u x)))

open import BRA.SoundCongLVProof using (body_congL_v)

------------------------------------------------------------------------
-- body_congL (alias for the verifying body in BRA.SoundCongLVProof).

body_congL : Fun2
body_congL = body_congL_v
