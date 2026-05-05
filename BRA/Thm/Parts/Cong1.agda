{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.Thm.Parts.Cong1
--
-- Proof-code vocabulary for the unary congruence rule (recursive, 1 sub-proof):
--   cong1 : (f : Fun1) -> Deriv (atomic (eqn t u))
--                       -> Deriv (atomic (eqn (ap1 f t) (ap1 f u))) .
--
-- Encoding includes  codeF1 f  and the sub-proof tree  y_h .

module BRA.Thm.Parts.Cong1 where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Thm.Tag using (tagCong1)

encCong1 : Fun1 -> Tree -> Tree
encCong1 f y_h = nd (natCode tagCong1) (nd (codeF1 f) y_h)

outCong1 : Fun1 -> Term -> Term -> Tree
outCong1 f t u = codeFormula (atomic (eqn (ap1 f t) (ap1 f u)))

open import BRA.SoundCong1VProof using (body_cong1_v)

------------------------------------------------------------------------
-- body_cong1 (alias for the verifying body in BRA.SoundCong1VProof).

body_cong1 : Fun2
body_cong1 = body_cong1_v
