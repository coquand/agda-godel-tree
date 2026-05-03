{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.Thm12.Param.AxTreeRecLf : parametric Term-level encoder + dispatch
-- for axTreeRecLf.  axTreeRecLf f s p :
--   ap2 (treeRec f s) p O = ap1 f p .
-- Encoded payload (depth-3 Pair):
--   parEncAxTreeRecLf fT sT pT
--     = Pair tagCode_axTreeRecLf (Pair fT (Pair sT pT))
-- where fT, sT, pT are the encoded forms of f, s, p respectively.

module BRA.Thm12.Param.AxTreeRecLf where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Deriv
open import BRA.Thm.ThmT
  using ( thmT ; tagCode_axTreeRecLf ; thmTDispAxTreeRecLf_param )

parEncAxTreeRecLf : Term -> Term -> Term -> Term
parEncAxTreeRecLf fT sT pT =
  ap2 Pair tagCode_axTreeRecLf (ap2 Pair fT (ap2 Pair sT pT))

parOutAxTreeRecLf : Term -> Term -> Term -> Term
parOutAxTreeRecLf fT sT pT =
  ap2 Pair
    (ap2 Pair (reify tagAp2)
      (ap2 Pair (ap2 Pair (reify (leftT (codeF2 (treeRec I IfLf))))
                          (ap2 Pair fT sT))
                (ap2 Pair pT O)))
    (ap2 Pair (reify tagAp1) (ap2 Pair fT pT))

parDispAxTreeRecLf : (fT sT pT : Term) ->
  Deriv (atomic (eqn (ap1 thmT (parEncAxTreeRecLf fT sT pT))
                     (parOutAxTreeRecLf fT sT pT)))
parDispAxTreeRecLf fT sT pT = thmTDispAxTreeRecLf_param fT sT pT
