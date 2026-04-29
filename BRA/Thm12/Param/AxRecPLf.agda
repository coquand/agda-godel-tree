{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.Thm12.Param.AxRecPLf : parametric Term-level encoder + dispatch
-- for axRecPLf.  axRecPLf s p : ap2 (RecP s) p O = O .  Encoded payload:
--   parEncAxRecPLf sT pT = Pair tagCode_axRecPLf (Pair sT pT)
-- where sT, pT are the encoded forms of s and p respectively.

module BRA.Thm12.Param.AxRecPLf where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Deriv
open import BRA.Thm.ThmT
  using ( thmT ; tagCode_axRecPLf ; thmTDispAxRecPLf_param )

parEncAxRecPLf : Term -> Term -> Term
parEncAxRecPLf sT pT =
  ap2 Pair tagCode_axRecPLf (ap2 Pair sT pT)

parOutAxRecPLf : Term -> Term -> Term
parOutAxRecPLf sT pT =
  ap2 Pair
    (ap2 Pair (reify tagAp2)
      (ap2 Pair (ap2 Pair (reify (leftT (codeF2 (RecP IfLf)))) sT)
                (ap2 Pair pT O)))
    O

parDispAxRecPLf : (sT pT : Term) ->
  Deriv (atomic (eqn (ap1 thmT (parEncAxRecPLf sT pT)) (parOutAxRecPLf sT pT)))
parDispAxRecPLf sT pT = thmTDispAxRecPLf_param sT pT
