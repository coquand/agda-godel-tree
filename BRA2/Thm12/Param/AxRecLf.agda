{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA2.Thm12.Param.AxRecLf : parametric Term-level encoder + dispatch
-- for axRecLf.  axRecLf z s : (Rec z s) O = z .  Encoded payload:
--   parEncAxRecLf zT sT = Pair tagCode_axRecLf (Pair zT sT)
-- where zT, sT are the encoded forms of z and s respectively.

module BRA2.Thm12.Param.AxRecLf where

open import BRA2.Base
open import BRA2.Term
open import BRA2.Formula
open import BRA2.Deriv
open import BRA2.Thm.ThmT
  using ( thmT ; tagCode_axRecLf ; thmTDispAxRecLf_param )

parEncAxRecLf : Term -> Term -> Term
parEncAxRecLf zT sT =
  ap2 Pair tagCode_axRecLf (ap2 Pair zT sT)

parOutAxRecLf : Term -> Term -> Term
parOutAxRecLf zT sT =
  ap2 Pair
    (ap2 Pair (reify tagAp1)
      (ap2 Pair (ap2 Pair (reify (leftT (codeF1 (Rec O IfLf))))
                          (ap2 Pair zT sT))
                O))
    zT

parDispAxRecLf : (zT sT : Term) ->
  Deriv (atomic (eqn (ap1 thmT (parEncAxRecLf zT sT)) (parOutAxRecLf zT sT)))
parDispAxRecLf zT sT = thmTDispAxRecLf_param zT sT
