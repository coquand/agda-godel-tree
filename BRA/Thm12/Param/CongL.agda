{-# OPTIONS --safe --without-K --exact-split #-}

module BRA.Thm12.Param.CongL where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Deriv
open import BRA.Thm.ThmT
  using ( thmT ; tagCode_congL ; thmTDispCongL_param )

-- New encoding (Finding 1): the open IH subterm  y_h_T  sits at the
-- outer  Snd , and the closed pair  (reify (codeF2 g), xT)  sits at the
-- inner Fst.  When  thmT  distributes through the payload, the Fst-walk
-- only goes through closed Pair-shaped subterms, so no shape obligation
-- on  y_h_T  is needed.
parEncCongL : Fun2 -> Term -> Term -> Term
parEncCongL g y_h_T xT =
  ap2 Pair tagCode_congL
    (ap2 Pair (ap2 Pair (reify (codeF2 g)) xT) y_h_T)

parOutCongL : Fun2 -> Term -> Term -> Term -> Term
parOutCongL g xT u1 u2 =
  ap2 Pair (ap2 Pair (reify tagAp2)
                     (ap2 Pair (reify (codeF2 g))
                               (ap2 Pair u1 xT)))
           (ap2 Pair (reify tagAp2)
                     (ap2 Pair (reify (codeF2 g))
                               (ap2 Pair u2 xT)))

parDispCongL : (g : Fun2) (y_h_T xT : Term) (u1 u2 : Term) ->
  Deriv (atomic (eqn (ap1 thmT y_h_T) (ap2 Pair u1 u2))) ->
  Deriv (atomic (eqn (ap1 thmT (parEncCongL g y_h_T xT))
                     (parOutCongL g xT u1 u2)))
parDispCongL g y_h_T xT u1 u2 d_h =
  thmTDispCongL_param g xT y_h_T u1 u2 d_h
