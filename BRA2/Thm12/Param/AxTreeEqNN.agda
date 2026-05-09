{-# OPTIONS --safe --without-K --exact-split #-}

module BRA2.Thm12.Param.AxTreeEqNN where

open import BRA2.Base
open import BRA2.Term
open import BRA2.Formula
open import BRA2.DerivThreshold
open import BRA2.Thm.ThmT
  using ( thmT ; tagCode_axTreeEqNN ; thmTDispAxTreeEqNN_param )

parEncAxTreeEqNN : Term -> Term -> Term -> Term -> Term
parEncAxTreeEqNN a1T a2T b1T b2T =
  ap2 Pair tagCode_axTreeEqNN
    (ap2 Pair a1T (ap2 Pair a2T (ap2 Pair b1T b2T)))

parOutAxTreeEqNN : Term -> Term -> Term -> Term -> Term
parOutAxTreeEqNN a1T a2T b1T b2T =
  ap2 Pair
    (ap2 Pair (reify tagAp2)
      (ap2 Pair (reify (codeF2 TreeEq))
        (ap2 Pair
          (ap2 Pair (reify tagAp2)
            (ap2 Pair (reify (codeF2 Pair))
              (ap2 Pair a1T a2T)))
          (ap2 Pair (reify tagAp2)
            (ap2 Pair (reify (codeF2 Pair))
              (ap2 Pair b1T b2T))))))
    (ap2 Pair (reify tagAp2)
      (ap2 Pair (reify (codeF2 IfLf))
        (ap2 Pair
          (ap2 Pair (reify tagAp2)
            (ap2 Pair (reify (codeF2 TreeEq))
              (ap2 Pair a1T b1T)))
          (ap2 Pair (reify tagAp2)
            (ap2 Pair (reify (codeF2 Pair))
              (ap2 Pair
                (ap2 Pair (reify tagAp2)
                  (ap2 Pair (reify (codeF2 TreeEq))
                    (ap2 Pair a2T b2T)))
                (ap2 Pair (reify tagAp2)
                  (ap2 Pair (reify (codeF2 Pair))
                    (ap2 Pair O O)))))))))

parDispAxTreeEqNN : (a1T a2T b1T b2T : Term) ->
  Deriv (atomic (eqn (ap1 thmT (parEncAxTreeEqNN a1T a2T b1T b2T))
                     (parOutAxTreeEqNN a1T a2T b1T b2T)))
parDispAxTreeEqNN a1T a2T b1T b2T = thmTDispAxTreeEqNN_param a1T a2T b1T b2T
