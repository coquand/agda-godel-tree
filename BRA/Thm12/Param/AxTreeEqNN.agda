{-# OPTIONS --safe --without-K --exact-split #-}

module BRA.Thm12.Param.AxTreeEqNN where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Deriv
open import BRA.Thm.ThmT
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
