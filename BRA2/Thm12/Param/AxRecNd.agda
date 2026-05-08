{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA2.Thm12.Param.AxRecNd : parametric Term-level encoder + dispatch
-- for axRecNd.  axRecNd z s a b :
--   (Rec z s) (Pair a b) = s (Pair a b) (Pair ((Rec z s) a) ((Rec z s) b)).
-- Encoded payload (depth-4 Pair):
--   parEncAxRecNd zT sT aT bT
--     = Pair tagCode_axRecNd (Pair zT (Pair sT (Pair aT bT)))
-- where zT, sT, aT, bT are the encoded forms of z, s, a, b respectively.

module BRA2.Thm12.Param.AxRecNd where

open import BRA2.Base
open import BRA2.Term
open import BRA2.Formula
open import BRA2.Deriv
open import BRA2.Thm.ThmT
  using ( thmT ; tagCode_axRecNd ; thmTDispAxRecNd_param )

parEncAxRecNd : Term -> Term -> Term -> Term -> Term
parEncAxRecNd zT sT aT bT =
  ap2 Pair tagCode_axRecNd
    (ap2 Pair zT (ap2 Pair sT (ap2 Pair aT bT)))

parOutAxRecNd : Term -> Term -> Term -> Term -> Term
parOutAxRecNd zT sT aT bT =
  ap2 Pair
    -- LHS-encoded: code (ap1 (Rec z s) (ap2 Pair a b))
    (ap2 Pair (reify tagAp1)
      (ap2 Pair (ap2 Pair (reify (leftT (codeF1 (Rec O IfLf))))
                          (ap2 Pair zT sT))
                (ap2 Pair (reify tagAp2)
                  (ap2 Pair (reify (codeF2 Pair))
                    (ap2 Pair aT bT)))))
    -- RHS-encoded: code (ap2 s (ap2 Pair a b)
    --                          (ap2 Pair (ap1 (Rec z s) a) (ap1 (Rec z s) b)))
    (ap2 Pair (reify tagAp2)
      (ap2 Pair sT
        (ap2 Pair
          (ap2 Pair (reify tagAp2)
            (ap2 Pair (reify (codeF2 Pair))
              (ap2 Pair aT bT)))
          (ap2 Pair (reify tagAp2)
            (ap2 Pair (reify (codeF2 Pair))
              (ap2 Pair
                (ap2 Pair (reify tagAp1)
                  (ap2 Pair (ap2 Pair (reify (leftT (codeF1 (Rec O IfLf))))
                                      (ap2 Pair zT sT))
                            aT))
                (ap2 Pair (reify tagAp1)
                  (ap2 Pair (ap2 Pair (reify (leftT (codeF1 (Rec O IfLf))))
                                      (ap2 Pair zT sT))
                            bT))))))))

parDispAxRecNd : (zT sT aT bT : Term) ->
  Deriv (atomic (eqn (ap1 thmT (parEncAxRecNd zT sT aT bT))
                     (parOutAxRecNd zT sT aT bT)))
parDispAxRecNd zT sT aT bT = thmTDispAxRecNd_param zT sT aT bT
