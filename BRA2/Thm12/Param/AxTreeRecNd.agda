{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA2.Thm12.Param.AxTreeRecNd : parametric Term-level encoder + dispatch
-- for axTreeRecNd.  axTreeRecNd f s p a b :
--   ap2 (treeRec f s) p (ap2 Pair a b)
--     = ap2 s (ap2 Pair p (ap2 Pair a b))
--             (ap2 Pair (ap2 (treeRec f s) p a)
--                       (ap2 (treeRec f s) p b)) .
-- Encoded payload (depth-5 Pair):
--   parEncAxTreeRecNd fT sT pT aT bT
--     = Pair tagCode_axTreeRecNd
--           (Pair fT (Pair sT (Pair pT (Pair aT bT))))
-- where fT, sT, pT, aT, bT are the encoded forms of f, s, p, a, b.

module BRA2.Thm12.Param.AxTreeRecNd where

open import BRA2.Base
open import BRA2.Term
open import BRA2.Formula
open import BRA2.DerivThreshold
open import BRA2.Thm.ThmT
  using ( thmT ; tagCode_axTreeRecNd ; thmTDispAxTreeRecNd_param )

parEncAxTreeRecNd : Term -> Term -> Term -> Term -> Term -> Term
parEncAxTreeRecNd fT sT pT aT bT =
  ap2 Pair tagCode_axTreeRecNd
    (ap2 Pair fT (ap2 Pair sT (ap2 Pair pT (ap2 Pair aT bT))))

parOutAxTreeRecNd : Term -> Term -> Term -> Term -> Term -> Term
parOutAxTreeRecNd fT sT pT aT bT =
  ap2 Pair
    -- LHS-encoded: code (ap2 (treeRec f s) p (ap2 Pair a b))
    (ap2 Pair (reify tagAp2)
      (ap2 Pair (ap2 Pair (reify (leftT (codeF2 (treeRec I IfLf))))
                          (ap2 Pair fT sT))
                (ap2 Pair pT
                  (ap2 Pair (reify tagAp2)
                    (ap2 Pair (reify (codeF2 Pair))
                      (ap2 Pair aT bT))))))
    -- RHS-encoded: code (ap2 s (ap2 Pair p (ap2 Pair a b))
    --                          (ap2 Pair (ap2 (treeRec f s) p a)
    --                                    (ap2 (treeRec f s) p b)))
    (ap2 Pair (reify tagAp2)
      (ap2 Pair sT
        (ap2 Pair
          (ap2 Pair (reify tagAp2)
            (ap2 Pair (reify (codeF2 Pair))
              (ap2 Pair pT
                (ap2 Pair (reify tagAp2)
                  (ap2 Pair (reify (codeF2 Pair))
                    (ap2 Pair aT bT))))))
          (ap2 Pair (reify tagAp2)
            (ap2 Pair (reify (codeF2 Pair))
              (ap2 Pair
                (ap2 Pair (reify tagAp2)
                  (ap2 Pair (ap2 Pair (reify (leftT (codeF2 (treeRec I IfLf))))
                                      (ap2 Pair fT sT))
                            (ap2 Pair pT aT)))
                (ap2 Pair (reify tagAp2)
                  (ap2 Pair (ap2 Pair (reify (leftT (codeF2 (treeRec I IfLf))))
                                      (ap2 Pair fT sT))
                            (ap2 Pair pT bT)))))))))

parDispAxTreeRecNd : (fT sT pT aT bT : Term) ->
  Deriv (atomic (eqn (ap1 thmT (parEncAxTreeRecNd fT sT pT aT bT))
                     (parOutAxTreeRecNd fT sT pT aT bT)))
parDispAxTreeRecNd fT sT pT aT bT = thmTDispAxTreeRecNd_param fT sT pT aT bT
