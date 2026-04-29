{-# OPTIONS --safe --without-K --exact-split #-}

module BRA.Thm12.Param.AxFan where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Deriv
open import BRA.Thm.ThmT
  using ( thmT ; tagCode_axFan ; thmTDispAxFan_param )

parEncAxFan : Fun2 -> Fun2 -> Fun2 -> Term -> Term -> Term
parEncAxFan h1' h2' h' aT bT =
  ap2 Pair tagCode_axFan
    (ap2 Pair (reify (codeF2 h1'))
      (ap2 Pair (reify (codeF2 h2'))
        (ap2 Pair (reify (codeF2 h'))
          (ap2 Pair aT bT))))

parOutAxFan : Fun2 -> Fun2 -> Fun2 -> Term -> Term -> Term
parOutAxFan h1' h2' h' aT bT =
  ap2 Pair
    (ap2 Pair (reify tagAp2)
      (ap2 Pair (ap2 Pair (reify (leftT (codeF2 (Fan IfLf IfLf IfLf))))
                          (ap2 Pair (reify (codeF2 h1'))
                            (ap2 Pair (reify (codeF2 h2'))
                              (reify (codeF2 h')))))
                (ap2 Pair aT bT)))
    (ap2 Pair (reify tagAp2)
      (ap2 Pair (reify (codeF2 h'))
        (ap2 Pair (ap2 Pair (reify tagAp2)
                            (ap2 Pair (reify (codeF2 h1')) (ap2 Pair aT bT)))
                  (ap2 Pair (reify tagAp2)
                            (ap2 Pair (reify (codeF2 h2')) (ap2 Pair aT bT))))))

parDispAxFan : (h1' h2' h' : Fun2) (aT bT : Term) ->
  Deriv (atomic (eqn (ap1 thmT (parEncAxFan h1' h2' h' aT bT))
                     (parOutAxFan h1' h2' h' aT bT)))
parDispAxFan h1' h2' h' aT bT = thmTDispAxFan_param h1' h2' h' aT bT
