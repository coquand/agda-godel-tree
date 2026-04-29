{-# OPTIONS --safe --without-K --exact-split #-}

module BRA.Thm12.Param.AxPost where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Deriv
open import BRA.Thm.ThmT
  using ( thmT ; tagCode_axPost ; thmTDispAxPost_param )

parEncAxPost : Fun1 -> Fun2 -> Term -> Term -> Term
parEncAxPost f h' aT bT =
  ap2 Pair tagCode_axPost
    (ap2 Pair (reify (codeF1 f))
      (ap2 Pair (reify (codeF2 h'))
        (ap2 Pair aT bT)))

parOutAxPost : Fun1 -> Fun2 -> Term -> Term -> Term
parOutAxPost f h' aT bT =
  ap2 Pair
    (ap2 Pair (reify tagAp2)
      (ap2 Pair (ap2 Pair (reify (leftT (codeF2 (Post I IfLf))))
                          (ap2 Pair (reify (codeF1 f))
                                    (reify (codeF2 h'))))
                (ap2 Pair aT bT)))
    (ap2 Pair (reify tagAp1)
      (ap2 Pair (reify (codeF1 f))
        (ap2 Pair (reify tagAp2)
          (ap2 Pair (reify (codeF2 h'))
            (ap2 Pair aT bT)))))

parDispAxPost : (f : Fun1) (h' : Fun2) (aT bT : Term) ->
  Deriv (atomic (eqn (ap1 thmT (parEncAxPost f h' aT bT))
                     (parOutAxPost f h' aT bT)))
parDispAxPost f h' aT bT = thmTDispAxPost_param f h' aT bT
