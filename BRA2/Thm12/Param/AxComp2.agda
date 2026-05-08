{-# OPTIONS --safe --without-K --exact-split #-}

module BRA2.Thm12.Param.AxComp2 where

open import BRA2.Base
open import BRA2.Term
open import BRA2.Formula
open import BRA2.Deriv
open import BRA2.Thm.ThmT
  using ( thmT ; tagCode_axComp2 ; thmTDispAxComp2_param )

parEncAxComp2 : Fun2 -> Fun1 -> Fun1 -> Term -> Term
parEncAxComp2 h' f g xT =
  ap2 Pair tagCode_axComp2
    (ap2 Pair (reify (codeF2 h'))
      (ap2 Pair (reify (codeF1 f))
        (ap2 Pair (reify (codeF1 g)) xT)))

parOutAxComp2 : Fun2 -> Fun1 -> Fun1 -> Term -> Term
parOutAxComp2 h' f g xT =
  ap2 Pair
    (ap2 Pair (reify tagAp1)
      (ap2 Pair (ap2 Pair (reify (leftT (codeF1 (Comp2 IfLf I I))))
                          (ap2 Pair (reify (codeF2 h'))
                            (ap2 Pair (reify (codeF1 f)) (reify (codeF1 g)))))
                xT))
    (ap2 Pair (reify tagAp2)
      (ap2 Pair (reify (codeF2 h'))
        (ap2 Pair (ap2 Pair (reify tagAp1)
                            (ap2 Pair (reify (codeF1 f)) xT))
                  (ap2 Pair (reify tagAp1)
                            (ap2 Pair (reify (codeF1 g)) xT)))))

parDispAxComp2 : (h' : Fun2) (f g : Fun1) (xT : Term) ->
  Deriv (atomic (eqn (ap1 thmT (parEncAxComp2 h' f g xT))
                     (parOutAxComp2 h' f g xT)))
parDispAxComp2 h' f g xT = thmTDispAxComp2_param h' f g xT
