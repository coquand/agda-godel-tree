{-# OPTIONS --safe --without-K --exact-split #-}

module BRA.Thm12.Param.AxComp where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Deriv
open import BRA.Thm.ThmT
  using ( thmT ; tagCode_axComp ; thmTDispAxComp_param )

parEncAxComp : Fun1 -> Fun1 -> Term -> Term
parEncAxComp f g xT =
  ap2 Pair tagCode_axComp
    (ap2 Pair (reify (codeF1 f))
      (ap2 Pair (reify (codeF1 g)) xT))

parOutAxComp : Fun1 -> Fun1 -> Term -> Term
parOutAxComp f g xT =
  ap2 Pair
    (ap2 Pair (reify tagAp1)
      (ap2 Pair (ap2 Pair (reify (leftT (codeF1 (Comp I I))))
                          (ap2 Pair (reify (codeF1 f))
                                    (reify (codeF1 g))))
                xT))
    (ap2 Pair (reify tagAp1)
      (ap2 Pair (reify (codeF1 f))
        (ap2 Pair (reify tagAp1)
          (ap2 Pair (reify (codeF1 g)) xT))))

parDispAxComp : (f g : Fun1) (xT : Term) ->
  Deriv (atomic (eqn (ap1 thmT (parEncAxComp f g xT)) (parOutAxComp f g xT)))
parDispAxComp f g xT = thmTDispAxComp_param f g xT
