{-# OPTIONS --safe --without-K --exact-split #-}

-- NelsonAxLift.agda
-- Nelson base case: axLift (tag 6).
-- Encoding: Pair(tag6T, Pair(fC, Pair(aC, bC)))
-- case6 = mkEqF (mkAp2F liftCode origB1 origB2) (mkAp1F origA origB1)
-- where liftCode = Fan (kF2 codeLiftTag) origA Pair
-- Result: Pair(mkAp2(Lift(f), a, b), mkAp1(f, a))

module Guard.NelsonAxLift where

open import Guard.Base
open import Guard.Term
open import Guard.Step
open import Guard.StepReduce
open import Guard.ThFunTForDefs
open import Guard.ThFunTForCases1
open import Guard.ThFunTFor
open import Guard.NelsonDispatch
open import Guard.NelsonExtractors

private
  tag6T : Term ; tag6T = reify (natCode n6)
  n26 : Nat ; n26 = suc n25
  n27 : Nat ; n27 = suc n26
  n28 : Nat ; n28 = suc n27
  codeLiftTag : Term ; codeLiftTag = reify (natCode n28)

nelsonAxLift : (fC aC bC : Term) -> {hyp : Equation} ->
  let liftCode = ap2 Pair codeLiftTag fC
  in Deriv hyp (eqn (ap1 thFunTFor (ap2 Pair tag6T (ap2 Pair fC (ap2 Pair aC bC))))
                    (ap2 Pair (ap2 Pair (reify tagAp2) (ap2 Pair liftCode (ap2 Pair aC bC)))
                              (ap2 Pair (reify tagAp1) (ap2 Pair fC aC))))
nelsonAxLift fC aC bC =
  let origT = ap2 Pair tag6T (ap2 Pair fC (ap2 Pair aC bC))
      recsT = ap2 Pair (ap1 thFunTFor tag6T) (ap1 thFunTFor (ap2 Pair fC (ap2 Pair aC bC)))
      liftCode = ap2 Pair codeLiftTag fC

      step12 = ruleTrans (phase1Nd tag6T fC (ap2 Pair aC bC))
                         (ndDispatchToCase6 (ap2 Pair fC (ap2 Pair aC bC)) recsT)

      oaR = origARed tag6T fC (ap2 Pair aC bC) recsT
      ob1R = origB1Red tag6T fC aC bC recsT
      ob2R = origB2Red tag6T fC aC bC recsT

      -- Lift code: Fan (kF2 codeLiftTag) origA Pair
      -- Reduces to Pair(codeLiftTag, fC) = liftCode
      liftCodeR : {h : Equation} -> Deriv h (eqn (ap2 (Fan (kF2 codeLiftTag) origA Pair) origT recsT) liftCode)
      liftCodeR = ruleTrans (axFan (kF2 codeLiftTag) origA Pair origT recsT)
                  (ruleTrans (congL Pair (ap2 origA origT recsT) (constF2Red codeLiftTag origT recsT))
                             (congR Pair codeLiftTag oaR))

      -- LHS: mkAp2F liftCode origB1 origB2
      leftRed = mkAp2FRed (Fan (kF2 codeLiftTag) origA Pair) origB1 origB2
                  origT recsT liftCode aC bC liftCodeR ob1R ob2R

      -- RHS: mkAp1F origA origB1
      rightRed = mkAp1FRed origA origB1 origT recsT fC aC oaR ob1R

      step4 = mkEqFRed (mkAp2F (Fan (kF2 codeLiftTag) origA Pair) origB1 origB2)
                        (mkAp1F origA origB1)
                origT recsT
                (ap2 Pair (reify tagAp2) (ap2 Pair liftCode (ap2 Pair aC bC)))
                (ap2 Pair (reify tagAp1) (ap2 Pair fC aC))
                leftRed rightRed
  in
  ruleTrans step12 step4
