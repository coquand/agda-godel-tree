{-# OPTIONS --safe --without-K --exact-split #-}

-- NelsonAxComp.agda
-- Nelson base case: axComp (tag 4).
-- Encoding: Pair(tag4T, Pair(fC, Pair(gC, tC)))
-- case4 = mkEqF (mkAp1F compCode origB2) (mkAp1F origA (mkAp1F origB1 origB2))
-- where compCode = Fan (kF2 codeCompTag) (Fan origA origB1 Pair) Pair
-- Result: Pair(mkAp1(Comp(f,g), t), mkAp1(f, mkAp1(g, t)))

module Guard.Nelson.NelsonAxComp where

open import Guard.Base
open import Guard.Term
open import Guard.Step
open import Guard.StepReduce
open import Guard.ThFunTForDefs
open import Guard.ThFunTForCases1
open import Guard.ThFunTFor
open import Guard.Nelson.NelsonDispatch
open import Guard.Nelson.NelsonExtractors

private
  tag4T : Term ; tag4T = reify (natCode n4)
  n26 : Nat ; n26 = suc n25
  n27 : Nat ; n27 = suc n26
  n28 : Nat ; n28 = suc n27
  n29 : Nat ; n29 = suc n28
  codeCompTag : Term ; codeCompTag = reify (natCode n29)

nelsonAxComp : (fC gC tC : Term) -> {hyp : Equation} ->
  let compCode = ap2 Pair codeCompTag (ap2 Pair fC gC)
      gOfT = ap2 Pair (reify tagAp1) (ap2 Pair gC tC)
  in Deriv hyp (eqn (ap1 thFunTFor (ap2 Pair tag4T (ap2 Pair fC (ap2 Pair gC tC))))
                    (ap2 Pair (ap2 Pair (reify tagAp1) (ap2 Pair compCode tC))
                              (ap2 Pair (reify tagAp1) (ap2 Pair fC gOfT))))
nelsonAxComp fC gC tC =
  let origT = ap2 Pair tag4T (ap2 Pair fC (ap2 Pair gC tC))
      recsT = ap2 Pair (ap1 thFunTFor tag4T) (ap1 thFunTFor (ap2 Pair fC (ap2 Pair gC tC)))
      compCode = ap2 Pair codeCompTag (ap2 Pair fC gC)
      gOfT = ap2 Pair (reify tagAp1) (ap2 Pair gC tC)

      step12 = ruleTrans (phase1Nd tag4T fC (ap2 Pair gC tC))
                         (ndDispatchToCase4 (ap2 Pair fC (ap2 Pair gC tC)) recsT)

      -- origA = fC
      oaR = origARed tag4T fC (ap2 Pair gC tC) recsT
      -- origB1 = Fst(origB) = Fst(Pair(gC, tC)) = gC
      ob1R = origB1Red tag4T fC gC tC recsT
      -- origB2 = Snd(origB) = Snd(Pair(gC, tC)) = tC
      ob2R = origB2Red tag4T fC gC tC recsT

      -- Comp code: Fan (kF2 codeCompTag) (Fan origA origB1 Pair) Pair
      -- = Pair(codeCompTag, Pair(fC, gC)) = compCode
      compCodeR : {h : Equation} -> Deriv h (eqn (ap2 (Fan (kF2 codeCompTag) (Fan origA origB1 Pair) Pair) origT recsT) compCode)
      compCodeR = ruleTrans (axFan (kF2 codeCompTag) (Fan origA origB1 Pair) Pair origT recsT)
                  (ruleTrans (congL Pair (ap2 (Fan origA origB1 Pair) origT recsT)
                                (constF2Red codeCompTag origT recsT))
                  (congR Pair codeCompTag
                    (ruleTrans (axFan origA origB1 Pair origT recsT)
                    (ruleTrans (congL Pair (ap2 origB1 origT recsT) oaR)
                               (congR Pair fC ob1R)))))

      -- LHS: mkAp1F compCode origB2 -> Pair(tagAp1T, Pair(compCode, tC))
      leftRed = mkAp1FRed (Fan (kF2 codeCompTag) (Fan origA origB1 Pair) Pair)
                  origB2 origT recsT compCode tC compCodeR ob2R

      -- mkAp1F origB1 origB2 -> Pair(tagAp1T, Pair(gC, tC)) = gOfT
      innerR = mkAp1FRed origB1 origB2 origT recsT gC tC ob1R ob2R

      -- RHS: mkAp1F origA (mkAp1F origB1 origB2) -> Pair(tagAp1T, Pair(fC, gOfT))
      rightRed = mkAp1FRed origA (mkAp1F origB1 origB2) origT recsT fC gOfT oaR innerR

      step4 = mkEqFRed (mkAp1F (Fan (kF2 codeCompTag) (Fan origA origB1 Pair) Pair) origB2)
                        (mkAp1F origA (mkAp1F origB1 origB2))
                origT recsT
                (ap2 Pair (reify tagAp1) (ap2 Pair compCode tC))
                (ap2 Pair (reify tagAp1) (ap2 Pair fC gOfT))
                leftRed rightRed
  in
  ruleTrans step12 step4
