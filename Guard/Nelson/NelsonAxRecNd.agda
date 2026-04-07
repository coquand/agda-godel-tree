{-# OPTIONS --safe --without-K --exact-split #-}

-- NelsonAxRecNd.agda
-- Nelson base case: axRecNd (tag 10).
-- Encoding: Pair(tag10T, Pair(zC, Pair(sC, Pair(aC, bC))))
-- case10 = mkEqF (mkAp1F recF pairAB)
--                (mkAp2F origB1 pairAB (mkAp2F (kF2 pairCF) (mkAp1F recF origB2a) (mkAp1F recF origB2b)))
-- where recF = codeRecF origA origB1, pairAB = mkAp2F (kF2 pairCF) origB2a origB2b
-- Result: Pair(mkAp1(Rec(z,s), Pair(a,b)),
--              mkAp2(s, Pair(a,b), Pair(mkAp1(Rec(z,s),a), mkAp1(Rec(z,s),b))))

module Guard.Nelson.NelsonAxRecNd where

open import Guard.Base
open import Guard.Term
open import Guard.Step
open import Guard.StepReduce
open import Guard.ThFunTForDefs
open import Guard.ThFunTForCases2
open import Guard.ThFunTFor
open import Guard.Nelson.NelsonDispatch
open import Guard.Nelson.NelsonExtractors

private
  tag10T : Term ; tag10T = reify (natCode n10)
  oC : Term ; oC = ap2 Pair O O
  pairCF : Term ; pairCF = reify (codeF2 Pair)
  n31 : Nat ; n31 = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))))))))))))))))))))
  recTag : Term ; recTag = reify (natCode n31)

  -- Deep extractor reductions
  origB2aRed : (tagT x b1 b2a b2b recs : Term) -> {hyp : Equation} ->
    Deriv hyp (eqn (ap2 origB2a (ap2 Pair tagT (ap2 Pair x (ap2 Pair b1 (ap2 Pair b2a b2b)))) recs) b2a)
  origB2aRed tagT x b1 b2a b2b recs =
    let origT = ap2 Pair tagT (ap2 Pair x (ap2 Pair b1 (ap2 Pair b2a b2b)))
    in ruleTrans (axPost Fst origB2 origT recs)
       (ruleTrans (cong1 Fst (origB2Red tagT x b1 (ap2 Pair b2a b2b) recs))
                  (axFst b2a b2b))

  origB2bRed : (tagT x b1 b2a b2b recs : Term) -> {hyp : Equation} ->
    Deriv hyp (eqn (ap2 origB2b (ap2 Pair tagT (ap2 Pair x (ap2 Pair b1 (ap2 Pair b2a b2b)))) recs) b2b)
  origB2bRed tagT x b1 b2a b2b recs =
    let origT = ap2 Pair tagT (ap2 Pair x (ap2 Pair b1 (ap2 Pair b2a b2b)))
    in ruleTrans (axPost Snd origB2 origT recs)
       (ruleTrans (cong1 Snd (origB2Red tagT x b1 (ap2 Pair b2a b2b) recs))
                  (axSnd b2a b2b))

nelsonAxRecNd : (zC sC aC bC : Term) -> {hyp : Equation} ->
  let recCode = ap2 Pair recTag (ap2 Pair zC sC)
      pairAB = ap2 Pair (reify tagAp2) (ap2 Pair pairCF (ap2 Pair aC bC))
      recA = ap2 Pair (reify tagAp1) (ap2 Pair recCode aC)
      recB = ap2 Pair (reify tagAp1) (ap2 Pair recCode bC)
      recPair = ap2 Pair (reify tagAp2) (ap2 Pair pairCF (ap2 Pair recA recB))
  in Deriv hyp (eqn (ap1 thFunTFor (ap2 Pair tag10T (ap2 Pair zC (ap2 Pair sC (ap2 Pair aC bC)))))
                    (ap2 Pair (ap2 Pair (reify tagAp1) (ap2 Pair recCode pairAB))
                              (ap2 Pair (reify tagAp2) (ap2 Pair sC (ap2 Pair pairAB recPair)))))
nelsonAxRecNd zC sC aC bC =
  let origT = ap2 Pair tag10T (ap2 Pair zC (ap2 Pair sC (ap2 Pair aC bC)))
      recsT = ap2 Pair (ap1 thFunTFor tag10T) (ap1 thFunTFor (ap2 Pair zC (ap2 Pair sC (ap2 Pair aC bC))))
      recCode = ap2 Pair recTag (ap2 Pair zC sC)
      pairAB = ap2 Pair (reify tagAp2) (ap2 Pair pairCF (ap2 Pair aC bC))
      recA = ap2 Pair (reify tagAp1) (ap2 Pair recCode aC)
      recB = ap2 Pair (reify tagAp1) (ap2 Pair recCode bC)
      recPair = ap2 Pair (reify tagAp2) (ap2 Pair pairCF (ap2 Pair recA recB))

      step12 = ruleTrans (phase1Nd tag10T zC (ap2 Pair sC (ap2 Pair aC bC)))
                         (ndDispatchToCase10 (ap2 Pair zC (ap2 Pair sC (ap2 Pair aC bC))) recsT)

      oaR = origARed tag10T zC (ap2 Pair sC (ap2 Pair aC bC)) recsT
      ob1R = origB1Red tag10T zC sC (ap2 Pair aC bC) recsT
      ob2aR = origB2aRed tag10T zC sC aC bC recsT
      ob2bR = origB2bRed tag10T zC sC aC bC recsT

      -- recF = Fan (kF2 recTag) (Fan origA origB1 Pair) Pair
      -- Reduces to Pair(recTag, Pair(zC, sC)) = recCode
      recCodeR : {h : Equation} -> Deriv h (eqn (ap2 (Fan (kF2 recTag) (Fan origA origB1 Pair) Pair) origT recsT) recCode)
      recCodeR = ruleTrans (axFan (kF2 recTag) (Fan origA origB1 Pair) Pair origT recsT)
                 (ruleTrans (congL Pair (ap2 (Fan origA origB1 Pair) origT recsT)
                               (constF2Red recTag origT recsT))
                 (congR Pair recTag
                   (ruleTrans (axFan origA origB1 Pair origT recsT)
                   (ruleTrans (congL Pair (ap2 origB1 origT recsT) oaR)
                              (congR Pair zC ob1R)))))

      kPairR : {h : Equation} -> Deriv h (eqn (ap2 (kF2 pairCF) origT recsT) pairCF)
      kPairR = constF2Red pairCF origT recsT

      -- pairAB = mkAp2F (kF2 pairCF) origB2a origB2b
      pairABR = mkAp2FRed (kF2 pairCF) origB2a origB2b origT recsT pairCF aC bC kPairR ob2aR ob2bR

      -- recF = codeRecF origA origB1
      recF : Fun2 ; recF = Fan (kF2 recTag) (Fan origA origB1 Pair) Pair

      -- LHS: mkAp1F recF pairAB -> Pair(tagAp1T, Pair(recCode, pairAB))
      leftRed = mkAp1FRed recF (mkAp2F (kF2 pairCF) origB2a origB2b) origT recsT recCode pairAB recCodeR pairABR

      -- mkAp1F recF origB2a -> Pair(tagAp1T, Pair(recCode, aC)) = recA
      recAR = mkAp1FRed recF origB2a origT recsT recCode aC recCodeR ob2aR

      -- mkAp1F recF origB2b -> Pair(tagAp1T, Pair(recCode, bC)) = recB
      recBR = mkAp1FRed recF origB2b origT recsT recCode bC recCodeR ob2bR

      -- mkAp2F (kF2 pairCF) (mkAp1F recF origB2a) (mkAp1F recF origB2b) -> recPair
      recPairR = mkAp2FRed (kF2 pairCF) (mkAp1F recF origB2a) (mkAp1F recF origB2b)
                   origT recsT pairCF recA recB kPairR recAR recBR

      -- RHS: mkAp2F origB1 pairAB recPairF
      rightRed = mkAp2FRed origB1 (mkAp2F (kF2 pairCF) origB2a origB2b)
                   (mkAp2F (kF2 pairCF) (mkAp1F recF origB2a) (mkAp1F recF origB2b))
                   origT recsT sC pairAB recPair ob1R pairABR recPairR

      step4 = mkEqFRed (mkAp1F recF (mkAp2F (kF2 pairCF) origB2a origB2b))
                        (mkAp2F origB1 (mkAp2F (kF2 pairCF) origB2a origB2b)
                                       (mkAp2F (kF2 pairCF) (mkAp1F recF origB2a) (mkAp1F recF origB2b)))
                origT recsT
                (ap2 Pair (reify tagAp1) (ap2 Pair recCode pairAB))
                (ap2 Pair (reify tagAp2) (ap2 Pair sC (ap2 Pair pairAB recPair)))
                leftRed rightRed
  in
  ruleTrans step12 step4
