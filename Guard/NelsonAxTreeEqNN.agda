{-# OPTIONS --safe --without-K --exact-split #-}

-- NelsonAxTreeEqNN.agda
-- Nelson base case: axTreeEqNN (tag 16).
-- Encoding: Pair(tag16T, Pair(a1C, Pair(a2C, Pair(b1C, b2C))))
-- case16 = mkEqF
--   (mkAp2F (kF2 treeeqCF) (mkAp2F (kF2 pairCF) origA origB1)
--                           (mkAp2F (kF2 pairCF) origB2a origB2b))
--   (mkAp2F (kF2 iflfCF) (mkAp2F (kF2 treeeqCF) origA origB2a)
--                         (mkAp2F (kF2 pairCF) (mkAp2F (kF2 treeeqCF) origB1 origB2b) (kF2 oneC)))
-- Result: Pair(mkAp2(TreeEq, Pair(a1,a2), Pair(b1,b2)),
--              mkAp2(IfLf, mkAp2(TreeEq,a1,b1), Pair(mkAp2(TreeEq,a2,b2), Pair(O,O))))

module Guard.NelsonAxTreeEqNN where

open import Guard.Base
open import Guard.Term
open import Guard.Step
open import Guard.StepReduce
open import Guard.ThFunTForDefs
open import Guard.ThFunTForCases2
open import Guard.ThFunTFor
open import Guard.NelsonDispatch
open import Guard.NelsonExtractors

private
  tag16T : Term ; tag16T = reify (natCode n16)
  oC : Term ; oC = ap2 Pair O O
  treeeqCF : Term ; treeeqCF = reify (codeF2 TreeEq)
  pairCF : Term ; pairCF = reify (codeF2 Pair)
  iflfCF : Term ; iflfCF = reify (codeF2 IfLf)
  reifyTagAp2 : Term ; reifyTagAp2 = ap2 Pair O (ap2 Pair O (ap2 Pair O O))
  oneC : Term ; oneC = ap2 Pair reifyTagAp2 (ap2 Pair pairCF (ap2 Pair oC oC))

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

nelsonAxTreeEqNN : (a1C a2C b1C b2C : Term) -> {hyp : Equation} ->
  let pairA = ap2 Pair (reify tagAp2) (ap2 Pair pairCF (ap2 Pair a1C a2C))
      pairB = ap2 Pair (reify tagAp2) (ap2 Pair pairCF (ap2 Pair b1C b2C))
      teqA1B1 = ap2 Pair (reify tagAp2) (ap2 Pair treeeqCF (ap2 Pair a1C b1C))
      teqA2B2 = ap2 Pair (reify tagAp2) (ap2 Pair treeeqCF (ap2 Pair a2C b2C))
      innerPair = ap2 Pair (reify tagAp2) (ap2 Pair pairCF (ap2 Pair teqA2B2 oneC))
  in Deriv hyp (eqn (ap1 thFunTFor (ap2 Pair tag16T (ap2 Pair a1C (ap2 Pair a2C (ap2 Pair b1C b2C)))))
                    (ap2 Pair (ap2 Pair (reify tagAp2) (ap2 Pair treeeqCF (ap2 Pair pairA pairB)))
                              (ap2 Pair (reify tagAp2) (ap2 Pair iflfCF (ap2 Pair teqA1B1 innerPair)))))
nelsonAxTreeEqNN a1C a2C b1C b2C =
  let origT = ap2 Pair tag16T (ap2 Pair a1C (ap2 Pair a2C (ap2 Pair b1C b2C)))
      recsT = ap2 Pair (ap1 thFunTFor tag16T) (ap1 thFunTFor (ap2 Pair a1C (ap2 Pair a2C (ap2 Pair b1C b2C))))
      pairA = ap2 Pair (reify tagAp2) (ap2 Pair pairCF (ap2 Pair a1C a2C))
      pairB = ap2 Pair (reify tagAp2) (ap2 Pair pairCF (ap2 Pair b1C b2C))
      teqA1B1 = ap2 Pair (reify tagAp2) (ap2 Pair treeeqCF (ap2 Pair a1C b1C))
      teqA2B2 = ap2 Pair (reify tagAp2) (ap2 Pair treeeqCF (ap2 Pair a2C b2C))
      innerPair = ap2 Pair (reify tagAp2) (ap2 Pair pairCF (ap2 Pair teqA2B2 oneC))

      step12 = ruleTrans (phase1Nd tag16T a1C (ap2 Pair a2C (ap2 Pair b1C b2C)))
                         (ndDispatchToCase16 (ap2 Pair a1C (ap2 Pair a2C (ap2 Pair b1C b2C))) recsT)

      oaR = origARed tag16T a1C (ap2 Pair a2C (ap2 Pair b1C b2C)) recsT
      ob1R = origB1Red tag16T a1C a2C (ap2 Pair b1C b2C) recsT
      ob2aR = origB2aRed tag16T a1C a2C b1C b2C recsT
      ob2bR = origB2bRed tag16T a1C a2C b1C b2C recsT

      kTrR : {h : Equation} -> Deriv h (eqn (ap2 (kF2 treeeqCF) origT recsT) treeeqCF)
      kTrR = constF2Red treeeqCF origT recsT
      kPairR : {h : Equation} -> Deriv h (eqn (ap2 (kF2 pairCF) origT recsT) pairCF)
      kPairR = constF2Red pairCF origT recsT
      kIfR : {h : Equation} -> Deriv h (eqn (ap2 (kF2 iflfCF) origT recsT) iflfCF)
      kIfR = constF2Red iflfCF origT recsT
      kOneCR : {h : Equation} -> Deriv h (eqn (ap2 (kF2 oneC) origT recsT) oneC)
      kOneCR = constF2Red oneC origT recsT

      -- mkAp2F (kF2 pairCF) origA origB1 -> pairA
      pairAR = mkAp2FRed (kF2 pairCF) origA origB1 origT recsT pairCF a1C a2C kPairR oaR ob1R

      -- mkAp2F (kF2 pairCF) origB2a origB2b -> pairB
      pairBR = mkAp2FRed (kF2 pairCF) origB2a origB2b origT recsT pairCF b1C b2C kPairR ob2aR ob2bR

      -- LHS: mkAp2F (kF2 treeeqCF) pairAF pairBF
      leftRed = mkAp2FRed (kF2 treeeqCF) (mkAp2F (kF2 pairCF) origA origB1)
                  (mkAp2F (kF2 pairCF) origB2a origB2b)
                  origT recsT treeeqCF pairA pairB kTrR pairAR pairBR

      -- mkAp2F (kF2 treeeqCF) origA origB2a -> teqA1B1
      teqA1B1R = mkAp2FRed (kF2 treeeqCF) origA origB2a origT recsT treeeqCF a1C b1C kTrR oaR ob2aR

      -- mkAp2F (kF2 treeeqCF) origB1 origB2b -> teqA2B2
      teqA2B2R = mkAp2FRed (kF2 treeeqCF) origB1 origB2b origT recsT treeeqCF a2C b2C kTrR ob1R ob2bR

      -- mkAp2F (kF2 pairCF) teqA2B2F (kF2 oneC) -> innerPair
      innerPairR = mkAp2FRed (kF2 pairCF) (mkAp2F (kF2 treeeqCF) origB1 origB2b) (kF2 oneC)
                     origT recsT pairCF teqA2B2 oneC kPairR teqA2B2R kOneCR

      -- RHS: mkAp2F (kF2 iflfCF) teqA1B1F innerPairF
      rightRed = mkAp2FRed (kF2 iflfCF) (mkAp2F (kF2 treeeqCF) origA origB2a)
                   (mkAp2F (kF2 pairCF) (mkAp2F (kF2 treeeqCF) origB1 origB2b) (kF2 oneC))
                   origT recsT iflfCF teqA1B1 innerPair kIfR teqA1B1R innerPairR

      step4 = mkEqFRed (mkAp2F (kF2 treeeqCF) (mkAp2F (kF2 pairCF) origA origB1)
                                                (mkAp2F (kF2 pairCF) origB2a origB2b))
                        (mkAp2F (kF2 iflfCF) (mkAp2F (kF2 treeeqCF) origA origB2a)
                                             (mkAp2F (kF2 pairCF) (mkAp2F (kF2 treeeqCF) origB1 origB2b) (kF2 oneC)))
                origT recsT
                (ap2 Pair (reify tagAp2) (ap2 Pair treeeqCF (ap2 Pair pairA pairB)))
                (ap2 Pair (reify tagAp2) (ap2 Pair iflfCF (ap2 Pair teqA1B1 innerPair)))
                leftRed rightRed
  in
  ruleTrans step12 step4
