{-# OPTIONS --safe --without-K --exact-split #-}

-- NelsonRuleTransOPair.agda
-- Variant of NelsonRuleTransFull for O-Pair-tagged sp1.
--
-- sp1 = Pair(O, Pair(Pair(c1',c2'), d')) — tag-0 sub-proof (axI encoding)
-- sp2 = Pair(Pair(c1, c2), d1)           — PairPair-tagged
--
-- The inner passthrough uses ndDispatchOPairMiss instead of ndDispatchPairMiss.
-- Everything else is identical to NelsonRuleTransFull.

module Guard.NelsonRuleTransOPair where

open import Guard.Base
open import Guard.Term
open import Guard.Step
open import Guard.StepReduce
open import Guard.ThFunTForDefs
open import Guard.ThFunTFor
open import Guard.ThFunTForCorrectDefs hiding (natCodeNeq)
open import Guard.PairPassthroughAll
open import Guard.GodelII using (treeEqSelf)
open import Guard.NelsonAxRefl using (natCodeNeq ; natAdd)
open import Guard.NelsonDispatch

private
  poo : Term ; poo = ap2 Pair O O
  tag19T : Term ; tag19T = reify (natCode n19)

------------------------------------------------------------------------
-- nelsonRuleTransOPair:
-- sp1 = Pair(O, Pair(Pair(e1, e2), e3))     [O-Pair, e.g. axI encoding]
-- sp2 = Pair(Pair(c1, c2), d1)              [PairPair-tagged]
--
-- thFunTFor(Pair(tag19T, Pair(sp1, sp2)))
--   = Pair(Fst(thFunTFor(sp1)), Snd(thFunTFor(sp2)))

nelsonRuleTransOPair :
  (e1 e2 e3 c1 c2 d1 : Term) -> {hyp : Equation} ->
  let sp1 = ap2 Pair O (ap2 Pair (ap2 Pair e1 e2) e3)
      sp2 = ap2 Pair (ap2 Pair c1 c2) d1
  in Deriv hyp (eqn (ap1 thFunTFor (ap2 Pair tag19T (ap2 Pair sp1 sp2)))
                    (ap2 Pair (ap1 Fst (ap1 thFunTFor sp1))
                              (ap1 Snd (ap1 thFunTFor sp2))))
nelsonRuleTransOPair e1 e2 e3 c1 c2 d1 =
  let sp1 = ap2 Pair O (ap2 Pair (ap2 Pair e1 e2) e3)
      sp2 = ap2 Pair (ap2 Pair c1 c2) d1
      origT = ap2 Pair tag19T (ap2 Pair sp1 sp2)
      recsSp = ap2 Pair (ap1 thFunTFor sp1) (ap1 thFunTFor sp2)
      innerRec = ap1 thFunTFor (ap2 Pair sp1 sp2)
      recsT = ap2 Pair (ap1 thFunTFor tag19T) innerRec
  in
  -- Phase 1+2: thFunTFor(origT) -> case19(origT, recsT)
  let step12 = ruleTrans (phase1Nd tag19T sp1 sp2)
                         (ndDispatchToCase19 (ap2 Pair sp1 sp2) recsT)
  in
  -- Phase 3: Inner passthrough using ndDispatchOPairMiss
  -- thFunTFor(Pair(sp1, sp2)): sp1 = Pair(O, Pair(Pair(e1,e2), e3))
  -- guardNd(sp1, Pair(c1,c2), d1, recsSp) checks Snd(Pair(sp1,sp2)) = sp2 = Pair(...)
  let passInner = ruleTrans (axRecNd O thFunStep sp1 sp2)
                  (ruleTrans (guardNd sp1 (ap2 Pair c1 c2) d1 recsSp)
                  (ruleTrans (ndDispatchOPairMiss e1 e2 e3 sp2 recsSp)
                  (ruleTrans (axPost Snd Pair (ap2 Pair sp1 sp2) recsSp)
                             (axSnd (ap2 Pair sp1 sp2) recsSp))))
  in
  -- Phase 4: case19 extractors (identical to NelsonRuleTransFull)
  let snd2 = ruleTrans (axPost Snd Pair origT recsT) (axSnd origT recsT)
      ps = ruleTrans (axPost Snd sndArg2 origT recsT) (cong1 Snd snd2)
      sndR = axSnd (ap1 thFunTFor tag19T) innerRec
      full = ruleTrans ps (ruleTrans sndR passInner)

      raL = ruleTrans (axPost Fst recsA origT recsT)
            (ruleTrans (cong1 Fst (ruleTrans (axPost Fst (Post Snd sndArg2) origT recsT) (cong1 Fst full)))
                       (cong1 Fst (axFst (ap1 thFunTFor sp1) (ap1 thFunTFor sp2))))
      rbR = ruleTrans (axPost Snd recsB origT recsT)
            (ruleTrans (cong1 Snd (ruleTrans (axPost Snd (Post Snd sndArg2) origT recsT) (cong1 Snd full)))
                       (cong1 Snd (axSnd (ap1 thFunTFor sp1) (ap1 thFunTFor sp2))))
      step4 = ruleTrans (axFan recsAL recsBR Pair origT recsT)
              (ruleTrans (congL Pair (ap2 recsBR origT recsT) raL)
                         (congR Pair (ap1 Fst (ap1 thFunTFor sp1)) rbR))
  in
  ruleTrans step12 step4
