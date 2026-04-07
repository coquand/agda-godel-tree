{-# OPTIONS --safe --without-K --exact-split #-}

-- NelsonExtractors.agda
-- Shared extractor reduction lemmas for Nelson case proofs.
--
-- For orig = Pair(tagT, Pair(x, y)):
--   origARed: origA(orig, recs) = x
--   origBRed: origB(orig, recs) = y
--
-- For orig = Pair(tagT, Pair(Pair(a1,a2), y)):
--   origALRed: origAL(orig, recs) = a1
--   origARRed: origAR(orig, recs) = a2
--
-- For recs = Pair(thFunTFor(tagT), innerRec) with passthrough:
--   recsPassthrough: chain from sndArg2 through Snd(recs) to passthrough result
--   recsBLRed / recsBRRed: extract L/R from sub-proof thFunTFor result

module Guard.Nelson.NelsonExtractors where

open import Guard.Base
open import Guard.Term
open import Guard.Step
open import Guard.StepReduce
open import Guard.ThFunTForDefs
open import Guard.ThFunTFor
open import Guard.ThFunTForCorrectDefs
open import Guard.PairPassthroughAll

------------------------------------------------------------------------
-- origA reduction: Fst(Snd(orig))
-- For orig = Pair(tagT, Pair(x, y)):
--   origA(orig, recs) = Fst(Snd(Pair(tagT, Pair(x,y)))) = Fst(Pair(x,y)) = x

origARed : (tagT x y recs : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap2 origA (ap2 Pair tagT (ap2 Pair x y)) recs) x)
origARed tagT x y recs =
  ruleTrans (axLift (Comp Fst Snd) (ap2 Pair tagT (ap2 Pair x y)) recs)
  (ruleTrans (axComp Fst Snd (ap2 Pair tagT (ap2 Pair x y)))
  (ruleTrans (cong1 Fst (axSnd tagT (ap2 Pair x y)))
             (axFst x y)))

------------------------------------------------------------------------
-- origB reduction: Snd(Snd(orig))
-- For orig = Pair(tagT, Pair(x, y)):
--   origB(orig, recs) = Snd(Snd(Pair(tagT, Pair(x,y)))) = Snd(Pair(x,y)) = y

origBRed : (tagT x y recs : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap2 origB (ap2 Pair tagT (ap2 Pair x y)) recs) y)
origBRed tagT x y recs =
  ruleTrans (axLift (Comp Snd Snd) (ap2 Pair tagT (ap2 Pair x y)) recs)
  (ruleTrans (axComp Snd Snd (ap2 Pair tagT (ap2 Pair x y)))
  (ruleTrans (cong1 Snd (axSnd tagT (ap2 Pair x y)))
             (axSnd x y)))

------------------------------------------------------------------------
-- origAL reduction: Fst(origA)
-- For orig = Pair(tagT, Pair(Pair(a1,a2), y)):
--   origAL(orig, recs) = Fst(origA(orig, recs)) = Fst(Pair(a1,a2)) = a1

origALRed : (tagT a1 a2 y recs : Term) -> {hyp : Equation} ->
  let origT = ap2 Pair tagT (ap2 Pair (ap2 Pair a1 a2) y)
  in Deriv hyp (eqn (ap2 origAL origT recs) a1)
origALRed tagT a1 a2 y recs =
  let origT = ap2 Pair tagT (ap2 Pair (ap2 Pair a1 a2) y)
  in ruleTrans (axPost Fst origA origT recs)
     (ruleTrans (cong1 Fst (origARed tagT (ap2 Pair a1 a2) y recs))
                (axFst a1 a2))

------------------------------------------------------------------------
-- origAR reduction: Snd(origA)
-- For orig = Pair(tagT, Pair(Pair(a1,a2), y)):
--   origAR(orig, recs) = Snd(origA(orig, recs)) = Snd(Pair(a1,a2)) = a2

origARRed : (tagT a1 a2 y recs : Term) -> {hyp : Equation} ->
  let origT = ap2 Pair tagT (ap2 Pair (ap2 Pair a1 a2) y)
  in Deriv hyp (eqn (ap2 origAR origT recs) a2)
origARRed tagT a1 a2 y recs =
  let origT = ap2 Pair tagT (ap2 Pair (ap2 Pair a1 a2) y)
  in ruleTrans (axPost Snd origA origT recs)
     (ruleTrans (cong1 Snd (origARed tagT (ap2 Pair a1 a2) y recs))
                (axSnd a1 a2))

------------------------------------------------------------------------
-- origB sub-extractors: Fst(origB), Snd(origB)
-- For orig = Pair(tagT, Pair(x, Pair(b1, b2))):

origB1Red : (tagT x b1 b2 recs : Term) -> {hyp : Equation} ->
  let origT = ap2 Pair tagT (ap2 Pair x (ap2 Pair b1 b2))
  in Deriv hyp (eqn (ap2 origB1 origT recs) b1)
origB1Red tagT x b1 b2 recs =
  let origT = ap2 Pair tagT (ap2 Pair x (ap2 Pair b1 b2))
  in ruleTrans (axPost Fst origB origT recs)
     (ruleTrans (cong1 Fst (origBRed tagT x (ap2 Pair b1 b2) recs))
                (axFst b1 b2))

origB2Red : (tagT x b1 b2 recs : Term) -> {hyp : Equation} ->
  let origT = ap2 Pair tagT (ap2 Pair x (ap2 Pair b1 b2))
  in Deriv hyp (eqn (ap2 origB2 origT recs) b2)
origB2Red tagT x b1 b2 recs =
  let origT = ap2 Pair tagT (ap2 Pair x (ap2 Pair b1 b2))
  in ruleTrans (axPost Snd origB origT recs)
     (ruleTrans (cong1 Snd (origBRed tagT x (ap2 Pair b1 b2) recs))
                (axSnd b1 b2))

------------------------------------------------------------------------
-- Recs extraction chain
-- For recs = Pair(thFunTFor(tagT), innerRec) where innerRec = thFunTFor(Pair(x, y)):
--
-- sndArg2(orig, recs) = recs
-- Post Snd sndArg2 (orig, recs) = Snd(recs) = innerRec
--
-- When inner passthrough applies (x is Pair-Pair-tagged):
-- innerRec = recsSp = Pair(thFunTFor(x), thFunTFor(y))
--
-- recsA(orig, recs) = Fst(innerRec)
-- recsB(orig, recs) = Snd(innerRec)

-- sndArg2 reduction: sndArg2(orig, recs) = recs
sndArg2Red : (orig recs : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap2 sndArg2 orig recs) recs)
sndArg2Red orig recs =
  ruleTrans (axPost Snd Pair orig recs) (axSnd orig recs)

-- Post Snd sndArg2 = Snd(recs)
postSndSndArg2Red : (orig recs : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap2 (Post Snd sndArg2) orig recs) (ap1 Snd recs))
postSndSndArg2Red orig recs =
  ruleTrans (axPost Snd sndArg2 orig recs)
            (cong1 Snd (sndArg2Red orig recs))

------------------------------------------------------------------------
-- Inner passthrough proof:
-- thFunTFor(Pair(x, Pair(s1,s2))) where x is Pair-Pair-tagged.
-- Uses RecNd + guardNd + ndDispatchPairMiss + sndArg2.
-- Result: thFunTFor(Pair(x, Pair(s1,s2))) = Pair(thFunTFor(x), thFunTFor(Pair(s1,s2)))

innerPassthrough :
  (a1 a2 b s1 s2 : Term) -> {hyp : Equation} ->
  let x = ap2 Pair (ap2 Pair a1 a2) b
      sp = ap2 Pair s1 s2
  in Deriv hyp (eqn (ap1 thFunTFor (ap2 Pair x sp))
                    (ap2 Pair (ap1 thFunTFor x) (ap1 thFunTFor sp)))
innerPassthrough a1 a2 b s1 s2 =
  let x = ap2 Pair (ap2 Pair a1 a2) b
      sp = ap2 Pair s1 s2
      recsSp = ap2 Pair (ap1 thFunTFor x) (ap1 thFunTFor sp)
  in ruleTrans (axRecNd O thFunStep x sp)
     (ruleTrans (guardNd x s1 s2 recsSp)
     (ruleTrans (ndDispatchPairMiss a1 a2 b sp recsSp)
     (ruleTrans (axPost Snd Pair (ap2 Pair x sp) recsSp)
                (axSnd (ap2 Pair x sp) recsSp))))

------------------------------------------------------------------------
-- Recs B extraction with passthrough
-- Given origT and recsT where inner passthrough gives recsSp:
-- recsB(origT, recsT) = Snd(Snd(recsT))
-- After passthrough: Snd(recsT) = thFunTFor(Pair(x,y)) = recsSp = Pair(thFunTFor(x), thFunTFor(y))
-- So recsB = Snd(recsSp) = thFunTFor(y)

-- Full chain from recsB to thFunTFor(sp) via passthrough
-- origT = Pair(tagT, Pair(x, sp))
-- recsT = Pair(thFunTFor(tagT), thFunTFor(Pair(x, sp)))
-- When x = Pair(Pair(a1,a2), b) (Pair-Pair-tagged) and sp = Pair(s1, s2):

recsBWithPassthrough :
  (tagT a1 a2 b s1 s2 : Term) -> {hyp : Equation} ->
  let x = ap2 Pair (ap2 Pair a1 a2) b
      sp = ap2 Pair s1 s2
      origT = ap2 Pair tagT (ap2 Pair x sp)
      innerRec = ap1 thFunTFor (ap2 Pair x sp)
      recsT = ap2 Pair (ap1 thFunTFor tagT) innerRec
  in Deriv hyp (eqn (ap2 recsB origT recsT) (ap1 thFunTFor sp))
recsBWithPassthrough tagT a1 a2 b s1 s2 =
  let x = ap2 Pair (ap2 Pair a1 a2) b
      sp = ap2 Pair s1 s2
      origT = ap2 Pair tagT (ap2 Pair x sp)
      innerRec = ap1 thFunTFor (ap2 Pair x sp)
      recsT = ap2 Pair (ap1 thFunTFor tagT) innerRec
      recsSp = ap2 Pair (ap1 thFunTFor x) (ap1 thFunTFor sp)
      pss = postSndSndArg2Red origT recsT
      sndR = axSnd (ap1 thFunTFor tagT) innerRec
      pass = innerPassthrough a1 a2 b s1 s2
      full = ruleTrans pss (ruleTrans sndR pass)
  in ruleTrans (axPost Snd (Post Snd sndArg2) origT recsT)
     (ruleTrans (cong1 Snd full)
                (axSnd (ap1 thFunTFor x) (ap1 thFunTFor sp)))

-- recsA with passthrough: Fst(Snd(recsT)) = thFunTFor(x)
recsAWithPassthrough :
  (tagT a1 a2 b s1 s2 : Term) -> {hyp : Equation} ->
  let x = ap2 Pair (ap2 Pair a1 a2) b
      sp = ap2 Pair s1 s2
      origT = ap2 Pair tagT (ap2 Pair x sp)
      innerRec = ap1 thFunTFor (ap2 Pair x sp)
      recsT = ap2 Pair (ap1 thFunTFor tagT) innerRec
  in Deriv hyp (eqn (ap2 recsA origT recsT) (ap1 thFunTFor x))
recsAWithPassthrough tagT a1 a2 b s1 s2 =
  let x = ap2 Pair (ap2 Pair a1 a2) b
      sp = ap2 Pair s1 s2
      origT = ap2 Pair tagT (ap2 Pair x sp)
      innerRec = ap1 thFunTFor (ap2 Pair x sp)
      recsT = ap2 Pair (ap1 thFunTFor tagT) innerRec
      recsSp = ap2 Pair (ap1 thFunTFor x) (ap1 thFunTFor sp)
      pss = postSndSndArg2Red origT recsT
      sndR = axSnd (ap1 thFunTFor tagT) innerRec
      pass = innerPassthrough a1 a2 b s1 s2
      full = ruleTrans pss (ruleTrans sndR pass)
  in ruleTrans (axPost Fst (Post Snd sndArg2) origT recsT)
     (ruleTrans (cong1 Fst full)
                (axFst (ap1 thFunTFor x) (ap1 thFunTFor sp)))

------------------------------------------------------------------------
-- recsBL / recsBR with passthrough: Fst/Snd of thFunTFor(sp)

recsBLWithPassthrough :
  (tagT a1 a2 b s1 s2 : Term) -> {hyp : Equation} ->
  let x = ap2 Pair (ap2 Pair a1 a2) b
      sp = ap2 Pair s1 s2
      origT = ap2 Pair tagT (ap2 Pair x sp)
      innerRec = ap1 thFunTFor (ap2 Pair x sp)
      recsT = ap2 Pair (ap1 thFunTFor tagT) innerRec
  in Deriv hyp (eqn (ap2 recsBL origT recsT) (ap1 Fst (ap1 thFunTFor sp)))
recsBLWithPassthrough tagT a1 a2 b s1 s2 =
  let x = ap2 Pair (ap2 Pair a1 a2) b
      sp = ap2 Pair s1 s2
      origT = ap2 Pair tagT (ap2 Pair x sp)
      innerRec = ap1 thFunTFor (ap2 Pair x sp)
      recsT = ap2 Pair (ap1 thFunTFor tagT) innerRec
  in ruleTrans (axPost Fst recsB origT recsT)
               (cong1 Fst (recsBWithPassthrough tagT a1 a2 b s1 s2))

recsBRWithPassthrough :
  (tagT a1 a2 b s1 s2 : Term) -> {hyp : Equation} ->
  let x = ap2 Pair (ap2 Pair a1 a2) b
      sp = ap2 Pair s1 s2
      origT = ap2 Pair tagT (ap2 Pair x sp)
      innerRec = ap1 thFunTFor (ap2 Pair x sp)
      recsT = ap2 Pair (ap1 thFunTFor tagT) innerRec
  in Deriv hyp (eqn (ap2 recsBR origT recsT) (ap1 Snd (ap1 thFunTFor sp)))
recsBRWithPassthrough tagT a1 a2 b s1 s2 =
  let x = ap2 Pair (ap2 Pair a1 a2) b
      sp = ap2 Pair s1 s2
      origT = ap2 Pair tagT (ap2 Pair x sp)
      innerRec = ap1 thFunTFor (ap2 Pair x sp)
      recsT = ap2 Pair (ap1 thFunTFor tagT) innerRec
  in ruleTrans (axPost Snd recsB origT recsT)
               (cong1 Snd (recsBWithPassthrough tagT a1 a2 b s1 s2))

------------------------------------------------------------------------
-- recsAL / recsAR with passthrough: Fst/Snd of thFunTFor(x)

recsALWithPassthrough :
  (tagT a1 a2 b s1 s2 : Term) -> {hyp : Equation} ->
  let x = ap2 Pair (ap2 Pair a1 a2) b
      sp = ap2 Pair s1 s2
      origT = ap2 Pair tagT (ap2 Pair x sp)
      innerRec = ap1 thFunTFor (ap2 Pair x sp)
      recsT = ap2 Pair (ap1 thFunTFor tagT) innerRec
  in Deriv hyp (eqn (ap2 recsAL origT recsT) (ap1 Fst (ap1 thFunTFor x)))
recsALWithPassthrough tagT a1 a2 b s1 s2 =
  let x = ap2 Pair (ap2 Pair a1 a2) b
      sp = ap2 Pair s1 s2
      origT = ap2 Pair tagT (ap2 Pair x sp)
      innerRec = ap1 thFunTFor (ap2 Pair x sp)
      recsT = ap2 Pair (ap1 thFunTFor tagT) innerRec
  in ruleTrans (axPost Fst recsA origT recsT)
               (cong1 Fst (recsAWithPassthrough tagT a1 a2 b s1 s2))

recsARWithPassthrough :
  (tagT a1 a2 b s1 s2 : Term) -> {hyp : Equation} ->
  let x = ap2 Pair (ap2 Pair a1 a2) b
      sp = ap2 Pair s1 s2
      origT = ap2 Pair tagT (ap2 Pair x sp)
      innerRec = ap1 thFunTFor (ap2 Pair x sp)
      recsT = ap2 Pair (ap1 thFunTFor tagT) innerRec
  in Deriv hyp (eqn (ap2 recsAR origT recsT) (ap1 Snd (ap1 thFunTFor x)))
recsARWithPassthrough tagT a1 a2 b s1 s2 =
  let x = ap2 Pair (ap2 Pair a1 a2) b
      sp = ap2 Pair s1 s2
      origT = ap2 Pair tagT (ap2 Pair x sp)
      innerRec = ap1 thFunTFor (ap2 Pair x sp)
      recsT = ap2 Pair (ap1 thFunTFor tagT) innerRec
  in ruleTrans (axPost Snd recsA origT recsT)
               (cong1 Snd (recsAWithPassthrough tagT a1 a2 b s1 s2))

------------------------------------------------------------------------
-- mkAp1F reduction: Fan (kF2 tagAp1T) (Fan fCodeF tCodeF Pair) Pair
-- Given reductions of fCodeF and tCodeF:

mkAp1FRed : (fCodeF tCodeF : Fun2) (orig recs fResult tResult : Term) ->
  {hyp : Equation} ->
  Deriv hyp (eqn (ap2 fCodeF orig recs) fResult) ->
  Deriv hyp (eqn (ap2 tCodeF orig recs) tResult) ->
  Deriv hyp (eqn (ap2 (mkAp1F fCodeF tCodeF) orig recs)
                 (ap2 Pair (reify tagAp1) (ap2 Pair fResult tResult)))
mkAp1FRed fCodeF tCodeF orig recs fR tR fPf tPf =
  ruleTrans (axFan (kF2 (reify tagAp1)) (Fan fCodeF tCodeF Pair) Pair orig recs)
  (ruleTrans (congL Pair (ap2 (Fan fCodeF tCodeF Pair) orig recs)
               (constF2Red (reify tagAp1) orig recs))
  (congR Pair (reify tagAp1)
    (ruleTrans (axFan fCodeF tCodeF Pair orig recs)
    (ruleTrans (congL Pair (ap2 tCodeF orig recs) fPf)
               (congR Pair fR tPf)))))

------------------------------------------------------------------------
-- mkAp2F reduction: Fan (kF2 tagAp2T) (Fan gCodeF (Fan aCodeF bCodeF Pair) Pair) Pair

mkAp2FRed : (gCodeF aCodeF bCodeF : Fun2) (orig recs gR aR bR : Term) ->
  {hyp : Equation} ->
  Deriv hyp (eqn (ap2 gCodeF orig recs) gR) ->
  Deriv hyp (eqn (ap2 aCodeF orig recs) aR) ->
  Deriv hyp (eqn (ap2 bCodeF orig recs) bR) ->
  Deriv hyp (eqn (ap2 (mkAp2F gCodeF aCodeF bCodeF) orig recs)
                 (ap2 Pair (reify tagAp2) (ap2 Pair gR (ap2 Pair aR bR))))
mkAp2FRed gCodeF aCodeF bCodeF orig recs gR aR bR gPf aPf bPf =
  let innerPair = ruleTrans (axFan aCodeF bCodeF Pair orig recs)
                  (ruleTrans (congL Pair (ap2 bCodeF orig recs) aPf)
                             (congR Pair aR bPf))
      midPair = ruleTrans (axFan gCodeF (Fan aCodeF bCodeF Pair) Pair orig recs)
                (ruleTrans (congL Pair (ap2 (Fan aCodeF bCodeF Pair) orig recs) gPf)
                           (congR Pair gR innerPair))
  in ruleTrans (axFan (kF2 (reify tagAp2)) (Fan gCodeF (Fan aCodeF bCodeF Pair) Pair) Pair orig recs)
     (ruleTrans (congL Pair (ap2 (Fan gCodeF (Fan aCodeF bCodeF Pair) Pair) orig recs)
                  (constF2Red (reify tagAp2) orig recs))
                (congR Pair (reify tagAp2) midPair))

------------------------------------------------------------------------
-- mkEqF reduction: Fan leftF rightF Pair
-- Given reductions of leftF and rightF, produce the Pair result.

mkEqFRed : (leftF rightF : Fun2) (orig recs leftResult rightResult : Term) ->
  {hyp : Equation} ->
  Deriv hyp (eqn (ap2 leftF orig recs) leftResult) ->
  Deriv hyp (eqn (ap2 rightF orig recs) rightResult) ->
  Deriv hyp (eqn (ap2 (mkEqF leftF rightF) orig recs) (ap2 Pair leftResult rightResult))
mkEqFRed leftF rightF orig recs lR rR lPf rPf =
  ruleTrans (axFan leftF rightF Pair orig recs)
  (ruleTrans (congL Pair (ap2 rightF orig recs) lPf)
             (congR Pair lR rPf))
