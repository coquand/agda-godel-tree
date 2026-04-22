{-# OPTIONS --safe --without-K --exact-split #-}

-- Guard.ExtractorRedUnify -- port of Guard.ExtractorRed to DerivF.
--
-- Reductions for extractor Fun2s (origA, origB, origAL, origAR,
-- origB1, origB2, origB2a, origB2b, origB2b1, origB2b2, recsA, recsB,
-- recsAL, recsAR, recsBL, recsBR, kF2, mkEqF, mkAp1F, mkAp2F,
-- sndArg2).  All conclusions atomic.
--
-- Part of the unify-2 migration.

module Guard.ExtractorRedUnify where

open import Guard.Base
open import Guard.Term
open import Guard.Formula
open import Guard.DerivF
open import Guard.StepReduceUnify
open import Guard.ThFunTForDefs

------------------------------------------------------------------------
-- Extractor reductions at specific arguments
-- orig = Pair(tag, Pair(a, b)), recs = Pair(recTag, recData)

-- origA = Lift (Comp Fst Snd) : extracts Fst(Snd(orig))
origARed : (tag a b recs : Term) ->
  Deriv (atomic (eqn (ap2 origA (ap2 Pair tag (ap2 Pair a b)) recs) a))
origARed tag a b recs =
  ruleTrans (liftRed (Comp Fst Snd) (ap2 Pair tag (ap2 Pair a b)) recs)
  (ruleTrans (compRed Fst Snd (ap2 Pair tag (ap2 Pair a b)))
  (ruleTrans (cong1 Fst (axSnd tag (ap2 Pair a b)))
             (axFst a b)))

-- origB = Lift (Comp Snd Snd) : extracts Snd(Snd(orig))
origBRed : (tag a b recs : Term) ->
  Deriv (atomic (eqn (ap2 origB (ap2 Pair tag (ap2 Pair a b)) recs) b))
origBRed tag a b recs =
  ruleTrans (liftRed (Comp Snd Snd) (ap2 Pair tag (ap2 Pair a b)) recs)
  (ruleTrans (compRed Snd Snd (ap2 Pair tag (ap2 Pair a b)))
  (ruleTrans (cong1 Snd (axSnd tag (ap2 Pair a b)))
             (axSnd a b)))

-- origAL = Post Fst origA : extracts Fst(origA) = Fst(Fst(Snd(orig)))
origALRed : (tag a1 a2 b recs : Term) ->
  Deriv (atomic (eqn (ap2 origAL (ap2 Pair tag (ap2 Pair (ap2 Pair a1 a2) b)) recs) a1))
origALRed tag a1 a2 b recs =
  ruleTrans (postRed Fst origA (ap2 Pair tag (ap2 Pair (ap2 Pair a1 a2) b)) recs)
  (ruleTrans (cong1 Fst (origARed tag (ap2 Pair a1 a2) b recs))
             (axFst a1 a2))

-- origAR = Post Snd origA : extracts Snd(origA)
origARRed : (tag a1 a2 b recs : Term) ->
  Deriv (atomic (eqn (ap2 origAR (ap2 Pair tag (ap2 Pair (ap2 Pair a1 a2) b)) recs) a2))
origARRed tag a1 a2 b recs =
  ruleTrans (postRed Snd origA (ap2 Pair tag (ap2 Pair (ap2 Pair a1 a2) b)) recs)
  (ruleTrans (cong1 Snd (origARed tag (ap2 Pair a1 a2) b recs))
             (axSnd a1 a2))

-- kF2 t reduces to t
kF2Red : (t orig recs : Term) ->
  Deriv (atomic (eqn (ap2 (kF2 t) orig recs) t))
kF2Red t orig recs = constF2Red t orig recs

------------------------------------------------------------------------
-- mkEqF, mkAp1F, mkAp2F evaluation

mkEqFRed : (lF rF : Fun2) (orig recs lVal rVal : Term) ->
  Deriv (atomic (eqn (ap2 lF orig recs) lVal)) ->
  Deriv (atomic (eqn (ap2 rF orig recs) rVal)) ->
  Deriv (atomic (eqn (ap2 (mkEqF lF rF) orig recs) (ap2 Pair lVal rVal)))
mkEqFRed lF rF orig recs lVal rVal lPf rPf =
  ruleTrans (fanRed lF rF Pair orig recs)
  (ruleTrans (congL Pair (ap2 rF orig recs) lPf)
             (congR Pair lVal rPf))

mkAp1FRed : (fF tF : Fun2) (orig recs fVal tVal : Term) ->
  Deriv (atomic (eqn (ap2 fF orig recs) fVal)) ->
  Deriv (atomic (eqn (ap2 tF orig recs) tVal)) ->
  Deriv (atomic (eqn (ap2 (mkAp1F fF tF) orig recs)
                      (ap2 Pair (reify tagAp1) (ap2 Pair fVal tVal))))
mkAp1FRed fF tF orig recs fVal tVal fPf tPf =
  ruleTrans (fanRed (kF2 (reify tagAp1)) (Fan fF tF Pair) Pair orig recs)
  (ruleTrans (congL Pair (ap2 (Fan fF tF Pair) orig recs) (kF2Red (reify tagAp1) orig recs))
  (congR Pair (reify tagAp1)
    (ruleTrans (fanRed fF tF Pair orig recs)
    (ruleTrans (congL Pair (ap2 tF orig recs) fPf)
               (congR Pair fVal tPf)))))

------------------------------------------------------------------------
-- Deep payload extractors

origB1Red : (tag a b1 b2 recs : Term) ->
  Deriv (atomic (eqn (ap2 origB1 (ap2 Pair tag (ap2 Pair a (ap2 Pair b1 b2))) recs) b1))
origB1Red tag a b1 b2 recs =
  ruleTrans (postRed Fst origB (ap2 Pair tag (ap2 Pair a (ap2 Pair b1 b2))) recs)
  (ruleTrans (cong1 Fst (origBRed tag a (ap2 Pair b1 b2) recs))
             (axFst b1 b2))

origB2Red : (tag a b1 b2 recs : Term) ->
  Deriv (atomic (eqn (ap2 origB2 (ap2 Pair tag (ap2 Pair a (ap2 Pair b1 b2))) recs) b2))
origB2Red tag a b1 b2 recs =
  ruleTrans (postRed Snd origB (ap2 Pair tag (ap2 Pair a (ap2 Pair b1 b2))) recs)
  (ruleTrans (cong1 Snd (origBRed tag a (ap2 Pair b1 b2) recs))
             (axSnd b1 b2))

origB2aRed : (tag a b1 b2a b2b recs : Term) ->
  Deriv (atomic (eqn (ap2 origB2a (ap2 Pair tag (ap2 Pair a (ap2 Pair b1 (ap2 Pair b2a b2b)))) recs) b2a))
origB2aRed tag a b1 b2a b2b recs =
  let orig = ap2 Pair tag (ap2 Pair a (ap2 Pair b1 (ap2 Pair b2a b2b))) in
  ruleTrans (postRed Fst origB2 orig recs)
  (ruleTrans (cong1 Fst (origB2Red tag a b1 (ap2 Pair b2a b2b) recs))
             (axFst b2a b2b))

origB2bRed : (tag a b1 b2a b2b recs : Term) ->
  Deriv (atomic (eqn (ap2 origB2b (ap2 Pair tag (ap2 Pair a (ap2 Pair b1 (ap2 Pair b2a b2b)))) recs) b2b))
origB2bRed tag a b1 b2a b2b recs =
  let orig = ap2 Pair tag (ap2 Pair a (ap2 Pair b1 (ap2 Pair b2a b2b))) in
  ruleTrans (postRed Snd origB2 orig recs)
  (ruleTrans (cong1 Snd (origB2Red tag a b1 (ap2 Pair b2a b2b) recs))
             (axSnd b2a b2b))

private
  origB2b1 : Fun2
  origB2b1 = Post Fst origB2b

  origB2b2 : Fun2
  origB2b2 = Post Snd origB2b

origB2b1Red : (tag a b1 b2a b2b1 b2b2 recs : Term) ->
  Deriv (atomic (eqn (ap2 origB2b1
    (ap2 Pair tag (ap2 Pair a (ap2 Pair b1 (ap2 Pair b2a (ap2 Pair b2b1 b2b2))))) recs) b2b1))
origB2b1Red tag a b1 b2a b2b1 b2b2 recs =
  let orig = ap2 Pair tag (ap2 Pair a (ap2 Pair b1 (ap2 Pair b2a (ap2 Pair b2b1 b2b2)))) in
  ruleTrans (postRed Fst origB2b orig recs)
  (ruleTrans (cong1 Fst (origB2bRed tag a b1 b2a (ap2 Pair b2b1 b2b2) recs))
             (axFst b2b1 b2b2))

origB2b2Red : (tag a b1 b2a b2b1 b2b2 recs : Term) ->
  Deriv (atomic (eqn (ap2 origB2b2
    (ap2 Pair tag (ap2 Pair a (ap2 Pair b1 (ap2 Pair b2a (ap2 Pair b2b1 b2b2))))) recs) b2b2))
origB2b2Red tag a b1 b2a b2b1 b2b2 recs =
  let orig = ap2 Pair tag (ap2 Pair a (ap2 Pair b1 (ap2 Pair b2a (ap2 Pair b2b1 b2b2)))) in
  ruleTrans (postRed Snd origB2b orig recs)
  (ruleTrans (cong1 Snd (origB2bRed tag a b1 b2a (ap2 Pair b2b1 b2b2) recs))
             (axSnd b2b1 b2b2))

------------------------------------------------------------------------
-- Recursive-result extractors

sndArg2RedE : (orig recs : Term) ->
  Deriv (atomic (eqn (ap2 sndArg2 orig recs) recs))
sndArg2RedE orig recs = ruleTrans (postRed Snd Pair orig recs) (axSnd orig recs)

recsARed : (orig recTag recA recB : Term) ->
  Deriv (atomic (eqn (ap2 recsA orig (ap2 Pair recTag (ap2 Pair recA recB))) recA))
recsARed orig recTag recA recB =
  ruleTrans (postRed Fst (Post Snd sndArg2) orig (ap2 Pair recTag (ap2 Pair recA recB)))
  (ruleTrans (cong1 Fst
    (ruleTrans (postRed Snd sndArg2 orig (ap2 Pair recTag (ap2 Pair recA recB)))
    (ruleTrans (cong1 Snd (sndArg2RedE orig (ap2 Pair recTag (ap2 Pair recA recB))))
               (axSnd recTag (ap2 Pair recA recB)))))
  (axFst recA recB))

recsBRed : (orig recTag recA recB : Term) ->
  Deriv (atomic (eqn (ap2 recsB orig (ap2 Pair recTag (ap2 Pair recA recB))) recB))
recsBRed orig recTag recA recB =
  ruleTrans (postRed Snd (Post Snd sndArg2) orig (ap2 Pair recTag (ap2 Pair recA recB)))
  (ruleTrans (cong1 Snd
    (ruleTrans (postRed Snd sndArg2 orig (ap2 Pair recTag (ap2 Pair recA recB)))
    (ruleTrans (cong1 Snd (sndArg2RedE orig (ap2 Pair recTag (ap2 Pair recA recB))))
               (axSnd recTag (ap2 Pair recA recB)))))
  (axSnd recA recB))

recsALRed : (orig recTag rAL rAR recB : Term) ->
  Deriv (atomic (eqn (ap2 recsAL orig (ap2 Pair recTag (ap2 Pair (ap2 Pair rAL rAR) recB))) rAL))
recsALRed orig recTag rAL rAR recB =
  ruleTrans (postRed Fst recsA orig (ap2 Pair recTag (ap2 Pair (ap2 Pair rAL rAR) recB)))
  (ruleTrans (cong1 Fst (recsARed orig recTag (ap2 Pair rAL rAR) recB))
             (axFst rAL rAR))

recsARRed : (orig recTag rAL rAR recB : Term) ->
  Deriv (atomic (eqn (ap2 recsAR orig (ap2 Pair recTag (ap2 Pair (ap2 Pair rAL rAR) recB))) rAR))
recsARRed orig recTag rAL rAR recB =
  ruleTrans (postRed Snd recsA orig (ap2 Pair recTag (ap2 Pair (ap2 Pair rAL rAR) recB)))
  (ruleTrans (cong1 Snd (recsARed orig recTag (ap2 Pair rAL rAR) recB))
             (axSnd rAL rAR))

recsBLRed : (orig recTag recA rBL rBR : Term) ->
  Deriv (atomic (eqn (ap2 recsBL orig (ap2 Pair recTag (ap2 Pair recA (ap2 Pair rBL rBR)))) rBL))
recsBLRed orig recTag recA rBL rBR =
  ruleTrans (postRed Fst recsB orig (ap2 Pair recTag (ap2 Pair recA (ap2 Pair rBL rBR))))
  (ruleTrans (cong1 Fst (recsBRed orig recTag recA (ap2 Pair rBL rBR)))
             (axFst rBL rBR))

recsBRRed : (orig recTag recA rBL rBR : Term) ->
  Deriv (atomic (eqn (ap2 recsBR orig (ap2 Pair recTag (ap2 Pair recA (ap2 Pair rBL rBR)))) rBR))
recsBRRed orig recTag recA rBL rBR =
  ruleTrans (postRed Snd recsB orig (ap2 Pair recTag (ap2 Pair recA (ap2 Pair rBL rBR))))
  (ruleTrans (cong1 Snd (recsBRed orig recTag recA (ap2 Pair rBL rBR)))
             (axSnd rBL rBR))

------------------------------------------------------------------------
-- mkAp2F reduction

mkAp2FRed : (gF aF bF : Fun2) (orig recs gVal aVal bVal : Term) ->
  Deriv (atomic (eqn (ap2 gF orig recs) gVal)) ->
  Deriv (atomic (eqn (ap2 aF orig recs) aVal)) ->
  Deriv (atomic (eqn (ap2 bF orig recs) bVal)) ->
  Deriv (atomic (eqn (ap2 (mkAp2F gF aF bF) orig recs)
                      (ap2 Pair (reify tagAp2) (ap2 Pair gVal (ap2 Pair aVal bVal)))))
mkAp2FRed gF aF bF orig recs gVal aVal bVal gPf aPf bPf =
  ruleTrans (fanRed (kF2 (reify tagAp2)) (Fan gF (Fan aF bF Pair) Pair) Pair orig recs)
  (ruleTrans (congL Pair (ap2 (Fan gF (Fan aF bF Pair) Pair) orig recs)
               (kF2Red (reify tagAp2) orig recs))
  (congR Pair (reify tagAp2)
    (ruleTrans (fanRed gF (Fan aF bF Pair) Pair orig recs)
    (ruleTrans (congL Pair (ap2 (Fan aF bF Pair) orig recs) gPf)
    (congR Pair gVal
      (ruleTrans (fanRed aF bF Pair orig recs)
      (ruleTrans (congL Pair (ap2 bF orig recs) aPf)
                 (congR Pair aVal bPf))))))))
