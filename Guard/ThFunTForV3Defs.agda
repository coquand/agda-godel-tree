{-# OPTIONS --safe --without-K --exact-split #-}

-- Guard.ThFunTForV3Defs — V3-specific dispatch helpers.
--
-- Phase B2 of the Gödel-II redesign: the object-level reduction
-- machinery that proves how  thmTStep  and  ndDispatchV3  reduce.
--
-- What is here:
--   * guardNdV3, guardLfV3 — how thmTStep (the V3 step) dispatches
--     to ndDispatchV3 (nd body case) or lfDispatchV3 (lf body case).
--   * recUnfoldIHV3 — Rec unfolding adapted for thmT = Rec O (thmTStep hCode).
--   * case26Match — reduction of case26 at the match (body = hCode) case.
--
-- Generic helpers  tagCheckRed, branchHit, branchMiss, ndBranchHit,
-- ndBranchMiss, natCodeSelfEq, natCodeNeq  are reused verbatim from
-- Guard.ThFunTForCorrectDefs (they don't reference old  thFunStep ).

module Guard.ThFunTForV3Defs where

open import Guard.Base
open import Guard.Term
open import Guard.Step
open import Guard.StepReduce
open import Guard.ThFunTForDefs
open import Guard.ExtractorRed
open import Guard.ThFunTForV3
open import Guard.GodelII using (treeEqSelf)

------------------------------------------------------------------------
-- Shorthand.

private
  poo : Term
  poo = ap2 Pair O O

-- sndArg2 applied at any orig, recs: returns recs.
-- (Generic; independent of V2/V3.)
sndArg2RedV3 : (orig recs : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap2 sndArg2 orig recs) recs)
sndArg2RedV3 orig recs =
  ruleTrans (postRed Snd Pair orig recs) (axSnd orig recs)

------------------------------------------------------------------------
-- Rec unfolding for thmT hCode = Rec O (thmTStep hCode).
--
-- Given:  Deriv hyp (ap1 (thmT hCode) (reify a) = reify (thFun_hCode a))
--         Deriv hyp (ap1 (thmT hCode) (reify b) = reify (thFun_hCode b))
-- conclude Deriv hyp about thmT applied at the nd-node, expressed via
-- thmTStep.  Unlike the V2 version, we state it schematically in
-- ra, rb (the recursive results) because thmT's metalevel function
-- body is defined inline in ThFunV3, and we don't want to couple
-- against a single global metalevel  thFun .

recUnfoldIHV3 :
  (hCode ra rb : Term) -> {hyp : Equation} (a b : Term) ->
  Deriv hyp (eqn (ap1 (thmT hCode) a) ra) ->
  Deriv hyp (eqn (ap1 (thmT hCode) b) rb) ->
  Deriv hyp (eqn (ap1 (thmT hCode) (ap2 Pair a b))
                 (ap2 (thmTStep hCode) (ap2 Pair a b)
                                       (ap2 Pair ra rb)))
recUnfoldIHV3 hCode ra rb a b iha ihb =
  ruleTrans (recNdRed O (thmTStep hCode) a b)
  (congR (thmTStep hCode) (ap2 Pair a b)
    (ruleTrans (congL Pair (ap1 (thmT hCode) b) iha)
               (congR Pair ra ihb)))

------------------------------------------------------------------------
-- When data = Pair x y (nd case): thmTStep hCode selects ndDispatchV3 hCode.

guardNdV3 : (hCode tag x y recs : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap2 (thmTStep hCode) (ap2 Pair tag (ap2 Pair x y)) recs)
                 (ap2 (ndDispatchV3 hCode) (ap2 Pair tag (ap2 Pair x y)) recs))
guardNdV3 hCode tag x y recs =
  let orig = ap2 Pair tag (ap2 Pair x y)
      checkIsLf = ap2 dataIsLfV3 orig recs
  in ruleTrans (fanRed dataIsLfV3 (Fan lfDispatchV3 (ndDispatchV3 hCode) Pair) IfLf orig recs)
     (ruleTrans (congL IfLf (ap2 (Fan lfDispatchV3 (ndDispatchV3 hCode) Pair) orig recs)
                  -- compute check: Snd(orig) = Pair x y, compared to O, gives poo
                  (ruleTrans (fanRed (Lift Snd) (kF2 O) TreeEq orig recs)
                  (ruleTrans (congL TreeEq (ap2 (kF2 O) orig recs)
                               (ruleTrans (liftRed Snd orig recs)
                                          (axSnd tag (ap2 Pair x y))))
                  (ruleTrans (congR TreeEq (ap2 Pair x y)
                               (constF2Red O orig recs))
                             (axTreeEqNL x y)))))
     (ruleTrans (congR IfLf poo
                  (fanRed lfDispatchV3 (ndDispatchV3 hCode) Pair orig recs))
                (axIfLfN O O (ap2 lfDispatchV3 orig recs)
                             (ap2 (ndDispatchV3 hCode) orig recs))))

------------------------------------------------------------------------
-- When data = O (lf case): thmTStep hCode selects lfDispatchV3.

guardLfV3 : (hCode tag recs : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap2 (thmTStep hCode) (ap2 Pair tag O) recs)
                 (ap2 lfDispatchV3 (ap2 Pair tag O) recs))
guardLfV3 hCode tag recs =
  let orig = ap2 Pair tag O
  in ruleTrans (fanRed dataIsLfV3 (Fan lfDispatchV3 (ndDispatchV3 hCode) Pair) IfLf orig recs)
     (ruleTrans (congL IfLf (ap2 (Fan lfDispatchV3 (ndDispatchV3 hCode) Pair) orig recs)
                  -- compute check: Snd(orig) = O, compared to O, gives O
                  (ruleTrans (fanRed (Lift Snd) (kF2 O) TreeEq orig recs)
                  (ruleTrans (congL TreeEq (ap2 (kF2 O) orig recs)
                               (ruleTrans (liftRed Snd orig recs)
                                          (axSnd tag O)))
                  (ruleTrans (congR TreeEq O (constF2Red O orig recs))
                             axTreeEqLL))))
     (ruleTrans (congR IfLf O
                  (fanRed lfDispatchV3 (ndDispatchV3 hCode) Pair orig recs))
                (axIfLfL (ap2 lfDispatchV3 orig recs)
                         (ap2 (ndDispatchV3 hCode) orig recs))))

------------------------------------------------------------------------
-- case26 reduction at the match point.
--
-- Input shape: orig = Pair tag hCode  (the body literally IS hCode).
-- Expected output: hCode.

case26Match : (hCode tag recs : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap2 (case26 hCode) (ap2 Pair tag hCode) recs) hCode)
case26Match hCode tag recs =
  let orig = ap2 Pair tag hCode
      -- branch's check-Fan part
      checkF = Fan (Lift Snd) (kF2 hCode) TreeEq
      thenElseF = Fan (kF2 hCode) (kF2 O) Pair
  in ruleTrans (fanRed checkF thenElseF IfLf orig recs)
     (ruleTrans (congL IfLf (ap2 thenElseF orig recs)
                  -- check: TreeEq(Snd orig, hCode) = TreeEq(hCode, hCode) = O
                  (ruleTrans (fanRed (Lift Snd) (kF2 hCode) TreeEq orig recs)
                  (ruleTrans (congL TreeEq (ap2 (kF2 hCode) orig recs)
                               (ruleTrans (liftRed Snd orig recs)
                                          (axSnd tag hCode)))
                  (ruleTrans (congR TreeEq hCode (constF2Red hCode orig recs))
                             (treeEqSelfAtHCode hCode)))))
     (ruleTrans (congR IfLf O (fanRed (kF2 hCode) (kF2 O) Pair orig recs))
                (ruleTrans (axIfLfL (ap2 (kF2 hCode) orig recs)
                                    (ap2 (kF2 O) orig recs))
                           (constF2Red hCode orig recs))))
  where
  treeEqSelfAtHCode : (c : Term) -> {hyp : Equation} ->
                      Deriv hyp (eqn (ap2 TreeEq c c) O)
  treeEqSelfAtHCode c = treeEqSelf c

------------------------------------------------------------------------
-- Intermediate passthrough (V3): when the data of a node has shape
-- Pair(sp2a, sp2b) and the tag itself is a valid sub-encoding tagT
-- (so ndDispatchV3 misses at it), thmT hCode pushes through to
-- Pair(thmT hCode tagT, thmT hCode (Pair sp2a sp2b)).
--
-- Direct port of Guard.IntermediatePassthrough.intermediateGeneric.

intermediateGenericV3 :
  (hCode tagT datT : Term)
  (sp2a sp2b : Term)
  -> ((x recs : Term) -> {hyp : Equation} ->
      Deriv hyp (eqn (ap2 (ndDispatchV3 hCode) (ap2 Pair tagT x) recs)
                     (ap2 sndArg2 (ap2 Pair tagT x) recs)))
  -> {hyp : Equation}
  -> Deriv hyp (eqn (ap1 (thmT hCode) (ap2 Pair tagT (ap2 Pair sp2a sp2b)))
                    (ap2 Pair (ap1 (thmT hCode) tagT)
                              (ap1 (thmT hCode) (ap2 Pair sp2a sp2b))))
intermediateGenericV3 hCode tagT datT sp2a sp2b dispMiss =
  let dat  = ap2 Pair sp2a sp2b
      orig = ap2 Pair tagT dat
      recs = ap2 Pair (ap1 (thmT hCode) tagT) (ap1 (thmT hCode) dat)
  in ruleTrans (recNdRed O (thmTStep hCode) tagT dat)
     (ruleTrans (guardNdV3 hCode tagT sp2a sp2b recs)
     (ruleTrans (dispMiss dat recs)
                (sndArg2RedV3 orig recs)))

------------------------------------------------------------------------
-- case19V3Match: at a genuine trans node where the middle terms agree,
-- case19V3 reduces to  Pair (leftT sp1-result) (rightT sp2-result) .
--
-- Preconditions:
--   * orig has shape Pair tagR dat (standard Rec node shape).
--   * recs has shape Pair recTag (Pair recA recB), where recA and recB
--     are the thmT-values of the two sub-proofs (assumed already
--     reduced to Pair tC uC1 and Pair uC2 vC respectively).
--   * The middle terms agree: uC1 = uC2 = uC.
--
-- Then case19V3 at (orig, recs) reduces to Pair tC vC.

case19V3Match :
  (tag dat recTag tC uC vC : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap2 case19V3
                   (ap2 Pair tag dat)
                   (ap2 Pair recTag (ap2 Pair (ap2 Pair tC uC) (ap2 Pair uC vC))))
                 (ap2 Pair tC vC))
case19V3Match tag dat recTag tC uC vC =
  let orig = ap2 Pair tag dat
      recs = ap2 Pair recTag (ap2 Pair (ap2 Pair tC uC) (ap2 Pair uC vC))
      checkF  = Fan recsAR recsBL TreeEq
      matchF  = Fan recsAL recsBR Pair
      branchF = Fan matchF (kF2 O) Pair
  in ruleTrans (fanRed checkF branchF IfLf orig recs)
     -- check-result reduces to TreeEq(uC, uC) = O
     (ruleTrans
       (congL IfLf (ap2 branchF orig recs)
         (ruleTrans (fanRed recsAR recsBL TreeEq orig recs)
         (ruleTrans
           (congL TreeEq (ap2 recsBL orig recs)
             (recsARRed orig recTag tC uC (ap2 Pair uC vC)))
         (ruleTrans
           (congR TreeEq uC
             (recsBLRed orig recTag (ap2 Pair tC uC) uC vC))
           (treeEqSelf uC)))))
     -- branchF reduces to Pair (matchF result) (kF2 O result) = Pair (Pair tC vC) O
     (ruleTrans
       (congR IfLf O
         (ruleTrans (fanRed matchF (kF2 O) Pair orig recs)
         (ruleTrans
           (congL Pair (ap2 (kF2 O) orig recs)
             (ruleTrans (fanRed recsAL recsBR Pair orig recs)
             (ruleTrans
               (congL Pair (ap2 recsBR orig recs)
                 (recsALRed orig recTag tC uC (ap2 Pair uC vC)))
               (congR Pair tC
                 (recsBRRed orig recTag (ap2 Pair tC uC) uC vC)))))
           (congR Pair (ap2 Pair tC vC)
             (constF2Red O orig recs)))))
       (axIfLfL (ap2 Pair tC vC) O)))
