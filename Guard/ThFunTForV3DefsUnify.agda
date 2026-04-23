{-# OPTIONS --safe --without-K --exact-split #-}

-- Guard.ThFunTForV3DefsUnify — reduction machinery for the hyp-free
-- thmT (Guard.ThFunTForHF).
--
-- Per UNIFIED-DESIGN-REV2.md: thmT is hyp-free (no hCode parameter).
-- case26 / case26Match are gone.
--
-- What is here:
--   * guardNdV3, guardLfV3 — how thmTStep dispatches to
--     ndDispatchV3 (nd body case) or lfDispatchV3 (lf body case).
--   * recUnfoldIHV3 — Rec unfolding adapted for thmT = Rec O thmTStep.
--   * case19V3Match and case23V3Match.
--   * intermediateGenericV3.
--
-- Generic helpers tagCheckRed, branchHit, branchMiss, ndBranchHit,
-- ndBranchMiss, natCodeSelfEq, natCodeNeq are reused verbatim from
-- Guard.ThFunTForCorrectDefsUnify.

module Guard.ThFunTForV3DefsUnify where

open import Guard.Base
open import Guard.Term
open import Guard.Formula
open import Guard.DerivF
open import Guard.StepReduceUnify
open import Guard.ThFunTForDefs
open import Guard.ExtractorRedUnify
open import Guard.ThFunTForHF
open import Guard.TreeEqSelfUnify using (treeEqSelf ; treeEqSelfReify)
open import Guard.SubstOpUnify using (substOp)

------------------------------------------------------------------------
-- Shorthand.

-- sndArg2 applied at any orig, recs: returns recs.
sndArg2RedV3 : (orig recs : Term) ->
  Deriv (eqF (ap2 sndArg2 orig recs) recs)
sndArg2RedV3 orig recs =
  ruleTrans (postRed Snd Pair orig recs) (axSnd orig recs)

------------------------------------------------------------------------
-- Rec unfolding for thmT = Rec O thmTStep.
--
-- Given:  Deriv (ap1 thmT (reify a) = reify (thFun a))
--         Deriv (ap1 thmT (reify b) = reify (thFun b))
-- conclude Deriv about thmT applied at the nd-node, expressed via
-- thmTStep.

recUnfoldIHV3 :
  (ra rb : Term) (a b : Term) ->
  Deriv (eqF (ap1 thmT a) ra) ->
  Deriv (eqF (ap1 thmT b) rb) ->
  Deriv (eqF (ap1 thmT (ap2 Pair a b))
                 (ap2 thmTStep (ap2 Pair a b)
                               (ap2 Pair ra rb)))
recUnfoldIHV3 ra rb a b iha ihb =
  ruleTrans (recNdRed O thmTStep a b)
  (congR thmTStep (ap2 Pair a b)
    (ruleTrans (congL Pair (ap1 thmT b) iha)
               (congR Pair ra ihb)))

------------------------------------------------------------------------
-- When data = Pair x y (nd case): thmTStep selects ndDispatchV3.

guardNdV3 : (tag x y recs : Term) ->
  Deriv (eqF (ap2 thmTStep (ap2 Pair tag (ap2 Pair x y)) recs)
                 (ap2 ndDispatchV3 (ap2 Pair tag (ap2 Pair x y)) recs))
guardNdV3 tag x y recs =
  let orig = ap2 Pair tag (ap2 Pair x y)
      checkIsLf = ap2 dataIsLfV3 orig recs
  in ruleTrans (fanRed dataIsLfV3 (Fan lfDispatchV3 ndDispatchV3 Pair) IfLf orig recs)
     (ruleTrans (congL IfLf (ap2 (Fan lfDispatchV3 ndDispatchV3 Pair) orig recs)
                  -- compute check: Snd(orig) = Pair x y, compared to O, gives falseT
                  (ruleTrans (fanRed (Lift Snd) (kF2 O) TreeEq orig recs)
                  (ruleTrans (congL TreeEq (ap2 (kF2 O) orig recs)
                               (ruleTrans (liftRed Snd orig recs)
                                          (axSnd tag (ap2 Pair x y))))
                  (ruleTrans (congR TreeEq (ap2 Pair x y)
                               (constF2Red O orig recs))
                             (axTreeEqNL x y)))))
     (ruleTrans (congR IfLf falseT
                  (fanRed lfDispatchV3 ndDispatchV3 Pair orig recs))
                (axIfLfN O O (ap2 lfDispatchV3 orig recs)
                             (ap2 ndDispatchV3 orig recs))))

------------------------------------------------------------------------
-- When data = O (lf case): thmTStep selects lfDispatchV3.

guardLfV3 : (tag recs : Term) ->
  Deriv (eqF (ap2 thmTStep (ap2 Pair tag O) recs)
                 (ap2 lfDispatchV3 (ap2 Pair tag O) recs))
guardLfV3 tag recs =
  let orig = ap2 Pair tag O
  in ruleTrans (fanRed dataIsLfV3 (Fan lfDispatchV3 ndDispatchV3 Pair) IfLf orig recs)
     (ruleTrans (congL IfLf (ap2 (Fan lfDispatchV3 ndDispatchV3 Pair) orig recs)
                  -- compute check: Snd(orig) = O, compared to O, gives O
                  (ruleTrans (fanRed (Lift Snd) (kF2 O) TreeEq orig recs)
                  (ruleTrans (congL TreeEq (ap2 (kF2 O) orig recs)
                               (ruleTrans (liftRed Snd orig recs)
                                          (axSnd tag O)))
                  (ruleTrans (congR TreeEq O (constF2Red O orig recs))
                             axTreeEqLL))))
     (ruleTrans (congR IfLf O
                  (fanRed lfDispatchV3 ndDispatchV3 Pair orig recs))
                (axIfLfL (ap2 lfDispatchV3 orig recs)
                         (ap2 ndDispatchV3 orig recs))))

------------------------------------------------------------------------
-- Intermediate passthrough (V3): when the data of a node has shape
-- Pair(sp2a, sp2b) and the tag itself is a valid sub-encoding tagT
-- (so ndDispatchV3 misses at it), thmT pushes through to
-- Pair(thmT tagT, thmT (Pair sp2a sp2b)).

intermediateGenericV3 :
  (tagT datT : Term)
  (sp2a sp2b : Term)
  -> ((x recs : Term) ->
      Deriv (eqF (ap2 ndDispatchV3 (ap2 Pair tagT x) recs)
                     (ap2 sndArg2 (ap2 Pair tagT x) recs)))
  -> Deriv (eqF (ap1 thmT (ap2 Pair tagT (ap2 Pair sp2a sp2b)))
                    (ap2 Pair (ap1 thmT tagT)
                              (ap1 thmT (ap2 Pair sp2a sp2b))))
intermediateGenericV3 tagT datT sp2a sp2b dispMiss =
  let dat  = ap2 Pair sp2a sp2b
      orig = ap2 Pair tagT dat
      recs = ap2 Pair (ap1 thmT tagT) (ap1 thmT dat)
  in ruleTrans (recNdRed O thmTStep tagT dat)
     (ruleTrans (guardNdV3 tagT sp2a sp2b recs)
     (ruleTrans (dispMiss dat recs)
                (sndArg2RedV3 orig recs)))

------------------------------------------------------------------------
-- case19V3Match: at a genuine trans node where the middle terms agree,
-- case19V3 reduces to  Pair (leftT sp1-result) (rightT sp2-result) .
--
-- Under REV2's sentinel change, case19V3's on-miss branch returns
-- codeTrueT (not O).  But at the MATCH point (middle terms agree),
-- the IfLf selects the on-match branch; the on-miss value never
-- appears.  So the proof here is unchanged.

case19V3Match :
  (tag dat recTag tC uC vC : Term) ->
  (Deriv (eqF (ap2 TreeEq uC uC) O)) ->
  Deriv (eqF (ap2 case19V3
                   (ap2 Pair tag dat)
                   (ap2 Pair recTag (ap2 Pair (ap2 Pair tC uC) (ap2 Pair uC vC))))
                 (ap2 Pair tC vC))
case19V3Match tag dat recTag tC uC vC uCSelf =
  let orig = ap2 Pair tag dat
      recs = ap2 Pair recTag (ap2 Pair (ap2 Pair tC uC) (ap2 Pair uC vC))
      checkF  = Fan recsAR recsBL TreeEq
      matchF  = Fan recsAL recsBR Pair
      branchF = Fan matchF (kF2 codeTrueT) Pair
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
           uCSelf))))
     -- branchF reduces to Pair (matchF result) (kF2 codeTrueT result) = Pair (Pair tC vC) codeTrueT
     (ruleTrans
       (congR IfLf O
         (ruleTrans (fanRed matchF (kF2 codeTrueT) Pair orig recs)
         (ruleTrans
           (congL Pair (ap2 (kF2 codeTrueT) orig recs)
             (ruleTrans (fanRed recsAL recsBR Pair orig recs)
             (ruleTrans
               (congL Pair (ap2 recsBR orig recs)
                 (recsALRed orig recTag tC uC (ap2 Pair uC vC)))
               (congR Pair tC
                 (recsBRRed orig recTag (ap2 Pair tC uC) uC vC)))))
           (congR Pair (ap2 Pair tC vC)
             (constF2Red codeTrueT orig recs)))))
       (axIfLfL (ap2 Pair tC vC) codeTrueT)))

------------------------------------------------------------------------
-- case23V3Match: the ruleInst reduction.
--
-- Input shape:
--   orig = Pair tag (Pair origAval other)
--         -- tag is the outer n23-tag (ignored by case23V3),
--         -- origAval is the substitution-parameter pair,
--         -- other is the sub-proof encoding (irrelevant to the Fun2).
--   recs = Pair recTag (Pair recA (Pair L R))
--         -- recTag = thmT tag (ignored), recA = thmT origAval (ignored),
--         -- (L, R) = the thmT-result of the sub-proof = codeEqn (subEq).
--
-- Result:  Pair (substOp origAval L) (substOp origAval R)

case23V3Match :
  (tag origAval other recTag recA L R : Term) ->
  Deriv (eqF (ap2 case23V3
                   (ap2 Pair tag (ap2 Pair origAval other))
                   (ap2 Pair recTag (ap2 Pair recA (ap2 Pair L R))))
                 (ap2 Pair (ap2 substOp origAval L)
                           (ap2 substOp origAval R)))
case23V3Match tag origAval other recTag recA L R =
  let orig = ap2 Pair tag (ap2 Pair origAval other)
      recs = ap2 Pair recTag (ap2 Pair recA (ap2 Pair L R))
      leftF  = Fan origA recsBL substOp
      rightF = Fan origA recsBR substOp
      -- leftF reduces to  substOp origAval L
      leftEval = ruleTrans (fanRed origA recsBL substOp orig recs)
                 (ruleTrans (congL substOp (ap2 recsBL orig recs)
                              (origARed tag origAval other recs))
                            (congR substOp origAval
                              (recsBLRed orig recTag recA L R)))
      -- rightF reduces to  substOp origAval R
      rightEval = ruleTrans (fanRed origA recsBR substOp orig recs)
                  (ruleTrans (congL substOp (ap2 recsBR orig recs)
                               (origARed tag origAval other recs))
                             (congR substOp origAval
                               (recsBRRed orig recTag recA L R)))
  in ruleTrans (fanRed leftF rightF Pair orig recs)
     (ruleTrans (congL Pair (ap2 rightF orig recs) leftEval)
                (congR Pair (ap2 substOp origAval L) rightEval))
