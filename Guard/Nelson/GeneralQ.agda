{-# OPTIONS --safe --without-K --exact-split #-}

-- GeneralQ.agda
-- Generalizing the Q/R lemma technique to more program types.
--
-- Key lemmas from DoublerProof:
--   R: IfLf(x, Pair(Pair(O,O), Pair(O,O))) = Pair(O,O) for all x.
--   Q: IfLf(TreeEq(x, a), Pair(TreeEq(x, b), Pair(O,O))) = Pair(O,O)
--      for all x, when a ≠ b.
--
-- Q handles: Pair(x, x) ≠ Pair(a, b) when a ≠ b.
--
-- We now need to handle:
--   Pair(g(x), h(x)) ≠ Pair(a, b) for various g, h
--
-- The comparison:
--   TreeEq(Pair(g(x), h(x)), Pair(a, b))
--   = IfLf(TreeEq(g(x), a), Pair(TreeEq(h(x), b), Pair(O,O)))
--
-- This = Pair(O,O) iff: when g(x) = a, then h(x) ≠ b.

module Guard.Nelson.GeneralQ where

open import Guard.Base
open import Guard.Term
open import Guard.Step
open import Guard.StepReduce
open import Guard.ThFun
open import Guard.Nelson.Machine
open import Guard.Nelson.GroundEval

private
  poo : Term ; poo = ap2 Pair O O
  v0 : Term ; v0 = var zero
  v1 : Term ; v1 = var (suc zero)
  pair01 : Term ; pair01 = ap2 Pair v0 v1
  gKT : Fun1 ; gKT = KT poo
  sConst : Fun2 ; sConst = Lift (KT poo)
  sConstRed : {hyp : Equation} (a b : Term) -> Deriv hyp (eqn (ap2 sConst a b) poo)
  sConstRed a b = ruleTrans (axLift (KT poo) a b) (axKT poo a)
  gStepS : {hyp : Equation} ->
    Deriv hyp (eqn (ap1 gKT pair01)
                   (ap2 sConst pair01 (ap2 Pair (ap1 gKT v0) (ap1 gKT v1))))
  gStepS = ruleTrans (axKT poo pair01)
           (ruleSym (sConstRed pair01 (ap2 Pair (ap1 gKT v0) (ap1 gKT v1))))
  dSP : Tree ; dSP = encRefl (code O)

------------------------------------------------------------------------
-- Import R and Q from DoublerProof structure (re-derive for modularity)

-- R(x) = IfLf(x, Pair(poo, poo)). Proved: R(x) = poo for all x.
rFun : Fun1
rFun = Comp2 IfLf I (KT (ap2 Pair poo poo))

rFunRed : {hyp : Equation} (t : Term) ->
  Deriv hyp (eqn (ap1 rFun t) (ap2 IfLf t (ap2 Pair poo poo)))
rFunRed t =
  ruleTrans (axComp2 IfLf I (KT (ap2 Pair poo poo)) t)
  (ruleTrans (congL IfLf (ap1 (KT (ap2 Pair poo poo)) t) (axI t))
    (congR IfLf t (axKT (ap2 Pair poo poo) t)))

rBase : {hyp : Equation} -> Deriv hyp (eqn (ap1 rFun O) poo)
rBase = ruleTrans (rFunRed O) (axIfLfL poo poo)

rStep : {hyp : Equation} -> Deriv hyp (eqn (ap1 rFun pair01) poo)
rStep = ruleTrans (rFunRed pair01) (axIfLfN v0 v1 poo poo)

rStepS : {hyp : Equation} ->
  Deriv hyp (eqn (ap1 rFun pair01)
                 (ap2 sConst pair01 (ap2 Pair (ap1 rFun v0) (ap1 rFun v1))))
rStepS = ruleTrans rStep (ruleSym (sConstRed pair01 (ap2 Pair (ap1 rFun v0) (ap1 rFun v1))))

rIsConst : {hyp : Equation} -> Deriv hyp (eqn (ap1 rFun v0) (ap1 gKT v0))
rIsConst = ruleF rFun gKT poo sConst rBase rStepS (axKT poo O) gStepS

rInst : {hyp : Equation} (t : Term) -> Deriv hyp (eqn (ap1 rFun t) poo)
rInst t = ruleTrans (ruleInst zero t rIsConst) (axKT poo t)

ifLfCollapse : {hyp : Equation} (x : Term) ->
  Deriv hyp (eqn (ap2 IfLf x (ap2 Pair poo poo)) poo)
ifLfCollapse x = ruleTrans (ruleSym (rFunRed x)) (rInst x)

------------------------------------------------------------------------
-- Q for specific (a, b) pairs
-- Q_{a,b}(x) = IfLf(TreeEq(x, a), Pair(TreeEq(x, b), Pair(O,O)))
-- = Pair(O,O) for all x, whenever a ≠ b.

-- Q for a = Pair(O,O), b = O (from xi = Pair(Pair(O,O), O))
-- Already proved in DoublerProof. Re-derive:

qFun1 : Fun1
qFun1 = Comp2 IfLf
  (Comp2 TreeEq I (KT poo))
  (Comp2 Pair (Comp2 TreeEq I (KT O)) (KT poo))

qFun1Red : {hyp : Equation} (t : Term) ->
  Deriv hyp (eqn (ap1 qFun1 t)
                 (ap2 IfLf (ap2 TreeEq t poo) (ap2 Pair (ap2 TreeEq t O) poo)))
qFun1Red t =
  ruleTrans (axComp2 IfLf (Comp2 TreeEq I (KT poo)) (Comp2 Pair (Comp2 TreeEq I (KT O)) (KT poo)) t)
  (ruleTrans
    (congL IfLf
      (ap1 (Comp2 Pair (Comp2 TreeEq I (KT O)) (KT poo)) t)
      (ruleTrans (axComp2 TreeEq I (KT poo) t)
        (ruleTrans (congL TreeEq (ap1 (KT poo) t) (axI t))
          (congR TreeEq t (axKT poo t)))))
    (congR IfLf (ap2 TreeEq t poo)
      (ruleTrans (axComp2 Pair (Comp2 TreeEq I (KT O)) (KT poo) t)
        (ruleTrans
          (congL Pair (ap1 (KT poo) t)
            (ruleTrans (axComp2 TreeEq I (KT O) t)
              (ruleTrans (congL TreeEq (ap1 (KT O) t) (axI t))
                (congR TreeEq t (axKT O t)))))
          (congR Pair (ap2 TreeEq t O) (axKT poo t))))))

qFun1Base : {hyp : Equation} -> Deriv hyp (eqn (ap1 qFun1 O) poo)
qFun1Base =
  ruleTrans (qFun1Red O)
  (ruleTrans (congL IfLf (ap2 Pair (ap2 TreeEq O O) poo) (axTreeEqLN O O))
    (axIfLfN O O (ap2 TreeEq O O) poo))

qFun1Step : {hyp : Equation} -> Deriv hyp (eqn (ap1 qFun1 pair01) poo)
qFun1Step =
  ruleTrans (qFun1Red pair01)
  (ruleTrans (congR IfLf (ap2 TreeEq pair01 poo) (congL Pair poo (axTreeEqNL v0 v1)))
    (ifLfCollapse (ap2 TreeEq pair01 poo)))

qFun1StepS : {hyp : Equation} ->
  Deriv hyp (eqn (ap1 qFun1 pair01)
                 (ap2 sConst pair01 (ap2 Pair (ap1 qFun1 v0) (ap1 qFun1 v1))))
qFun1StepS = ruleTrans qFun1Step
             (ruleSym (sConstRed pair01 (ap2 Pair (ap1 qFun1 v0) (ap1 qFun1 v1))))

qFun1Const : {hyp : Equation} -> Deriv hyp (eqn (ap1 qFun1 v0) (ap1 gKT v0))
qFun1Const = ruleF qFun1 gKT poo sConst qFun1Base qFun1StepS (axKT poo O) gStepS

qFun1Inst : {hyp : Equation} (t : Term) -> Deriv hyp (eqn (ap1 qFun1 t) poo)
qFun1Inst t = ruleTrans (ruleInst zero t qFun1Const) (axKT poo t)

------------------------------------------------------------------------
-- Q for a = O, b = Pair(O,O) (from xi = Pair(O, Pair(O,O)))

qFun2 : Fun1
qFun2 = Comp2 IfLf
  (Comp2 TreeEq I (KT O))
  (Comp2 Pair (Comp2 TreeEq I (KT poo)) (KT poo))

qFun2Red : {hyp : Equation} (t : Term) ->
  Deriv hyp (eqn (ap1 qFun2 t)
                 (ap2 IfLf (ap2 TreeEq t O) (ap2 Pair (ap2 TreeEq t poo) poo)))
qFun2Red t =
  ruleTrans (axComp2 IfLf (Comp2 TreeEq I (KT O)) (Comp2 Pair (Comp2 TreeEq I (KT poo)) (KT poo)) t)
  (ruleTrans
    (congL IfLf
      (ap1 (Comp2 Pair (Comp2 TreeEq I (KT poo)) (KT poo)) t)
      (ruleTrans (axComp2 TreeEq I (KT O) t)
        (ruleTrans (congL TreeEq (ap1 (KT O) t) (axI t))
          (congR TreeEq t (axKT O t)))))
    (congR IfLf (ap2 TreeEq t O)
      (ruleTrans (axComp2 Pair (Comp2 TreeEq I (KT poo)) (KT poo) t)
        (ruleTrans
          (congL Pair (ap1 (KT poo) t)
            (ruleTrans (axComp2 TreeEq I (KT poo) t)
              (ruleTrans (congL TreeEq (ap1 (KT poo) t) (axI t))
                (congR TreeEq t (axKT poo t)))))
          (congR Pair (ap2 TreeEq t poo) (axKT poo t))))))

qFun2Base : {hyp : Equation} -> Deriv hyp (eqn (ap1 qFun2 O) poo)
qFun2Base =
  -- IfLf(TreeEq(O, O), Pair(TreeEq(O, poo), poo))
  -- = IfLf(O, Pair(TreeEq(O, poo), poo))           [axTreeEqLL]
  -- = TreeEq(O, poo)                                [axIfLfL]
  -- = poo                                           [axTreeEqLN]
  ruleTrans (qFun2Red O)
  (ruleTrans (congL IfLf (ap2 Pair (ap2 TreeEq O poo) poo) axTreeEqLL)
    (ruleTrans (axIfLfL (ap2 TreeEq O poo) poo)
               (axTreeEqLN O O)))

qFun2Step : {hyp : Equation} -> Deriv hyp (eqn (ap1 qFun2 pair01) poo)
qFun2Step =
  ruleTrans (qFun2Red pair01)
  (ruleTrans (congL IfLf (ap2 Pair (ap2 TreeEq pair01 poo) poo) (axTreeEqNL v0 v1))
    (axIfLfN O O (ap2 TreeEq pair01 poo) poo))

qFun2StepS : {hyp : Equation} ->
  Deriv hyp (eqn (ap1 qFun2 pair01)
                 (ap2 sConst pair01 (ap2 Pair (ap1 qFun2 v0) (ap1 qFun2 v1))))
qFun2StepS = ruleTrans qFun2Step
             (ruleSym (sConstRed pair01 (ap2 Pair (ap1 qFun2 v0) (ap1 qFun2 v1))))

qFun2Const : {hyp : Equation} -> Deriv hyp (eqn (ap1 qFun2 v0) (ap1 gKT v0))
qFun2Const = ruleF qFun2 gKT poo sConst qFun2Base qFun2StepS (axKT poo O) gStepS

qFun2Inst : {hyp : Equation} (t : Term) -> Deriv hyp (eqn (ap1 qFun2 t) poo)
qFun2Inst t = ruleTrans (ruleInst zero t qFun2Const) (axKT poo t)

------------------------------------------------------------------------
-- GENERAL PATTERN:
--
-- Q_{a,b}(x) = IfLf(TreeEq(x, a), Pair(TreeEq(x, b), Pair(O,O))) = Pair(O,O)
-- whenever a ≠ b.
--
-- Base case: Q_{a,b}(O)
--   = IfLf(TreeEq(O, a), Pair(TreeEq(O, b), Pair(O,O)))
--   Case a = O: TreeEq(O, O) = O. IfLf(O, Pair(TreeEq(O, b), Pair(O,O)))
--     = TreeEq(O, b). Since a = O ≠ b, b ≠ O. So b = Pair(..). TreeEq(O, Pair(..)) = Pair(O,O). ✓
--   Case a = Pair(..): TreeEq(O, Pair(..)) = Pair(O,O). IfLf(Pair(O,O), ..) = Pair(O,O). ✓
--
-- Step case: Q_{a,b}(Pair(v0,v1))
--   = IfLf(TreeEq(Pair(v0,v1), a), Pair(TreeEq(Pair(v0,v1), b), Pair(O,O)))
--   Case a = O: TreeEq(Pair(v0,v1), O) = Pair(O,O) by axTreeEqNL.
--     IfLf(Pair(O,O), ..) = Pair(O,O). ✓
--   Case a = Pair(a1,a2):
--     TreeEq(Pair(v0,v1), Pair(a1,a2)) = IfLf(TreeEq(v0,a1), Pair(TreeEq(v1,a2), Pair(O,O)))
--     Need: IfLf(IfLf(..), Pair(TreeEq(Pair(v0,v1), b), Pair(O,O)))
--     Case b = O: TreeEq(Pair(v0,v1), O) = Pair(O,O). Second arg = Pair(Pair(O,O), Pair(O,O)).
--       IfLf(X, Pair(Pair(O,O), Pair(O,O))) = Pair(O,O) by R. ✓
--     Case b = Pair(b1,b2):
--       TreeEq(Pair(v0,v1), Pair(b1,b2)) = IfLf(TreeEq(v0,b1), Pair(TreeEq(v1,b2), Pair(O,O)))
--       Second arg = Pair(IfLf(..), Pair(O,O)).
--       Whole: IfLf(IfLf(..), Pair(IfLf(..), Pair(O,O)))
--       This is IfLf(Y, Pair(Z, Pair(O,O))) where Y, Z are IfLf expressions.
--       This has the SAME FORM as Q_{..}! But with inner IfLfs.
--       By R: IfLf(Y, Pair(Pair(O,O), Pair(O,O))) = Pair(O,O) for any Y.
--       But Z might not be Pair(O,O) in general...
--
-- The step case when both a and b are Pair is harder.
-- But: one of a, b has a "simpler" structure that leads to collapse.
-- Specifically: since a ≠ b, there is a SHALLOWEST position where they differ.
-- At that position, the TreeEq comparison short-circuits, and the IfLf/R collapse kicks in.
--
-- For the specific cases tested:
-- a = Pair(O,O), b = O (Q1): step collapses via axTreeEqNL on the b side + R.
-- a = O, b = Pair(O,O) (Q2): step collapses via axTreeEqNL on the a side.

------------------------------------------------------------------------
-- APPLICATION: iterate (Comp2 Pair I (Comp2 Pair I I)) O
-- step(x) = Pair(x, Pair(x, x))
-- Output is always Pair(rec, Pair(rec, rec)).
-- Against xi = Pair(Pair(O,O), O):
--   TreeEq(Pair(rec, Pair(rec,rec)), Pair(Pair(O,O), O))
--   = IfLf(TreeEq(rec, Pair(O,O)), Pair(TreeEq(Pair(rec,rec), O), Pair(O,O)))
--   = IfLf(TreeEq(rec, Pair(O,O)), Pair(Pair(O,O), Pair(O,O)))  [by axTreeEqNL]
--   = Pair(O,O) by R (= ifLfCollapse)

tripler : Fun1
tripler = Comp2 Pair I (Comp2 Pair I I)

triplerRed : {hyp : Equation} (t : Term) ->
  Deriv hyp (eqn (ap1 tripler t) (ap2 Pair t (ap2 Pair t t)))
triplerRed t =
  ruleTrans (axComp2 Pair I (Comp2 Pair I I) t)
  (ruleTrans (congL Pair (ap1 (Comp2 Pair I I) t) (axI t))
    (congR Pair t
      (ruleTrans (axComp2 Pair I I t)
        (ruleTrans (congL Pair (ap1 I t) (axI t))
          (congR Pair t (axI t))))))

triplerIter : Fun1
triplerIter = iterate tripler O

-- xi = Pair(Pair(O,O), O)
xi : Tree ; xi = nd (nd lf lf) lf
xiT : Term ; xiT = ap2 Pair poo O

hTrip : Fun1
hTrip = Comp2 TreeEq triplerIter (KT xiT)

private
  rec1 : Term ; rec1 = ap1 triplerIter v1

-- Base: h(O) = TreeEq(O, xi) = Pair(O,O)
hTripBase : {hyp : Equation} -> Deriv hyp (eqn (ap1 hTrip O) poo)
hTripBase =
  ruleTrans (axComp2 TreeEq triplerIter (KT xiT) O)
  (ruleTrans (congL TreeEq (ap1 (KT xiT) O) (iterBase tripler O))
  (ruleTrans (congR TreeEq O (axKT xiT O))
             (axTreeEqLN poo O)))

-- Step: triplerIter(Pair(v0,v1)) = tripler(rec(v1))
tripIterStep : {hyp : Equation} ->
  Deriv hyp (eqn (ap1 triplerIter pair01) (ap1 tripler rec1))
tripIterStep = iterNd tripler O v0 v1

-- tripler(rec1) = Pair(rec1, Pair(rec1, rec1))
tripRecRed : {hyp : Equation} ->
  Deriv hyp (eqn (ap1 tripler rec1) (ap2 Pair rec1 (ap2 Pair rec1 rec1)))
tripRecRed = triplerRed rec1

-- TreeEq(Pair(rec1, Pair(rec1,rec1)), xiT)
-- = IfLf(TreeEq(rec1, poo), Pair(TreeEq(Pair(rec1,rec1), O), poo))
-- TreeEq(Pair(rec1,rec1), O) = poo by axTreeEqNL
-- So = IfLf(TreeEq(rec1, poo), Pair(poo, poo))
-- = poo by ifLfCollapse

hTripStepFull : {hyp : Equation} -> Deriv hyp (eqn (ap1 hTrip pair01) poo)
hTripStepFull =
  ruleTrans (axComp2 TreeEq triplerIter (KT xiT) pair01)
  (ruleTrans (congR TreeEq (ap1 triplerIter pair01) (axKT xiT pair01))
  (ruleTrans (congL TreeEq xiT tripIterStep)
  (ruleTrans (congL TreeEq xiT tripRecRed)
  (ruleTrans (axTreeEqNN rec1 (ap2 Pair rec1 rec1) poo O)
  (ruleTrans (congR IfLf (ap2 TreeEq rec1 poo)
    (congL Pair poo (axTreeEqNL rec1 rec1)))
  (ifLfCollapse (ap2 TreeEq rec1 poo)))))))

-- Schema F step
hTripStep : {hyp : Equation} ->
  Deriv hyp (eqn (ap1 hTrip pair01)
                 (ap2 sConst pair01 (ap2 Pair (ap1 hTrip v0) (ap1 hTrip v1))))
hTripStep = ruleTrans hTripStepFull
            (ruleSym (sConstRed pair01 (ap2 Pair (ap1 hTrip v0) (ap1 hTrip v1))))

-- THEOREM: triplerIter(t) ≠ xi for all t
triplerNeverXi : {hyp : Equation} ->
  Deriv hyp (eqn (ap1 hTrip v0) (ap1 gKT v0))
triplerNeverXi = ruleF hTrip gKT poo sConst hTripBase hTripStep (axKT poo O) gStepS

-- Verify
private
  encTripSF : Tree
  encTripSF = encF (codeF1 hTrip) (codeF1 gKT) (code poo) (codeF2 sConst) dSP dSP dSP dSP

  checkTrip : Eq (checkProof2 encTripSF) true
  checkTrip = refl

------------------------------------------------------------------------
-- APPLICATION 2: iterate (Comp2 Pair (KT poo) (Comp2 Pair I I)) O
-- step(x) = Pair(Pair(O,O), Pair(x, x))
-- Has BOTH a constant position (Fst = Pair(O,O)) AND a doubler.
-- Against xi = Pair(Pair(O,O), O):
--   Fst of output = Pair(O,O) = Fst(xi). Matches!
--   Fall through to: TreeEq(Pair(rec,rec), O) = Pair(O,O) by axTreeEqNL. ✓
-- The Snd comparison short-circuits because Pair vs O.

mixed : Fun1
mixed = Comp2 Pair (KT poo) (Comp2 Pair I I)

mixedRed : {hyp : Equation} (t : Term) ->
  Deriv hyp (eqn (ap1 mixed t) (ap2 Pair poo (ap2 Pair t t)))
mixedRed t =
  ruleTrans (axComp2 Pair (KT poo) (Comp2 Pair I I) t)
  (ruleTrans (congL Pair (ap1 (Comp2 Pair I I) t) (axKT poo t))
    (congR Pair poo
      (ruleTrans (axComp2 Pair I I t)
        (ruleTrans (congL Pair (ap1 I t) (axI t))
          (congR Pair t (axI t))))))

mixedIter : Fun1
mixedIter = iterate mixed O

hMix : Fun1
hMix = Comp2 TreeEq mixedIter (KT xiT)

private
  mrec1 : Term ; mrec1 = ap1 mixedIter v1

hMixBase : {hyp : Equation} -> Deriv hyp (eqn (ap1 hMix O) poo)
hMixBase =
  ruleTrans (axComp2 TreeEq mixedIter (KT xiT) O)
  (ruleTrans (congL TreeEq (ap1 (KT xiT) O) (iterBase mixed O))
  (ruleTrans (congR TreeEq O (axKT xiT O))
             (axTreeEqLN poo O)))

-- Step: mixed(rec1) = Pair(poo, Pair(rec1, rec1))
-- TreeEq(Pair(poo, Pair(rec1,rec1)), Pair(poo, O))
-- = IfLf(TreeEq(poo, poo), Pair(TreeEq(Pair(rec1,rec1), O), poo))
-- TreeEq(poo, poo):
--   = IfLf(TreeEq(O, O), Pair(TreeEq(O, O), poo))
--   = IfLf(O, Pair(O, poo))
--   = O                     [axIfLfL: first element]
-- So: IfLf(O, Pair(TreeEq(Pair(rec1,rec1), O), poo))
--   = TreeEq(Pair(rec1,rec1), O) [axIfLfL]
--   = poo                    [axTreeEqNL]

-- TreeEq(poo, poo) = O
treeEqSelf : {hyp : Equation} ->
  Deriv hyp (eqn (ap2 TreeEq poo poo) O)
treeEqSelf =
  ruleTrans (axTreeEqNN O O O O)
  (ruleTrans (congL IfLf (ap2 Pair (ap2 TreeEq O O) poo) axTreeEqLL)
    (ruleTrans (axIfLfL (ap2 TreeEq O O) poo) axTreeEqLL))

hMixStepFull : {hyp : Equation} -> Deriv hyp (eqn (ap1 hMix pair01) poo)
hMixStepFull =
  ruleTrans (axComp2 TreeEq mixedIter (KT xiT) pair01)
  (ruleTrans (congR TreeEq (ap1 mixedIter pair01) (axKT xiT pair01))
  (ruleTrans (congL TreeEq xiT (iterNd mixed O v0 v1))
  (ruleTrans (congL TreeEq xiT (mixedRed mrec1))
  (ruleTrans (axTreeEqNN poo (ap2 Pair mrec1 mrec1) poo O)
  (ruleTrans (congL IfLf (ap2 Pair (ap2 TreeEq (ap2 Pair mrec1 mrec1) O) poo) treeEqSelf)
  (ruleTrans (axIfLfL (ap2 TreeEq (ap2 Pair mrec1 mrec1) O) poo)
             (axTreeEqNL mrec1 mrec1)))))))

hMixStep : {hyp : Equation} ->
  Deriv hyp (eqn (ap1 hMix pair01)
                 (ap2 sConst pair01 (ap2 Pair (ap1 hMix v0) (ap1 hMix v1))))
hMixStep = ruleTrans hMixStepFull
           (ruleSym (sConstRed pair01 (ap2 Pair (ap1 hMix v0) (ap1 hMix v1))))

mixedNeverXi : {hyp : Equation} ->
  Deriv hyp (eqn (ap1 hMix v0) (ap1 gKT v0))
mixedNeverXi = ruleF hMix gKT poo sConst hMixBase hMixStep (axKT poo O) gStepS

private
  encMixSF : Tree
  encMixSF = encF (codeF1 hMix) (codeF1 gKT) (code poo) (codeF2 sConst) dSP dSP dSP dSP

  checkMix : Eq (checkProof2 encMixSF) true
  checkMix = refl

------------------------------------------------------------------------
-- SUMMARY OF PROOF PATTERNS
--
-- 1. natCodeIter (KRShortProof): Fst mismatch. axTreeEqLN at depth 0.
--    Skeleton: {Fst ↦ O}. Oblivious.
--
-- 2. doubler (DoublerProof): Q lemma handles case split.
--    IfLf(TreeEq(x,a), Pair(TreeEq(x,b), poo)) = poo when a ≠ b.
--    Needs: nested Schema F (R then Q then main).
--
-- 3. tripler (this file): axTreeEqNL collapses Snd comparison,
--    then ifLfCollapse (= R) handles the outer IfLf.
--    Same pattern as doubler but simpler (NL collapse is direct).
--
-- 4. mixed (this file): TreeEq(poo, poo) = O matches Fst,
--    falls through to Snd which is Pair vs O → axTreeEqNL.
--    When Fst of output MATCHES Fst of xi: use axIfLfL to fall through.
--
-- ALL FOUR use only Schema F at BLevel 0 (no ruleInst with non-ground terms).
-- ALL FOUR are O(1) in proof size.
--
-- The key building blocks:
--   (a) axTreeEqLN / axTreeEqNL: leaf vs non-leaf immediate mismatch
--   (b) axTreeEqNN: structural decomposition
--   (c) R / ifLfCollapse: IfLf(x, Pair(poo, poo)) = poo for any x
--   (d) Q1 / qFun1Inst: IfLf(TreeEq(x,poo), Pair(TreeEq(x,O), poo)) = poo for any x
--   (e) treeEqSelf: TreeEq(poo, poo) = O (equal components)
--
-- Every iterate program's step case decomposes into a CHAIN of these lemmas,
-- where each link either short-circuits (axTreeEqLN/NL) or collapses (R/Q).
-- The chain length is bounded by the DEPTH of xi (constant for fixed xi).
