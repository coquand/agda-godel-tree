{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.SubT -- our tree-based analog of Guard's substitution functor
-- (Exercise 24 [4], guard15.pdf p.14):
--
--     subT(<code(var n), codeA>, codeB)
--       =  reify (codedSubst codeA (code(var n)) codeB) .
--
-- Substitution data is packaged as ap2 Pair (reify (code (var n)))
-- (reify codeA), the target as reify codeB.  subT is built from RecP
-- plus combinators (Fan, Lift, Comp, Post, Pair, IfLf, TreeEq) -- no
-- new primitives.

module BRA.SubT where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Deriv
open import BRA.StepReduce

------------------------------------------------------------------------
-- Aux 1: dispatch on a Bool-as-Term result of TreeEq.
--
--   IfLf (boolCase b O falseT) (Pair m n) = boolCase b m n .

ifLfDispatch : (b : Bool) (matchVal noMatchVal : Term) ->
  Deriv (atomic (eqn (ap2 IfLf (boolCase b O falseT) (ap2 Pair matchVal noMatchVal))
                      (boolCase b matchVal noMatchVal)))
ifLfDispatch true  matchVal noMatchVal = axIfLfL matchVal noMatchVal
ifLfDispatch false matchVal noMatchVal = axIfLfN O O matchVal noMatchVal

------------------------------------------------------------------------
-- Aux 2: the inner IfLf pattern produced by axTreeEqNN reflects boolAnd.
--
--   IfLf (boolCase b1 O falseT) (Pair (boolCase b2 O falseT) falseT)
--     = boolCase (boolAnd b1 b2) O falseT .

boolAndIfLf : (b1 b2 : Bool) ->
  Deriv (atomic (eqn (ap2 IfLf (boolCase b1 O falseT)
                              (ap2 Pair (boolCase b2 O falseT) falseT))
                     (boolCase (boolAnd b1 b2) O falseT)))
boolAndIfLf true  true  = axIfLfL O falseT
boolAndIfLf true  false = axIfLfL falseT falseT
boolAndIfLf false b2    = axIfLfN O O (boolCase b2 O falseT) falseT

------------------------------------------------------------------------
-- Aux 3: TreeEq on two reified trees mirrors the meta-level treeEq.
--
--   ap2 TreeEq (reify a) (reify b) = boolCase (treeEq a b) O falseT .

treeEqRed : (a b : Tree) ->
  Deriv (atomic (eqn (ap2 TreeEq (reify a) (reify b))
                      (boolCase (treeEq a b) O falseT)))
treeEqRed lf       lf       = axTreeEqLL
treeEqRed lf       (nd c d) = axTreeEqLN (reify c) (reify d)
treeEqRed (nd a b) lf       = axTreeEqNL (reify a) (reify b)
treeEqRed (nd a b) (nd c d) =
  let s1 = axTreeEqNN (reify a) (reify b) (reify c) (reify d)
      ihAC = treeEqRed a c
      ihBD = treeEqRed b d
      pairBD : Term
      pairBD = ap2 Pair (ap2 TreeEq (reify b) (reify d)) falseT
      s2a : Deriv (atomic (eqn (ap2 IfLf (ap2 TreeEq (reify a) (reify c)) pairBD)
                                (ap2 IfLf (boolCase (treeEq a c) O falseT) pairBD)))
      s2a = congL IfLf pairBD ihAC
      newCond : Term
      newCond = boolCase (treeEq a c) O falseT
      newPairBD : Term
      newPairBD = ap2 Pair (boolCase (treeEq b d) O falseT) falseT
      s2b : Deriv (atomic (eqn (ap2 IfLf newCond pairBD)
                                (ap2 IfLf newCond newPairBD)))
      s2b = congR IfLf newCond (congL Pair falseT ihBD)
      s3 = boolAndIfLf (treeEq a c) (treeEq b d)
  in ruleTrans s1 (ruleTrans s2a (ruleTrans s2b s3))

------------------------------------------------------------------------
-- The combinators: subT, stepSubT, and the two halves of stepSubT.

checkEqSubT : Fun2
checkEqSubT = Fan (Lift (Comp Fst Fst)) (Lift Snd) TreeEq

contSubT : Fun2
contSubT = Fan (Lift (Comp Snd Fst)) (Post Snd Pair) Pair

stepSubT : Fun2
stepSubT = Fan checkEqSubT contSubT IfLf

subT : Fun2
subT = RecP stepSubT

------------------------------------------------------------------------
-- Reduction of stepSubT's two halves at generic arg1 = ap2 Pair p orig.
--
--   ap2 checkEqSubT (Pair p orig) recs  =  ap2 TreeEq (Fst p) orig
--   ap2 contSubT    (Pair p orig) recs  =  ap2 Pair (Snd p) recs

checkEqAt : (p orig recs : Term) ->
  Deriv (atomic (eqn (ap2 checkEqSubT (ap2 Pair p orig) recs)
                      (ap2 TreeEq (ap1 Fst p) orig)))
checkEqAt p orig recs =
  let arg1 : Term
      arg1 = ap2 Pair p orig
      r1 : Deriv (atomic (eqn (ap2 checkEqSubT arg1 recs)
                              (ap2 TreeEq (ap2 (Lift (Comp Fst Fst)) arg1 recs)
                                          (ap2 (Lift Snd) arg1 recs))))
      r1 = axFan (Lift (Comp Fst Fst)) (Lift Snd) TreeEq arg1 recs
      r2 : Deriv (atomic (eqn (ap2 (Lift (Comp Fst Fst)) arg1 recs) (ap1 Fst p)))
      r2 = ruleTrans (axLift (Comp Fst Fst) arg1 recs)
                     (ruleTrans (axComp Fst Fst arg1)
                                (cong1 Fst (axFst p orig)))
      r3 : Deriv (atomic (eqn (ap2 (Lift Snd) arg1 recs) orig))
      r3 = ruleTrans (axLift Snd arg1 recs) (axSnd p orig)
      r4 : Deriv (atomic (eqn (ap2 TreeEq (ap2 (Lift (Comp Fst Fst)) arg1 recs)
                                          (ap2 (Lift Snd) arg1 recs))
                              (ap2 TreeEq (ap1 Fst p) (ap2 (Lift Snd) arg1 recs))))
      r4 = congL TreeEq (ap2 (Lift Snd) arg1 recs) r2
      r5 : Deriv (atomic (eqn (ap2 TreeEq (ap1 Fst p) (ap2 (Lift Snd) arg1 recs))
                              (ap2 TreeEq (ap1 Fst p) orig)))
      r5 = congR TreeEq (ap1 Fst p) r3
  in ruleTrans r1 (ruleTrans r4 r5)

contAt : (p orig recs : Term) ->
  Deriv (atomic (eqn (ap2 contSubT (ap2 Pair p orig) recs)
                      (ap2 Pair (ap1 Snd p) recs)))
contAt p orig recs =
  let arg1 : Term
      arg1 = ap2 Pair p orig
      r1 : Deriv (atomic (eqn (ap2 contSubT arg1 recs)
                              (ap2 Pair (ap2 (Lift (Comp Snd Fst)) arg1 recs)
                                        (ap2 (Post Snd Pair) arg1 recs))))
      r1 = axFan (Lift (Comp Snd Fst)) (Post Snd Pair) Pair arg1 recs
      r2 : Deriv (atomic (eqn (ap2 (Lift (Comp Snd Fst)) arg1 recs) (ap1 Snd p)))
      r2 = ruleTrans (axLift (Comp Snd Fst) arg1 recs)
                     (ruleTrans (axComp Snd Fst arg1)
                                (cong1 Snd (axFst p orig)))
      r3 : Deriv (atomic (eqn (ap2 (Post Snd Pair) arg1 recs) recs))
      r3 = ruleTrans (axPost Snd Pair arg1 recs) (axSnd arg1 recs)
      r4 : Deriv (atomic (eqn (ap2 Pair (ap2 (Lift (Comp Snd Fst)) arg1 recs)
                                        (ap2 (Post Snd Pair) arg1 recs))
                              (ap2 Pair (ap1 Snd p) (ap2 (Post Snd Pair) arg1 recs))))
      r4 = congL Pair (ap2 (Post Snd Pair) arg1 recs) r2
      r5 : Deriv (atomic (eqn (ap2 Pair (ap1 Snd p) (ap2 (Post Snd Pair) arg1 recs))
                              (ap2 Pair (ap1 Snd p) recs)))
      r5 = congR Pair (ap1 Snd p) r3
  in ruleTrans r1 (ruleTrans r4 r5)

------------------------------------------------------------------------
-- Main lemma:
--   subT(<code(var n), codeA>, reify codeB)  =  reify (codedSubst codeA (code(var n)) codeB)
--
-- By meta-induction on the tree codeB.

subTDef : (n : Nat) (codeA codeB : Tree) ->
  Deriv (atomic (eqn (ap2 subT (ap2 Pair (reify (code (var n))) (reify codeA))
                                (reify codeB))
                      (reify (codedSubst codeA (code (var n)) codeB))))
subTDef n codeA lf =
  axRecPLf stepSubT (ap2 Pair (reify (code (var n))) (reify codeA))
subTDef n codeA (nd a b) =
  ruleTrans s1 (ruleTrans s2 (ruleTrans s6 (ruleTrans s7 s8)))
  where
    varT : Term
    varT = reify (code (var n))

    codeAT : Term
    codeAT = reify codeA

    p : Term
    p = ap2 Pair varT codeAT

    reifyA : Term
    reifyA = reify a

    reifyB : Term
    reifyB = reify b

    orig : Term
    orig = ap2 Pair reifyA reifyB

    arg1 : Term
    arg1 = ap2 Pair p orig

    varCode : Tree
    varCode = code (var n)

    recsA : Tree
    recsA = codedSubst codeA varCode a

    recsB : Tree
    recsB = codedSubst codeA varCode b

    recsTree : Tree
    recsTree = nd recsA recsB

    recA : Term
    recA = ap2 (RecP stepSubT) p reifyA

    recB : Term
    recB = ap2 (RecP stepSubT) p reifyB

    recs : Term
    recs = ap2 Pair recA recB

    treeEqB : Bool
    treeEqB = treeEq varCode (nd a b)

    ihA : Deriv (atomic (eqn recA (reify recsA)))
    ihA = subTDef n codeA a

    ihB : Deriv (atomic (eqn recB (reify recsB)))
    ihB = subTDef n codeA b

    -- Step 1: axRecPNd unfolds subT at the node.
    s1 : Deriv (atomic (eqn (ap2 subT p orig) (ap2 stepSubT arg1 recs)))
    s1 = axRecPNd stepSubT p reifyA reifyB

    -- Step 2: stepSubT = Fan checkEqSubT contSubT IfLf, axFan unfolds.
    s2 : Deriv (atomic (eqn (ap2 stepSubT arg1 recs)
                            (ap2 IfLf (ap2 checkEqSubT arg1 recs)
                                       (ap2 contSubT arg1 recs))))
    s2 = axFan checkEqSubT contSubT IfLf arg1 recs

    -- Step 3: rewrite the IfLf condition to TreeEq varT orig, then to boolCase.
    fstP : Deriv (atomic (eqn (ap1 Fst p) varT))
    fstP = axFst varT codeAT

    checkEqVarT : Deriv (atomic (eqn (ap2 checkEqSubT arg1 recs) (ap2 TreeEq varT orig)))
    checkEqVarT = ruleTrans (checkEqAt p orig recs) (congL TreeEq orig fstP)

    checkEqB : Deriv (atomic (eqn (ap2 checkEqSubT arg1 recs)
                                   (boolCase treeEqB O falseT)))
    checkEqB = ruleTrans checkEqVarT (treeEqRed varCode (nd a b))

    -- Step 5: rewrite the IfLf alternatives.
    sndP : Deriv (atomic (eqn (ap1 Snd p) codeAT))
    sndP = axSnd varT codeAT

    contCodeAT : Deriv (atomic (eqn (ap2 contSubT arg1 recs)
                                     (ap2 Pair codeAT recs)))
    contCodeAT = ruleTrans (contAt p orig recs) (congL Pair recs sndP)

    -- Step 6: combine condition + alternatives into a clean IfLf.
    s6 : Deriv (atomic (eqn (ap2 IfLf (ap2 checkEqSubT arg1 recs)
                                       (ap2 contSubT arg1 recs))
                            (ap2 IfLf (boolCase treeEqB O falseT)
                                       (ap2 Pair codeAT recs))))
    s6 = ruleTrans (congL IfLf (ap2 contSubT arg1 recs) checkEqB)
                   (congR IfLf (boolCase treeEqB O falseT) contCodeAT)

    -- Step 7: ifLfDispatch yields boolCase treeEqB codeAT recs.
    s7 : Deriv (atomic (eqn (ap2 IfLf (boolCase treeEqB O falseT)
                                       (ap2 Pair codeAT recs))
                            (boolCase treeEqB codeAT recs)))
    s7 = ifLfDispatch treeEqB codeAT recs

    -- Step 8: boolCase-by-cases.  In the false branch we need
    --   recs = ap2 Pair recA recB = ap2 Pair (reify recsA) (reify recsB) = reify recsTree
    -- which uses ihA, ihB.
    finishCase : (b' : Bool) ->
      Deriv (atomic (eqn (boolCase b' codeAT recs)
                          (reify (boolCase b' codeA recsTree))))
    finishCase true  = axRefl codeAT
    finishCase false = ruleTrans (congL Pair recB ihA) (congR Pair (reify recsA) ihB)

    s8 : Deriv (atomic (eqn (boolCase treeEqB codeAT recs)
                             (reify (boolCase treeEqB codeA recsTree))))
    s8 = finishCase treeEqB
