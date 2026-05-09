{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA2.Sb2 -- simultaneous double-substitution.
--
-- Analog of BRA2.Sb (which wraps subT for single-variable substitution),
-- but for substituting two distinct variables IN ONE WALK over the
-- formula code.  Single-variable subT cannot be nested cleanly when
-- the inner substituent is a stuck BRA expression like  ap1 cor (var n) ,
-- because the outer subT's RecP recursion gets stuck at non-Pair-shaped
-- sub-terms (cor x is ap1-shaped).  subT2 walks the original Tree once
-- and dispatches at each node: match varA-code → uA, match varB-code → uB,
-- else recurse.
--
-- Three-way dispatch at each node is implemented via NESTED IfLf:
--   IfLf testA (Pair uA (IfLf testB (Pair uB recs))) .
--
-- No postulates, no holes.

module BRA2.Sb2 where

open import BRA2.Base
open import BRA2.Term
open import BRA2.Formula
open import BRA2.DerivThreshold
open import BRA2.SubT using (ifLfDispatch ; treeEqRed)

------------------------------------------------------------------------
-- Combinators for subT2.
--
-- Substitution data layout:
--   sub-data  =  Pair (Pair varCodeA uA) (Pair varCodeB uB)
-- where each (varCode, u) pair gives one substitution.
--
-- step2SubT operates on (Pair sub-data orig) and recs.  Extractors:
--   varCodeA  =  Fst (Fst (Fst arg1))     -- Comp Fst (Comp Fst Fst)
--   uA        =  Snd (Fst (Fst arg1))     -- Comp Snd (Comp Fst Fst)
--   varCodeB  =  Fst (Snd (Fst arg1))     -- Comp Fst (Comp Snd Fst)
--   uB        =  Snd (Snd (Fst arg1))     -- Comp Snd (Comp Snd Fst)
--   orig      =  Snd arg1                  -- Snd

checkEqSubT2A : Fun2
checkEqSubT2A = Fan (Lift (Comp Fst (Comp Fst Fst))) (Lift Snd) TreeEq

checkEqSubT2B : Fun2
checkEqSubT2B = Fan (Lift (Comp Fst (Comp Snd Fst))) (Lift Snd) TreeEq

contInner2 : Fun2
contInner2 = Fan (Lift (Comp Snd (Comp Snd Fst))) (Post Snd Pair) Pair

innerStep2 : Fun2
innerStep2 = Fan checkEqSubT2B contInner2 IfLf

contOuter2 : Fun2
contOuter2 = Fan (Lift (Comp Snd (Comp Fst Fst))) innerStep2 Pair

stepSubT2 : Fun2
stepSubT2 = Fan checkEqSubT2A contOuter2 IfLf

subT2 : Fun2
subT2 = RecP stepSubT2

------------------------------------------------------------------------
-- Simultaneous double substitution on Term, total via safe defaults.
-- After the Tree=Term collapse, the previously-distinct  codedSubst2
-- (Tree-valued) and  codedSubstT2  (Term-valued) coincide.  We keep
-- both names as equal definitions so existing call sites continue to
-- typecheck.

codedSubstT2 : Term -> Term -> Term -> Term -> Term -> Term
codedSubstT2 uA uB varCodeA varCodeB O                       = O
codedSubstT2 uA uB varCodeA varCodeB (var n)                 = var n
codedSubstT2 uA uB varCodeA varCodeB (ap1 f t)               = ap1 f t
codedSubstT2 uA uB varCodeA varCodeB (ap2 Pair a b)          =
  boolCase (treeEq varCodeA (ap2 Pair a b))
    uA
    (boolCase (treeEq varCodeB (ap2 Pair a b))
      uB
      (ap2 Pair (codedSubstT2 uA uB varCodeA varCodeB a)
                (codedSubstT2 uA uB varCodeA varCodeB b)))
codedSubstT2 uA uB varCodeA varCodeB (ap2 Const a b)         = ap2 Const a b
codedSubstT2 uA uB varCodeA varCodeB (ap2 (Lift f) a b)      = ap2 (Lift f) a b
codedSubstT2 uA uB varCodeA varCodeB (ap2 (Post f h) a b)    = ap2 (Post f h) a b
codedSubstT2 uA uB varCodeA varCodeB (ap2 (Fan h1 h2 h) a b) = ap2 (Fan h1 h2 h) a b
codedSubstT2 uA uB varCodeA varCodeB (ap2 IfLf a b)          = ap2 IfLf a b
codedSubstT2 uA uB varCodeA varCodeB (ap2 TreeEq a b)        = ap2 TreeEq a b
codedSubstT2 uA uB varCodeA varCodeB (ap2 (treeRec f s) a b) = ap2 (treeRec f s) a b

codedSubst2 : Term -> Term -> Term -> Term -> Term -> Term
codedSubst2 = codedSubstT2

------------------------------------------------------------------------
-- After collapse, codedSubstT2 = codedSubst2 definitionally.

codedSubstT2_reify :
  (uA uB varCodeA varCodeB codeP : Term) ->
  Eq (codedSubstT2 uA uB varCodeA varCodeB codeP)
     (codedSubst2 uA uB varCodeA varCodeB codeP)
codedSubstT2_reify uA uB varA varB codeP = refl

------------------------------------------------------------------------
-- Reduction lemmas for the combinators.

-- checkEqAt2A : at sub-data and orig, checkEqSubT2A reduces to TreeEq varCodeA orig.

checkEqAt2A : (varCodeA uA varCodeB uB orig recs : Term) ->
  Deriv (atomic (eqn
    (ap2 checkEqSubT2A
      (ap2 Pair (ap2 Pair (ap2 Pair varCodeA uA) (ap2 Pair varCodeB uB)) orig)
      recs)
    (ap2 TreeEq varCodeA orig)))
checkEqAt2A varA uA varB uB orig recs =
  let
    p : Term
    p = ap2 Pair (ap2 Pair varA uA) (ap2 Pair varB uB)
    arg1 : Term
    arg1 = ap2 Pair p orig

    -- Step 1: Fan unfolds.
    r1 : Deriv (atomic (eqn (ap2 checkEqSubT2A arg1 recs)
                            (ap2 TreeEq
                              (ap2 (Lift (Comp Fst (Comp Fst Fst))) arg1 recs)
                              (ap2 (Lift Snd) arg1 recs))))
    r1 = axFan (Lift (Comp Fst (Comp Fst Fst))) (Lift Snd) TreeEq arg1 recs

    -- Step 2: reduce Lift (Comp Fst (Comp Fst Fst)) at arg1, recs to varA.
    --   ap1 (Comp Fst (Comp Fst Fst)) arg1 = Fst (Fst (Fst arg1)) = varA.
    eL1 : Deriv (atomic (eqn (ap2 (Lift (Comp Fst (Comp Fst Fst))) arg1 recs)
                              (ap1 (Comp Fst (Comp Fst Fst)) arg1)))
    eL1 = axLift (Comp Fst (Comp Fst Fst)) arg1 recs

    eL2 : Deriv (atomic (eqn (ap1 (Comp Fst (Comp Fst Fst)) arg1)
                              (ap1 Fst (ap1 (Comp Fst Fst) arg1))))
    eL2 = axComp Fst (Comp Fst Fst) arg1

    eL3 : Deriv (atomic (eqn (ap1 (Comp Fst Fst) arg1)
                              (ap1 Fst (ap1 Fst arg1))))
    eL3 = axComp Fst Fst arg1

    eL4 : Deriv (atomic (eqn (ap1 Fst arg1) p))
    eL4 = axFst p orig

    eL5 : Deriv (atomic (eqn (ap1 Fst (ap1 Fst arg1))
                              (ap1 Fst p)))
    eL5 = cong1 Fst eL4

    eL6 : Deriv (atomic (eqn (ap1 Fst p) (ap2 Pair varA uA)))
    eL6 = axFst (ap2 Pair varA uA) (ap2 Pair varB uB)

    eL7 : Deriv (atomic (eqn (ap1 Fst (ap1 Fst arg1)) (ap2 Pair varA uA)))
    eL7 = ruleTrans eL5 eL6

    eL8 : Deriv (atomic (eqn (ap1 (Comp Fst Fst) arg1) (ap2 Pair varA uA)))
    eL8 = ruleTrans eL3 eL7

    eL9 : Deriv (atomic (eqn (ap1 Fst (ap1 (Comp Fst Fst) arg1))
                              (ap1 Fst (ap2 Pair varA uA))))
    eL9 = cong1 Fst eL8

    eL10 : Deriv (atomic (eqn (ap1 Fst (ap2 Pair varA uA)) varA))
    eL10 = axFst varA uA

    eL11 : Deriv (atomic (eqn (ap1 Fst (ap1 (Comp Fst Fst) arg1)) varA))
    eL11 = ruleTrans eL9 eL10

    eL12 : Deriv (atomic (eqn (ap1 (Comp Fst (Comp Fst Fst)) arg1) varA))
    eL12 = ruleTrans eL2 eL11

    eL_full : Deriv (atomic (eqn (ap2 (Lift (Comp Fst (Comp Fst Fst))) arg1 recs) varA))
    eL_full = ruleTrans eL1 eL12

    -- Step 3: reduce (Lift Snd) at arg1, recs to orig.
    eR1 : Deriv (atomic (eqn (ap2 (Lift Snd) arg1 recs) (ap1 Snd arg1)))
    eR1 = axLift Snd arg1 recs

    eR2 : Deriv (atomic (eqn (ap1 Snd arg1) orig))
    eR2 = axSnd p orig

    eR_full : Deriv (atomic (eqn (ap2 (Lift Snd) arg1 recs) orig))
    eR_full = ruleTrans eR1 eR2

    -- Combine via congL/congR.
    e1 : Deriv (atomic (eqn
      (ap2 TreeEq (ap2 (Lift (Comp Fst (Comp Fst Fst))) arg1 recs)
                  (ap2 (Lift Snd) arg1 recs))
      (ap2 TreeEq varA (ap2 (Lift Snd) arg1 recs))))
    e1 = congL TreeEq (ap2 (Lift Snd) arg1 recs) eL_full

    e2 : Deriv (atomic (eqn
      (ap2 TreeEq varA (ap2 (Lift Snd) arg1 recs))
      (ap2 TreeEq varA orig)))
    e2 = congR TreeEq varA eR_full

  in ruleTrans r1 (ruleTrans e1 e2)

-- checkEqAt2B : symmetric for varB.

checkEqAt2B : (varCodeA uA varCodeB uB orig recs : Term) ->
  Deriv (atomic (eqn
    (ap2 checkEqSubT2B
      (ap2 Pair (ap2 Pair (ap2 Pair varCodeA uA) (ap2 Pair varCodeB uB)) orig)
      recs)
    (ap2 TreeEq varCodeB orig)))
checkEqAt2B varA uA varB uB orig recs =
  let
    p : Term
    p = ap2 Pair (ap2 Pair varA uA) (ap2 Pair varB uB)
    arg1 : Term
    arg1 = ap2 Pair p orig

    r1 : Deriv (atomic (eqn (ap2 checkEqSubT2B arg1 recs)
                            (ap2 TreeEq
                              (ap2 (Lift (Comp Fst (Comp Snd Fst))) arg1 recs)
                              (ap2 (Lift Snd) arg1 recs))))
    r1 = axFan (Lift (Comp Fst (Comp Snd Fst))) (Lift Snd) TreeEq arg1 recs

    -- ap1 (Comp Fst (Comp Snd Fst)) arg1 = Fst (Snd (Fst arg1)) = varB.
    eL1 : Deriv (atomic (eqn (ap2 (Lift (Comp Fst (Comp Snd Fst))) arg1 recs)
                              (ap1 (Comp Fst (Comp Snd Fst)) arg1)))
    eL1 = axLift (Comp Fst (Comp Snd Fst)) arg1 recs

    eL2 : Deriv (atomic (eqn (ap1 (Comp Fst (Comp Snd Fst)) arg1)
                              (ap1 Fst (ap1 (Comp Snd Fst) arg1))))
    eL2 = axComp Fst (Comp Snd Fst) arg1

    eL3 : Deriv (atomic (eqn (ap1 (Comp Snd Fst) arg1)
                              (ap1 Snd (ap1 Fst arg1))))
    eL3 = axComp Snd Fst arg1

    eL4 : Deriv (atomic (eqn (ap1 Fst arg1) p))
    eL4 = axFst p orig

    eL5 : Deriv (atomic (eqn (ap1 Snd (ap1 Fst arg1)) (ap1 Snd p)))
    eL5 = cong1 Snd eL4

    eL6 : Deriv (atomic (eqn (ap1 Snd p) (ap2 Pair varB uB)))
    eL6 = axSnd (ap2 Pair varA uA) (ap2 Pair varB uB)

    eL7 : Deriv (atomic (eqn (ap1 Snd (ap1 Fst arg1)) (ap2 Pair varB uB)))
    eL7 = ruleTrans eL5 eL6

    eL8 : Deriv (atomic (eqn (ap1 (Comp Snd Fst) arg1) (ap2 Pair varB uB)))
    eL8 = ruleTrans eL3 eL7

    eL9 : Deriv (atomic (eqn (ap1 Fst (ap1 (Comp Snd Fst) arg1))
                              (ap1 Fst (ap2 Pair varB uB))))
    eL9 = cong1 Fst eL8

    eL10 : Deriv (atomic (eqn (ap1 Fst (ap2 Pair varB uB)) varB))
    eL10 = axFst varB uB

    eL11 : Deriv (atomic (eqn (ap1 Fst (ap1 (Comp Snd Fst) arg1)) varB))
    eL11 = ruleTrans eL9 eL10

    eL12 : Deriv (atomic (eqn (ap1 (Comp Fst (Comp Snd Fst)) arg1) varB))
    eL12 = ruleTrans eL2 eL11

    eL_full : Deriv (atomic (eqn (ap2 (Lift (Comp Fst (Comp Snd Fst))) arg1 recs) varB))
    eL_full = ruleTrans eL1 eL12

    eR_full : Deriv (atomic (eqn (ap2 (Lift Snd) arg1 recs) orig))
    eR_full = ruleTrans (axLift Snd arg1 recs) (axSnd p orig)

    e1 : Deriv (atomic (eqn
      (ap2 TreeEq (ap2 (Lift (Comp Fst (Comp Snd Fst))) arg1 recs)
                  (ap2 (Lift Snd) arg1 recs))
      (ap2 TreeEq varB (ap2 (Lift Snd) arg1 recs))))
    e1 = congL TreeEq (ap2 (Lift Snd) arg1 recs) eL_full

    e2 : Deriv (atomic (eqn
      (ap2 TreeEq varB (ap2 (Lift Snd) arg1 recs))
      (ap2 TreeEq varB orig)))
    e2 = congR TreeEq varB eR_full

  in ruleTrans r1 (ruleTrans e1 e2)

-- extractUA_at: ap2 (Lift (Comp Snd (Comp Fst Fst))) arg1 recs = uA.

extractUA_at : (varCodeA uA varCodeB uB orig recs : Term) ->
  Deriv (atomic (eqn
    (ap2 (Lift (Comp Snd (Comp Fst Fst)))
      (ap2 Pair (ap2 Pair (ap2 Pair varCodeA uA) (ap2 Pair varCodeB uB)) orig)
      recs)
    uA))
extractUA_at varA uA varB uB orig recs =
  let
    p : Term
    p = ap2 Pair (ap2 Pair varA uA) (ap2 Pair varB uB)
    arg1 : Term
    arg1 = ap2 Pair p orig

    r1 : Deriv (atomic (eqn (ap2 (Lift (Comp Snd (Comp Fst Fst))) arg1 recs)
                            (ap1 (Comp Snd (Comp Fst Fst)) arg1)))
    r1 = axLift (Comp Snd (Comp Fst Fst)) arg1 recs

    r2 : Deriv (atomic (eqn (ap1 (Comp Snd (Comp Fst Fst)) arg1)
                             (ap1 Snd (ap1 (Comp Fst Fst) arg1))))
    r2 = axComp Snd (Comp Fst Fst) arg1

    r3 : Deriv (atomic (eqn (ap1 (Comp Fst Fst) arg1)
                             (ap1 Fst (ap1 Fst arg1))))
    r3 = axComp Fst Fst arg1

    r4 : Deriv (atomic (eqn (ap1 Fst arg1) p))
    r4 = axFst p orig

    r5 : Deriv (atomic (eqn (ap1 Fst (ap1 Fst arg1)) (ap1 Fst p)))
    r5 = cong1 Fst r4

    r6 : Deriv (atomic (eqn (ap1 Fst p) (ap2 Pair varA uA)))
    r6 = axFst (ap2 Pair varA uA) (ap2 Pair varB uB)

    r7 : Deriv (atomic (eqn (ap1 Fst (ap1 Fst arg1)) (ap2 Pair varA uA)))
    r7 = ruleTrans r5 r6

    r8 : Deriv (atomic (eqn (ap1 (Comp Fst Fst) arg1) (ap2 Pair varA uA)))
    r8 = ruleTrans r3 r7

    r9 : Deriv (atomic (eqn (ap1 Snd (ap1 (Comp Fst Fst) arg1))
                             (ap1 Snd (ap2 Pair varA uA))))
    r9 = cong1 Snd r8

    r10 : Deriv (atomic (eqn (ap1 Snd (ap2 Pair varA uA)) uA))
    r10 = axSnd varA uA

    r11 : Deriv (atomic (eqn (ap1 Snd (ap1 (Comp Fst Fst) arg1)) uA))
    r11 = ruleTrans r9 r10

    r12 : Deriv (atomic (eqn (ap1 (Comp Snd (Comp Fst Fst)) arg1) uA))
    r12 = ruleTrans r2 r11

  in ruleTrans r1 r12

-- extractUB_at: ap2 (Lift (Comp Snd (Comp Snd Fst))) arg1 recs = uB.

extractUB_at : (varCodeA uA varCodeB uB orig recs : Term) ->
  Deriv (atomic (eqn
    (ap2 (Lift (Comp Snd (Comp Snd Fst)))
      (ap2 Pair (ap2 Pair (ap2 Pair varCodeA uA) (ap2 Pair varCodeB uB)) orig)
      recs)
    uB))
extractUB_at varA uA varB uB orig recs =
  let
    p : Term
    p = ap2 Pair (ap2 Pair varA uA) (ap2 Pair varB uB)
    arg1 : Term
    arg1 = ap2 Pair p orig

    r1 : Deriv (atomic (eqn (ap2 (Lift (Comp Snd (Comp Snd Fst))) arg1 recs)
                            (ap1 (Comp Snd (Comp Snd Fst)) arg1)))
    r1 = axLift (Comp Snd (Comp Snd Fst)) arg1 recs

    r2 : Deriv (atomic (eqn (ap1 (Comp Snd (Comp Snd Fst)) arg1)
                             (ap1 Snd (ap1 (Comp Snd Fst) arg1))))
    r2 = axComp Snd (Comp Snd Fst) arg1

    r3 : Deriv (atomic (eqn (ap1 (Comp Snd Fst) arg1)
                             (ap1 Snd (ap1 Fst arg1))))
    r3 = axComp Snd Fst arg1

    r4 : Deriv (atomic (eqn (ap1 Fst arg1) p))
    r4 = axFst p orig

    r5 : Deriv (atomic (eqn (ap1 Snd (ap1 Fst arg1)) (ap1 Snd p)))
    r5 = cong1 Snd r4

    r6 : Deriv (atomic (eqn (ap1 Snd p) (ap2 Pair varB uB)))
    r6 = axSnd (ap2 Pair varA uA) (ap2 Pair varB uB)

    r7 : Deriv (atomic (eqn (ap1 Snd (ap1 Fst arg1)) (ap2 Pair varB uB)))
    r7 = ruleTrans r5 r6

    r8 : Deriv (atomic (eqn (ap1 (Comp Snd Fst) arg1) (ap2 Pair varB uB)))
    r8 = ruleTrans r3 r7

    r9 : Deriv (atomic (eqn (ap1 Snd (ap1 (Comp Snd Fst) arg1))
                             (ap1 Snd (ap2 Pair varB uB))))
    r9 = cong1 Snd r8

    r10 : Deriv (atomic (eqn (ap1 Snd (ap2 Pair varB uB)) uB))
    r10 = axSnd varB uB

    r11 : Deriv (atomic (eqn (ap1 Snd (ap1 (Comp Snd Fst) arg1)) uB))
    r11 = ruleTrans r9 r10

    r12 : Deriv (atomic (eqn (ap1 (Comp Snd (Comp Snd Fst)) arg1) uB))
    r12 = ruleTrans r2 r11

  in ruleTrans r1 r12

-- contInner_at: contInner reduces to Pair uB recs.

contInner2_at : (varCodeA uA varCodeB uB orig recs : Term) ->
  Deriv (atomic (eqn
    (ap2 contInner2
      (ap2 Pair (ap2 Pair (ap2 Pair varCodeA uA) (ap2 Pair varCodeB uB)) orig)
      recs)
    (ap2 Pair uB recs)))
contInner2_at varA uA varB uB orig recs =
  let
    p : Term
    p = ap2 Pair (ap2 Pair varA uA) (ap2 Pair varB uB)
    arg1 : Term
    arg1 = ap2 Pair p orig

    r1 : Deriv (atomic (eqn (ap2 contInner2 arg1 recs)
                            (ap2 Pair (ap2 (Lift (Comp Snd (Comp Snd Fst))) arg1 recs)
                                       (ap2 (Post Snd Pair) arg1 recs))))
    r1 = axFan (Lift (Comp Snd (Comp Snd Fst))) (Post Snd Pair) Pair arg1 recs

    rL : Deriv (atomic (eqn (ap2 (Lift (Comp Snd (Comp Snd Fst))) arg1 recs) uB))
    rL = extractUB_at varA uA varB uB orig recs

    rR : Deriv (atomic (eqn (ap2 (Post Snd Pair) arg1 recs) recs))
    rR = ruleTrans (axPost Snd Pair arg1 recs) (axSnd arg1 recs)

    e1 : Deriv (atomic (eqn (ap2 Pair (ap2 (Lift (Comp Snd (Comp Snd Fst))) arg1 recs)
                                       (ap2 (Post Snd Pair) arg1 recs))
                             (ap2 Pair uB (ap2 (Post Snd Pair) arg1 recs))))
    e1 = congL Pair (ap2 (Post Snd Pair) arg1 recs) rL

    e2 : Deriv (atomic (eqn (ap2 Pair uB (ap2 (Post Snd Pair) arg1 recs))
                             (ap2 Pair uB recs)))
    e2 = congR Pair uB rR

  in ruleTrans r1 (ruleTrans e1 e2)

-- innerStep2_at: innerStep2 reduces to IfLf testB (Pair uB recs).

innerStep2_at : (varCodeA uA varCodeB uB orig recs : Term) ->
  Deriv (atomic (eqn
    (ap2 innerStep2
      (ap2 Pair (ap2 Pair (ap2 Pair varCodeA uA) (ap2 Pair varCodeB uB)) orig)
      recs)
    (ap2 IfLf (ap2 TreeEq varCodeB orig) (ap2 Pair uB recs))))
innerStep2_at varA uA varB uB orig recs =
  let
    p : Term
    p = ap2 Pair (ap2 Pair varA uA) (ap2 Pair varB uB)
    arg1 : Term
    arg1 = ap2 Pair p orig

    r1 : Deriv (atomic (eqn (ap2 innerStep2 arg1 recs)
                            (ap2 IfLf (ap2 checkEqSubT2B arg1 recs)
                                       (ap2 contInner2 arg1 recs))))
    r1 = axFan checkEqSubT2B contInner2 IfLf arg1 recs

    rChk : Deriv (atomic (eqn (ap2 checkEqSubT2B arg1 recs)
                               (ap2 TreeEq varB orig)))
    rChk = checkEqAt2B varA uA varB uB orig recs

    rCnt : Deriv (atomic (eqn (ap2 contInner2 arg1 recs)
                               (ap2 Pair uB recs)))
    rCnt = contInner2_at varA uA varB uB orig recs

    e1 : Deriv (atomic (eqn (ap2 IfLf (ap2 checkEqSubT2B arg1 recs)
                                       (ap2 contInner2 arg1 recs))
                             (ap2 IfLf (ap2 TreeEq varB orig)
                                       (ap2 contInner2 arg1 recs))))
    e1 = congL IfLf (ap2 contInner2 arg1 recs) rChk

    e2 : Deriv (atomic (eqn (ap2 IfLf (ap2 TreeEq varB orig)
                                       (ap2 contInner2 arg1 recs))
                             (ap2 IfLf (ap2 TreeEq varB orig)
                                       (ap2 Pair uB recs))))
    e2 = congR IfLf (ap2 TreeEq varB orig) rCnt

  in ruleTrans r1 (ruleTrans e1 e2)

-- contOuter_at: contOuter reduces to Pair uA (innerStep_output).

contOuter2_at : (varCodeA uA varCodeB uB orig recs : Term) ->
  Deriv (atomic (eqn
    (ap2 contOuter2
      (ap2 Pair (ap2 Pair (ap2 Pair varCodeA uA) (ap2 Pair varCodeB uB)) orig)
      recs)
    (ap2 Pair uA
      (ap2 IfLf (ap2 TreeEq varCodeB orig) (ap2 Pair uB recs)))))
contOuter2_at varA uA varB uB orig recs =
  let
    p : Term
    p = ap2 Pair (ap2 Pair varA uA) (ap2 Pair varB uB)
    arg1 : Term
    arg1 = ap2 Pair p orig

    r1 : Deriv (atomic (eqn (ap2 contOuter2 arg1 recs)
                            (ap2 Pair (ap2 (Lift (Comp Snd (Comp Fst Fst))) arg1 recs)
                                       (ap2 innerStep2 arg1 recs))))
    r1 = axFan (Lift (Comp Snd (Comp Fst Fst))) innerStep2 Pair arg1 recs

    rUA : Deriv (atomic (eqn (ap2 (Lift (Comp Snd (Comp Fst Fst))) arg1 recs) uA))
    rUA = extractUA_at varA uA varB uB orig recs

    rIS : Deriv (atomic (eqn (ap2 innerStep2 arg1 recs)
                              (ap2 IfLf (ap2 TreeEq varB orig) (ap2 Pair uB recs))))
    rIS = innerStep2_at varA uA varB uB orig recs

    e1 : Deriv (atomic (eqn (ap2 Pair (ap2 (Lift (Comp Snd (Comp Fst Fst))) arg1 recs)
                                       (ap2 innerStep2 arg1 recs))
                             (ap2 Pair uA (ap2 innerStep2 arg1 recs))))
    e1 = congL Pair (ap2 innerStep2 arg1 recs) rUA

    e2 : Deriv (atomic (eqn (ap2 Pair uA (ap2 innerStep2 arg1 recs))
                             (ap2 Pair uA (ap2 IfLf (ap2 TreeEq varB orig)
                                                     (ap2 Pair uB recs)))))
    e2 = congR Pair uA rIS

  in ruleTrans r1 (ruleTrans e1 e2)

------------------------------------------------------------------------
-- Main lemma: subTDef_term2.

subTDef_term2 : (nA nB : Nat) (uA uB : Term) (codeP : Term) -> IsValue codeP ->
  Deriv (atomic (eqn
    (ap2 subT2 (ap2 Pair (ap2 Pair (code (var nA)) uA)
                          (ap2 Pair (code (var nB)) uB))
                codeP)
    (codedSubstT2 uA uB (code (var nA)) (code (var nB)) codeP)))
subTDef_term2 nA nB uA uB .O                  valO                 =
  axRecPLf stepSubT2
    (ap2 Pair (ap2 Pair (code (var nA)) uA)
              (ap2 Pair (code (var nB)) uB))
subTDef_term2 nA nB uA uB (ap2 Pair a b)     (valNd .a .b va vb)   =
  ruleTrans s1 (ruleTrans s2 (ruleTrans s6 s8))
  where
    varA : Term
    varA = code (var nA)

    varB : Term
    varB = code (var nB)

    varA_isValue : IsValue varA
    varA_isValue = code_isValue (var nA)

    varB_isValue : IsValue varB
    varB_isValue = code_isValue (var nB)

    p : Term
    p = ap2 Pair (ap2 Pair varA uA) (ap2 Pair varB uB)

    orig : Term
    orig = ap2 Pair a b

    orig_isValue : IsValue orig
    orig_isValue = valNd a b va vb

    arg1 : Term
    arg1 = ap2 Pair p orig

    varCodeA : Term
    varCodeA = code (var nA)

    varCodeB : Term
    varCodeB = code (var nB)

    recA : Term
    recA = ap2 (RecP stepSubT2) p a

    recB : Term
    recB = ap2 (RecP stepSubT2) p b

    recs : Term
    recs = ap2 Pair recA recB

    treeEqA : Bool
    treeEqA = treeEq varCodeA (ap2 Pair a b)

    treeEqB : Bool
    treeEqB = treeEq varCodeB (ap2 Pair a b)

    ihA : Deriv (atomic (eqn recA (codedSubstT2 uA uB varCodeA varCodeB a)))
    ihA = subTDef_term2 nA nB uA uB a va

    ihB : Deriv (atomic (eqn recB (codedSubstT2 uA uB varCodeA varCodeB b)))
    ihB = subTDef_term2 nA nB uA uB b vb

    s1 : Deriv (atomic (eqn (ap2 subT2 p orig) (ap2 stepSubT2 arg1 recs)))
    s1 = axRecPNd stepSubT2 p a b

    s2 : Deriv (atomic (eqn (ap2 stepSubT2 arg1 recs)
                            (ap2 IfLf (ap2 checkEqSubT2A arg1 recs)
                                       (ap2 contOuter2 arg1 recs))))
    s2 = axFan checkEqSubT2A contOuter2 IfLf arg1 recs

    chkA : Deriv (atomic (eqn (ap2 checkEqSubT2A arg1 recs)
                               (ap2 TreeEq varA orig)))
    chkA = checkEqAt2A varA uA varB uB orig recs

    chkA_bool : Deriv (atomic (eqn (ap2 checkEqSubT2A arg1 recs)
                                    (boolCase treeEqA O falseT)))
    chkA_bool = ruleTrans chkA (treeEqRed varCodeA varA_isValue (ap2 Pair a b) orig_isValue)

    cnt : Deriv (atomic (eqn (ap2 contOuter2 arg1 recs)
                              (ap2 Pair uA (ap2 IfLf (ap2 TreeEq varB orig)
                                                      (ap2 Pair uB recs)))))
    cnt = contOuter2_at varA uA varB uB orig recs

    chkB : Deriv (atomic (eqn (ap2 TreeEq varB orig)
                               (boolCase treeEqB O falseT)))
    chkB = treeEqRed varCodeB varB_isValue (ap2 Pair a b) orig_isValue

    cnt_bool : Deriv (atomic (eqn (ap2 contOuter2 arg1 recs)
                                   (ap2 Pair uA
                                     (ap2 IfLf (boolCase treeEqB O falseT)
                                                (ap2 Pair uB recs)))))
    cnt_bool = ruleTrans cnt (congR Pair uA
                                (congL IfLf (ap2 Pair uB recs) chkB))

    s6 : Deriv (atomic (eqn (ap2 IfLf (ap2 checkEqSubT2A arg1 recs)
                                       (ap2 contOuter2 arg1 recs))
                             (ap2 IfLf (boolCase treeEqA O falseT)
                                       (ap2 Pair uA
                                         (ap2 IfLf (boolCase treeEqB O falseT)
                                                    (ap2 Pair uB recs))))))
    s6 = ruleTrans (congL IfLf (ap2 contOuter2 arg1 recs) chkA_bool)
                   (congR IfLf (boolCase treeEqA O falseT) cnt_bool)

    innerCase : Deriv (atomic (eqn
      (ap2 IfLf (boolCase treeEqB O falseT) (ap2 Pair uB recs))
      (boolCase treeEqB uB recs)))
    innerCase = ifLfDispatch treeEqB uB recs

    finishInner : (b' : Bool) ->
      Deriv (atomic (eqn (boolCase b' uB recs)
                          (boolCase b' uB
                            (ap2 Pair (codedSubstT2 uA uB varCodeA varCodeB a)
                                       (codedSubstT2 uA uB varCodeA varCodeB b)))))
    finishInner true  = axRefl uB
    finishInner false =
      ruleTrans (congL Pair recB ihA)
                (congR Pair (codedSubstT2 uA uB varCodeA varCodeB a) ihB)

    innerFinal : Deriv (atomic (eqn
      (ap2 IfLf (boolCase treeEqB O falseT) (ap2 Pair uB recs))
      (boolCase treeEqB uB
        (ap2 Pair (codedSubstT2 uA uB varCodeA varCodeB a)
                   (codedSubstT2 uA uB varCodeA varCodeB b)))))
    innerFinal = ruleTrans innerCase (finishInner treeEqB)

    pairUA_inner : Deriv (atomic (eqn
      (ap2 Pair uA
        (ap2 IfLf (boolCase treeEqB O falseT) (ap2 Pair uB recs)))
      (ap2 Pair uA
        (boolCase treeEqB uB
          (ap2 Pair (codedSubstT2 uA uB varCodeA varCodeB a)
                     (codedSubstT2 uA uB varCodeA varCodeB b))))))
    pairUA_inner = congR Pair uA innerFinal

    outerDispatch : Deriv (atomic (eqn
      (ap2 IfLf (boolCase treeEqA O falseT)
        (ap2 Pair uA
          (boolCase treeEqB uB
            (ap2 Pair (codedSubstT2 uA uB varCodeA varCodeB a)
                       (codedSubstT2 uA uB varCodeA varCodeB b)))))
      (boolCase treeEqA uA
        (boolCase treeEqB uB
          (ap2 Pair (codedSubstT2 uA uB varCodeA varCodeB a)
                     (codedSubstT2 uA uB varCodeA varCodeB b))))))
    outerDispatch = ifLfDispatch treeEqA uA
                      (boolCase treeEqB uB
                        (ap2 Pair (codedSubstT2 uA uB varCodeA varCodeB a)
                                   (codedSubstT2 uA uB varCodeA varCodeB b)))

    s8 : Deriv (atomic (eqn
      (ap2 IfLf (boolCase treeEqA O falseT)
        (ap2 Pair uA
          (ap2 IfLf (boolCase treeEqB O falseT)
                     (ap2 Pair uB recs))))
      (codedSubstT2 uA uB varCodeA varCodeB (ap2 Pair a b))))
    s8 = ruleTrans (congR IfLf (boolCase treeEqA O falseT) pairUA_inner)
                   outerDispatch

------------------------------------------------------------------------
-- subTDef2 : wrapper around subTDef_term2 with IsValue threaded.

subTDef2 : (nA nB : Nat) (uA uB codeP : Term) -> IsValue codeP ->
  Deriv (atomic (eqn
    (ap2 subT2 (ap2 Pair (ap2 Pair (code (var nA)) uA)
                          (ap2 Pair (code (var nB)) uB))
                codeP)
    (codedSubst2 uA uB (code (var nA)) (code (var nB)) codeP)))
subTDef2 nA nB uA uB codeP cP = subTDef_term2 nA nB uA uB codeP cP
