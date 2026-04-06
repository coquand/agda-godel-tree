{-# OPTIONS --safe --without-K --exact-split #-}

-- Nelson Experiment A: the system can verify its own axRefl case.
--
-- Proves inside Deriv that thFunTFor applied to an axRefl encoding
-- returns Pair(x, x) — the code of the reflexivity equation.

module Guard.NelsonAxRefl where

open import Guard.Base
open import Guard.Term
open import Guard.Step
open import Guard.StepReduce
open import Guard.ThFunTForDefs
open import Guard.ThFunTForCases0
open import Guard.ThFunTForCases1
open import Guard.ThFunTForCases2
open import Guard.ThFunTForCases3
open import Guard.ThFunTFor
open import Guard.GodelII using (treeEqSelf)

private
  poo : Term ; poo = ap2 Pair O O
  v0 : Term ; v0 = var zero

  n0  : Nat ; n0  = zero
  n1  : Nat ; n1  = suc n0
  n2  : Nat ; n2  = suc n1
  n3  : Nat ; n3  = suc n2
  n4  : Nat ; n4  = suc n3
  n5  : Nat ; n5  = suc n4
  n6  : Nat ; n6  = suc n5
  n7  : Nat ; n7  = suc n6
  n8  : Nat ; n8  = suc n7
  n9  : Nat ; n9  = suc n8
  n10 : Nat ; n10 = suc n9
  n11 : Nat ; n11 = suc n10
  n12 : Nat ; n12 = suc n11
  n13 : Nat ; n13 = suc n12
  n14 : Nat ; n14 = suc n13
  n15 : Nat ; n15 = suc n14
  n16 : Nat ; n16 = suc n15
  n17 : Nat ; n17 = suc n16

  tag17T : Term ; tag17T = reify (natCode n17)

  -- The encoding of axRefl(x): Pair(tag17, Pair(x, O))
  origR : Term ; origR = ap2 Pair tag17T (ap2 Pair v0 O)
  recsR : Term ; recsR = ap2 Pair (ap1 thFunTFor tag17T) (ap1 thFunTFor (ap2 Pair v0 O))

  ------------------------------------------------------------------------
  -- TreeEq comparison: natCode 17 vs natCode k
  --
  -- For k < 17: TreeEq(reify(natCode 17), reify(natCode k)) = Pair(O,O)
  -- For k = 17: TreeEq(reify(natCode 17), reify(natCode 17)) = O

------------------------------------------------------------------------
-- Exported: natCode comparison helpers

natAdd : Nat -> Nat -> Nat
natAdd zero m = m
natAdd (suc n) m = suc (natAdd n m)

natCodeNeq : (k n : Nat) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap2 TreeEq (reify (natCode (natAdd n (suc k)))) (reify (natCode n))) poo)
natCodeNeq k zero = axTreeEqNL O (reify (natCode k))
natCodeNeq k (suc n) =
  ruleTrans (axTreeEqNN O (reify (natCode (natAdd n (suc k)))) O (reify (natCode n)))
  (ruleTrans (congL IfLf (ap2 Pair (ap2 TreeEq (reify (natCode (natAdd n (suc k)))) (reify (natCode n))) poo) axTreeEqLL)
  (ruleTrans (axIfLfL (ap2 TreeEq (reify (natCode (natAdd n (suc k)))) (reify (natCode n))) poo)
             (natCodeNeq k n)))

private
  -- Fst(orig) = tag17T
  fstOrig : {hyp : Equation} -> Deriv hyp (eqn (ap1 Fst origR) tag17T)
  fstOrig = axFst tag17T (ap2 Pair v0 O)

  ------------------------------------------------------------------------
  -- Branch dispatch helpers

  -- Tag check reduction: from tagCheck to TreeEq(Fst(orig), constant)
  tagCheckRed : (k : Nat) -> {hyp : Equation} ->
    Deriv hyp (eqn (ap2 (tagCheck k) origR recsR)
                   (ap2 TreeEq (ap1 Fst origR) (reify (natCode k))))
  tagCheckRed k =
    ruleTrans (axFan (Lift Fst) (Lift (KT (reify (natCode k)))) TreeEq origR recsR)
    (ruleTrans (congL TreeEq (ap2 (Lift (KT (reify (natCode k)))) origR recsR) (axLift Fst origR recsR))
    (congR TreeEq (ap1 Fst origR)
      (ruleTrans (axLift (KT (reify (natCode k))) origR recsR) (axKT (reify (natCode k)) origR))))

  -- Substitute Fst(orig) = tag17T in the TreeEq comparison
  tagNeq : (k : Nat) -> {hyp : Equation} ->
    Deriv hyp (eqn (ap2 TreeEq (reify (natCode n17)) (reify (natCode k))) poo) ->
    Deriv hyp (eqn (ap2 (tagCheck k) origR recsR) poo)
  tagNeq k cmp = ruleTrans (tagCheckRed k) (ruleTrans (congL TreeEq (reify (natCode k)) fstOrig) cmp)

  tagEq : {hyp : Equation} ->
    Deriv hyp (eqn (ap2 (tagCheck n17) origR recsR) O)
  tagEq = ruleTrans (tagCheckRed n17) (ruleTrans (congL TreeEq (reify (natCode n17)) fstOrig) (treeEqSelf tag17T))

  ------------------------------------------------------------------------
  -- Branch miss: if tag check gives Pair(O,O), fall through

  bMiss : (k : Nat) (caseF rest : Fun2) -> {hyp : Equation} ->
    Deriv hyp (eqn (ap2 (tagCheck k) origR recsR) poo) ->
    Deriv hyp (eqn (ap2 (branch (tagCheck k) caseF rest) origR recsR)
                   (ap2 rest origR recsR))
  bMiss k caseF rest chk =
    ruleTrans (axFan (tagCheck k) (Fan caseF rest Pair) IfLf origR recsR)
    (ruleTrans (congL IfLf (ap2 (Fan caseF rest Pair) origR recsR) chk)
    (ruleTrans (congR IfLf poo (axFan caseF rest Pair origR recsR))
               (axIfLfN O O (ap2 caseF origR recsR) (ap2 rest origR recsR))))

  -- Branch hit: if tag check gives O, take the case
  bHit : (k : Nat) (caseF rest : Fun2) -> {hyp : Equation} ->
    Deriv hyp (eqn (ap2 (tagCheck k) origR recsR) O) ->
    Deriv hyp (eqn (ap2 (branch (tagCheck k) caseF rest) origR recsR)
                   (ap2 caseF origR recsR))
  bHit k caseF rest chk =
    ruleTrans (axFan (tagCheck k) (Fan caseF rest Pair) IfLf origR recsR)
    (ruleTrans (congL IfLf (ap2 (Fan caseF rest Pair) origR recsR) chk)
    (ruleTrans (congR IfLf O (axFan caseF rest Pair origR recsR))
               (axIfLfL (ap2 caseF origR recsR) (ap2 rest origR recsR))))

  ------------------------------------------------------------------------
  -- Fall through branches 0-16 to reach case17
  --
  -- natCode 17 = suc(suc(...(suc zero)...)) with 17 sucs.
  -- For each k < 17: natCodeNeq (16-k) k gives the TreeEq comparison.
  -- natCode 17 = natCode(suc(natAdd (16-k) k)) = natCode(suc(16)) = natCode 17.
  -- So TreeEq(reify(natCode 17), reify(natCode k)) = Pair(O,O).

  -- TreeEq(reify(natCode 17), reify(natCode k)) = Pair(O,O) for k=0..16
  -- Using natCodeNeq: natCodeNeq diff k gives natCode(natAdd k (suc diff)) vs natCode k
  -- For tag17 vs k: 17 = natAdd k (suc (16 - k)), so diff = 16 - k.
  neq0  : {h : Equation} -> Deriv h (eqn (ap2 TreeEq tag17T (reify (natCode n0))) poo)
  neq0  = natCodeNeq n16 n0
  neq1  : {h : Equation} -> Deriv h (eqn (ap2 TreeEq tag17T (reify (natCode n1))) poo)
  neq1  = natCodeNeq n15 n1
  neq2  : {h : Equation} -> Deriv h (eqn (ap2 TreeEq tag17T (reify (natCode n2))) poo)
  neq2  = natCodeNeq n14 n2
  neq3  : {h : Equation} -> Deriv h (eqn (ap2 TreeEq tag17T (reify (natCode n3))) poo)
  neq3  = natCodeNeq n13 n3
  neq4  : {h : Equation} -> Deriv h (eqn (ap2 TreeEq tag17T (reify (natCode n4))) poo)
  neq4  = natCodeNeq n12 n4
  neq5  : {h : Equation} -> Deriv h (eqn (ap2 TreeEq tag17T (reify (natCode n5))) poo)
  neq5  = natCodeNeq n11 n5
  neq6  : {h : Equation} -> Deriv h (eqn (ap2 TreeEq tag17T (reify (natCode n6))) poo)
  neq6  = natCodeNeq n10 n6
  neq7  : {h : Equation} -> Deriv h (eqn (ap2 TreeEq tag17T (reify (natCode n7))) poo)
  neq7  = natCodeNeq n9 n7
  neq8  : {h : Equation} -> Deriv h (eqn (ap2 TreeEq tag17T (reify (natCode n8))) poo)
  neq8  = natCodeNeq n8 n8
  neq9  : {h : Equation} -> Deriv h (eqn (ap2 TreeEq tag17T (reify (natCode n9))) poo)
  neq9  = natCodeNeq n7 n9
  neq10 : {h : Equation} -> Deriv h (eqn (ap2 TreeEq tag17T (reify (natCode n10))) poo)
  neq10 = natCodeNeq n6 n10
  neq11 : {h : Equation} -> Deriv h (eqn (ap2 TreeEq tag17T (reify (natCode n11))) poo)
  neq11 = natCodeNeq n5 n11
  neq12 : {h : Equation} -> Deriv h (eqn (ap2 TreeEq tag17T (reify (natCode n12))) poo)
  neq12 = natCodeNeq n4 n12
  neq13 : {h : Equation} -> Deriv h (eqn (ap2 TreeEq tag17T (reify (natCode n13))) poo)
  neq13 = natCodeNeq n3 n13
  neq14 : {h : Equation} -> Deriv h (eqn (ap2 TreeEq tag17T (reify (natCode n14))) poo)
  neq14 = natCodeNeq n2 n14
  neq15 : {h : Equation} -> Deriv h (eqn (ap2 TreeEq tag17T (reify (natCode n15))) poo)
  neq15 = natCodeNeq n1 n15
  neq16 : {h : Equation} -> Deriv h (eqn (ap2 TreeEq tag17T (reify (natCode n16))) poo)
  neq16 = natCodeNeq n0 n16

  miss0  : {h : Equation} -> Deriv h (eqn (ap2 ndDispatch origR recsR) (ap2 ndT1 origR recsR))
  miss0  = bMiss n0 case0 ndT1 (tagNeq n0 neq0)

  miss1  : {h : Equation} -> Deriv h (eqn (ap2 ndT1 origR recsR) (ap2 ndT2 origR recsR))
  miss1  = bMiss n1 case1 ndT2 (tagNeq n1 neq1)

  miss2  : {h : Equation} -> Deriv h (eqn (ap2 ndT2 origR recsR) (ap2 ndT3 origR recsR))
  miss2  = bMiss n2 case2 ndT3 (tagNeq n2 neq2)

  miss3  : {h : Equation} -> Deriv h (eqn (ap2 ndT3 origR recsR) (ap2 ndT4 origR recsR))
  miss3  = bMiss n3 case3 ndT4 (tagNeq n3 neq3)

  miss4  : {h : Equation} -> Deriv h (eqn (ap2 ndT4 origR recsR) (ap2 ndT5 origR recsR))
  miss4  = bMiss n4 case4 ndT5 (tagNeq n4 neq4)

  miss5  : {h : Equation} -> Deriv h (eqn (ap2 ndT5 origR recsR) (ap2 ndT6 origR recsR))
  miss5  = bMiss n5 case5 ndT6 (tagNeq n5 neq5)

  miss6  : {h : Equation} -> Deriv h (eqn (ap2 ndT6 origR recsR) (ap2 ndT7 origR recsR))
  miss6  = bMiss n6 case6 ndT7 (tagNeq n6 neq6)

  miss7  : {h : Equation} -> Deriv h (eqn (ap2 ndT7 origR recsR) (ap2 ndT8 origR recsR))
  miss7  = bMiss n7 case7 ndT8 (tagNeq n7 neq7)

  miss8  : {h : Equation} -> Deriv h (eqn (ap2 ndT8 origR recsR) (ap2 ndT9 origR recsR))
  miss8  = bMiss n8 case8 ndT9 (tagNeq n8 neq8)

  miss9  : {h : Equation} -> Deriv h (eqn (ap2 ndT9 origR recsR) (ap2 ndT10 origR recsR))
  miss9  = bMiss n9 case9 ndT10 (tagNeq n9 neq9)

  miss10 : {h : Equation} -> Deriv h (eqn (ap2 ndT10 origR recsR) (ap2 ndT11 origR recsR))
  miss10 = bMiss n10 case10 ndT11 (tagNeq n10 neq10)

  miss11 : {h : Equation} -> Deriv h (eqn (ap2 ndT11 origR recsR) (ap2 ndT12 origR recsR))
  miss11 = bMiss n11 case11 ndT12 (tagNeq n11 neq11)

  miss12 : {h : Equation} -> Deriv h (eqn (ap2 ndT12 origR recsR) (ap2 ndT13 origR recsR))
  miss12 = bMiss n12 case12 ndT13 (tagNeq n12 neq12)

  miss13 : {h : Equation} -> Deriv h (eqn (ap2 ndT13 origR recsR) (ap2 ndT14 origR recsR))
  miss13 = bMiss n13 case13 ndT14 (tagNeq n13 neq13)

  miss14 : {h : Equation} -> Deriv h (eqn (ap2 ndT14 origR recsR) (ap2 ndT15 origR recsR))
  miss14 = bMiss n14 case14 ndT15 (tagNeq n14 neq14)

  miss15 : {h : Equation} -> Deriv h (eqn (ap2 ndT15 origR recsR) (ap2 ndT16 origR recsR))
  miss15 = bMiss n15 case15 ndT16 (tagNeq n15 neq15)

  miss16 : {h : Equation} -> Deriv h (eqn (ap2 ndT16 origR recsR) (ap2 ndT17 origR recsR))
  miss16 = bMiss n16 case16 ndT17 (tagNeq n16 neq16)

  -- Hit at branch 17
  hit17 : {h : Equation} -> Deriv h (eqn (ap2 ndT17 origR recsR) (ap2 case17 origR recsR))
  hit17 = bHit n17 case17 ndT18 tagEq

  -- Chain: ndDispatch -> case17
  dispatchToCase17 : {h : Equation} -> Deriv h (eqn (ap2 ndDispatch origR recsR) (ap2 case17 origR recsR))
  dispatchToCase17 = ruleTrans miss0 (ruleTrans miss1 (ruleTrans miss2 (ruleTrans miss3
    (ruleTrans miss4 (ruleTrans miss5 (ruleTrans miss6 (ruleTrans miss7
    (ruleTrans miss8 (ruleTrans miss9 (ruleTrans miss10 (ruleTrans miss11
    (ruleTrans miss12 (ruleTrans miss13 (ruleTrans miss14 (ruleTrans miss15
    (ruleTrans miss16 hit17))))))))))))))))

  ------------------------------------------------------------------------
  -- case17 reduction: Pair(Fst(Snd(orig)), Fst(Snd(orig)))
  -- = Pair(Fst(Pair(v0, O)), Fst(Pair(v0, O)))
  -- = Pair(v0, v0)

  -- case17 = mkEqF origA origA = Fan origA origA Pair
  -- origA = Lift (Comp Fst Snd)
  -- origA(origR, recsR) = Fst(Snd(origR)) = Fst(Pair(v0,O)) = v0
  origARed : {h : Equation} -> Deriv h (eqn (ap2 origA origR recsR) v0)
  origARed =
    ruleTrans (axLift (Comp Fst Snd) origR recsR)
    (ruleTrans (axComp Fst Snd origR)
    (ruleTrans (cong1 Fst (axSnd tag17T (ap2 Pair v0 O)))
               (axFst v0 O)))

  case17Red : {h : Equation} -> Deriv h (eqn (ap2 case17 origR recsR) (ap2 Pair v0 v0))
  case17Red =
    -- case17 = mkEqF origA origA = Fan origA origA Pair
    ruleTrans (axFan origA origA Pair origR recsR)
    (ruleTrans (congL Pair (ap2 origA origR recsR) origARed)
               (congR Pair v0 origARed))

  ------------------------------------------------------------------------
  -- thFunStep dispatch: from RecNd result to ndDispatch

  thFunStepToNd : {h : Equation} ->
    Deriv h (eqn (ap2 thFunStep origR recsR) (ap2 ndDispatch origR recsR))
  thFunStepToNd =
    -- thFunStep = Fan dataIsLf (Fan lfDispatch ndDispatch Pair) IfLf
    ruleTrans (axFan dataIsLf (Fan lfDispatch ndDispatch Pair) IfLf origR recsR)
    -- dataIsLf(origR, recsR) = TreeEq(Snd(origR), O)
    -- Snd(origR) = Snd(Pair(tag17T, Pair(v0, O))) = Pair(v0, O)
    -- TreeEq(Pair(v0, O), O) = Pair(O, O)
    (ruleTrans (congL IfLf (ap2 (Fan lfDispatch ndDispatch Pair) origR recsR)
      (ruleTrans (axFan (Lift Snd) (kF2 O) TreeEq origR recsR)
      (ruleTrans (congL TreeEq (ap2 (kF2 O) origR recsR) (axLift Snd origR recsR))
      (ruleTrans (congL TreeEq (ap2 (kF2 O) origR recsR) (axSnd tag17T (ap2 Pair v0 O)))
      (ruleTrans (congR TreeEq (ap2 Pair v0 O)
        (ruleTrans (axLift (KT O) origR recsR) (axKT O origR)))
      (axTreeEqNL v0 O))))))
    -- IfLf(Pair(O,O), Pair(lfDisp, ndDisp)) = ndDisp
    (ruleTrans (congR IfLf poo (axFan lfDispatch ndDispatch Pair origR recsR))
               (axIfLfN O O (ap2 lfDispatch origR recsR) (ap2 ndDispatch origR recsR))))

------------------------------------------------------------------------
-- Main theorem: thFunTFor on axRefl encoding gives Pair(x, x)
--
-- This is the internal verification: the system proves that its own
-- proof checker correctly handles the axRefl case.

nelsonAxRefl : {hyp : Equation} ->
  Deriv hyp (eqn (ap1 thFunTFor (ap2 Pair tag17T (ap2 Pair v0 O)))
                 (ap2 Pair v0 v0))
nelsonAxRefl =
  -- Step 1: RecNd unfold
  ruleTrans (axRecNd O thFunStep tag17T (ap2 Pair v0 O))
  -- Step 2: thFunStep dispatches to ndDispatch
  (ruleTrans thFunStepToNd
  -- Step 3: ndDispatch falls through to case17
  (ruleTrans dispatchToCase17
  -- Step 4: case17 gives Pair(v0, v0)
             case17Red))
