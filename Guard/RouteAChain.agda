{-# OPTIONS --safe --without-K --exact-split #-}

-- Guard.RouteAChain -- Guard 1963 BRA chain (step 1-5, p.17), Provable
-- layer, Route A transcription.
--
-- This file lifts the building blocks of Guard.RouteADf into the actual
-- chain structure from guard15.pdf p.17:
--
--   Step 1 : th(x) = j   imp   th(Dth(x)) = "th(x) = j"        [Th 13]
--   Step 2 : th(Dsub(i,i)) = "sub(i,i) = j"                     [Th 13 closed]
--   Step 3 : th(x) = j   imp   th(gx) = "th(x) = sub(i,i)"      [1, 2]
--   Step 4 : th(x) = j   imp   th(Y...) = "th(x) ≠ sub(i,i)"    [defn of j]
--   Step 5 : th(x) = j   imp   th(combined) = "0 = 1"           [3, 4]
--
-- We build each step as a Provable implication and glue via hypSyll' /
-- mp / axEqCong* .  The encoding used throughout is the "whole-
-- underline" form  encEqRefl t y = Pair (cor t) (cor y) , which
-- corresponds to Guard's "num(whole)" Def 12 convention.  Guard's
-- partial-underline form (e.g.  "th_x = _j"  with structured LHS) is
-- provably equal under cor's Rec-unfolding, so using whole-underline
-- uniformly preserves the chain's logical content.
--
-- This session: steps 1 and 2 only.  Steps 3-5 and the closure into
-- ChainBRA are follow-up work.
--
-- Conventions: --safe --without-K --exact-split, no postulates, no
-- holes.

module Guard.RouteAChain where

open import Guard.Base
open import Guard.Term
open import Guard.Step
open import Guard.SubstOp using (substOp)
open import Guard.ThFunTForV3 using (thmT)
open import Guard.CodeOfReify using (cor)
open import Guard.SubstTForPrecompClassical
  using (Triv ; gsCR ; cGSCR ; trivCT ; templateCodeCR)
open import Guard.GodelIClassical using (diagFTargetCR)
open import Guard.Formula
open import Guard.Provable
open import Guard.ProvableLemmas using (deductionThm)
open import Guard.RouteADf using (DfRefl ; encEqRefl ; thm13AtRefl)

private
  v1 : Nat
  v1 = suc zero

------------------------------------------------------------------------
-- The target equations shared by all chain steps.
--
-- j is the Goedel number of gsCR (the Gödel sentence), reified as a
-- closed Term.
--
-- rhsT is the "sub(i,i)"-equivalent Term from Guard.GodelIClassical:
-- a substOp-expression that provably equals  reify cGSCR  via
-- diagFTargetCR.

j : Term
j = reify cGSCR

rhsT : Term
rhsT = ap2 substOp
         (ap2 Pair (ap1 cor (reify templateCodeCR)) (reify (natCode v1)))
         (reify templateCodeCR)

-- x : Term   -- the proof slot.  We use  var zero  directly; no shift.

-- thx : Term   -- th applied to the proof slot.
thx : Term
thx = ap1 (thmT trivCT) (var zero)

------------------------------------------------------------------------
-- Step 1 : th(x) = j  ⊃  th(Dth(x)) = "th(x) = j".
--
-- Under the whole-underline convention, "th(x) = j" becomes
--  encEqRefl thx j = Pair (cor thx) (cor j) .  thm13AtRefl at t = thx,
-- y = j gives a Provable at hyp = (atomic (thx = j)) by using ruleHypP
-- for the hypothesis; deductionThm discharges it into a Provable imp.

chainStep1 : {hyp : Formula} ->
  Provable hyp
    (atomic (eqn thx j)
     imp
     atomic (eqn (ap1 (thmT trivCT) (DfRefl thx j))
                 (encEqRefl thx j)))
chainStep1 =
  deductionThm (atomic (eqn thx j)) _
    (thm13AtRefl thx j ruleHypP)

------------------------------------------------------------------------
-- Step 2 : th(Dsub(i,i)) = "sub(i,i) = j".
--
-- Closed-form: sub(i,i) = j  is provable as  Deriv hyp (eqn rhsT j)  via
-- diagFTargetCR.  Feed that through  thm13AtRefl  at t = rhsT, y = j
-- (no deductionThm since the hypothesis is discharged as fromDeriv).

chainStep2 : {hyp : Formula} ->
  Provable hyp
    (atomic (eqn (ap1 (thmT trivCT) (DfRefl rhsT j))
                 (encEqRefl rhsT j)))
chainStep2 {hyp} =
  thm13AtRefl rhsT j (fromDeriv diagFTargetCR)

------------------------------------------------------------------------
-- Remaining work (follow-up)
-- =====================================================================
--
-- Step 3: combine steps 1 and 2.  From step 1, under  th(x) = j , we
-- have  th(Dth(x)) = Pair (cor thx) (cor j) .  From step 2,
--  th(Dsub(i,i)) = Pair (cor rhsT) (cor j) .  We want to derive
--  th(gx) = Pair (cor thx) (cor rhsT)  conditional on  th(x) = j .
--
-- Strategy: rewrite step 1's RHS slot from  cor j  to  cor rhsT  via
--  cor j = cor rhsT  (from  rhsT = j  via diagFTargetCR + prCong1 cor
-- + prSym).  The encoding gx of the combined proof requires a term-
-- level combinator that mirrors an "internal transitivity": given the
-- encoded proofs  Dth(x) (concluding "th(x) = j")  and  Dsub(i,i)
-- (concluding "sub(i,i) = j"), build an encoded proof whose validator
-- computes "th(x) = sub(i,i)".  This is Guard's internal  encRuleSym
-- (to flip Dsub to "j = sub(i,i)")  +  encRuleTrans .
--
-- Steps 4 and 5 follow a similar pattern using encoded proofs of the
-- inequality axioms and eliminate to the "0 = 1" conclusion.  The
-- closure then feeds through ConBRA  via substitution into  var zero
-- and combines with  provableGodelIBridge  (Guard.ProvableGodelIBridge)
-- to discharge.
--
-- Each remaining step is ~30-80 lines.  Total chain completion:
-- ~200-300 lines.
--
-- Typechecks under --safe --without-K --exact-split.  No postulates,
-- no holes.
