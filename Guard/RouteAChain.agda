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
open import Guard.ProvableEqLifts using (prSym ; prTrans ; prCong1 ; prCongR)
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
-- Step 3 : th(x) = j  ⊃  th(gx) = "th(x) = sub(i,i)".
--
-- We reuse the Df term  DfRefl thx j  from step 1 (no need for a
-- new  gx  combinator under the whole-underline encoding + prTrans-
-- based rewrite).  The Provable chain:
--
--   step1 (under hyp  thx = j ):    th (DfRefl thx j) = Pair (cor thx) (cor j)
--   closed fact (diagFTargetCR):    rhsT = j
--     ~> via prSym + prCong1 cor:   cor j = cor rhsT
--     ~> via prCongR Pair:          Pair (cor thx) (cor j) = Pair (cor thx) (cor rhsT)
--   prTrans glues to:               th (DfRefl thx j) = Pair (cor thx) (cor rhsT)

chainStep3 : {hyp : Formula} ->
  Provable hyp
    (atomic (eqn thx j)
     imp
     atomic (eqn (ap1 (thmT trivCT) (DfRefl thx j))
                 (ap2 Pair (ap1 cor thx) (ap1 cor rhsT))))
chainStep3 =
  deductionThm (atomic (eqn thx j)) _ body
  where
  body :
    Provable (atomic (eqn thx j))
      (atomic (eqn (ap1 (thmT trivCT) (DfRefl thx j))
                   (ap2 Pair (ap1 cor thx) (ap1 cor rhsT))))
  body =
    prTrans _ (encEqRefl thx j) _
      (thm13AtRefl thx j ruleHypP)
      rewrCorJ
    where
    jIsRhsT : Provable (atomic (eqn thx j)) (atomic (eqn j rhsT))
    jIsRhsT = prSym rhsT j (fromDeriv diagFTargetCR)
    corjCorrhsT : Provable (atomic (eqn thx j))
                    (atomic (eqn (ap1 cor j) (ap1 cor rhsT)))
    corjCorrhsT = prCong1 cor j rhsT jIsRhsT
    rewrCorJ : Provable (atomic (eqn thx j))
                 (atomic (eqn (encEqRefl thx j)
                              (ap2 Pair (ap1 cor thx) (ap1 cor rhsT))))
    rewrCorJ = prCongR Pair (ap1 cor j) (ap1 cor rhsT) (ap1 cor thx) corjCorrhsT

------------------------------------------------------------------------
-- Remaining work (follow-up)
-- =====================================================================
--
-- Step 4 : th(x) = j  ⊃  th(Y) = "th(x) ≠ sub(i,i)".
--
-- "th(x) ≠ sub(i,i)" corresponds to the equation
--   TreeEq (thx) rhsT = poo
-- ("TreeEq returns poo iff unequal").  Under the whole-underline
-- encoding, this is  Pair (cor (TreeEq thx rhsT)) (cor poo) .  The step
-- uses  thm13AtRefl  at  t = TreeEq thx rhsT , y = poo , with the
-- Provable hypothesis  TreeEq thx rhsT = poo  extracted from  j 's
-- definition:  gsCR  (substituted form) IS exactly this equation,
-- modulo the  thx  slot.  Hence "by the definition of j" in Guard.
-- The hypothesis is NOT  thx = j  (that's the premise), but a closed
-- consequence of  j 's encoding — obtained via the unfolding of
--  reify cGSCR  as the Gödel number of  gsCR .  Requires careful
-- threading through  subst0GSCR  (Guard.SubstTForPrecompClassical).
--
-- Step 5 : combine steps 3 and 4.
--
-- Under hyp, we have:
--   step3:  th (D1) = Pair (cor thx) (cor rhsT)           -- "thx = rhsT"
--   step4:  th (D2) = Pair (cor (TreeEq thx rhsT)) (cor poo)
--                                                          -- "TreeEq thx rhsT = poo"
-- "combined" should validate to  "0 = 1" = Pair (cor O) (cor poo)
--  under hyp.
--
-- This is where a genuine Df-combining combinator enters: we need to
-- build a combined encoded proof whose validator output is exactly
--  Pair (cor O) (cor poo) .  In our Deriv system this is the
-- contradiction step: from  TreeEq thx rhsT = O  (derivable from step
-- 3 via axRefl + TreeEq self-equality  treeEqSelfReify ) AND
--  TreeEq thx rhsT = poo  (step 4), we get  O = poo , which is
-- "0 = 1".
--
-- Encoding at the Deriv / thmT level: use  encRuleTrans  to glue
-- Dth(x)-based and Y-based encoded proofs.  Requires a new encoded-
-- proof combinator  encMp  or manual construction via  encRuleTrans
-- + encRuleSym .  ~80-120 lines.
--
-- Step 6 : ChainBRA closure.  Substitute  var zero := combined  into
-- the hypothesis  ConBRA  to obtain  th(combined) ≠ codeBot , then
-- combine with step 5's conclusion  th(combined) = codeBot  to derive
--  atomic gsCR  (Gödel I's input, via  provableGodelIBridge ).
--
-- ~80 lines.

------------------------------------------------------------------------
-- Typechecks under --safe --without-K --exact-split.  No postulates,
-- no holes.
