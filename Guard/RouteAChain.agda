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
-- Step 4 — BLOCKED : formula-level negation encoding obstruction
-- =====================================================================
--
-- Guard 1963's step 4 (guard15.pdf p.17):
--   th(x) = j  ⊃  th(4J(J(num x,1),x)+1)  =  "th(x) ≠ sub(i,i)"
--
-- In Guard's BRA, the RHS  "th(x) ≠ sub(i,i)"  is the Goedel number of
-- the FORMULA  ~(th(x) = sub(i,i)) , using Def 11.3's negation
-- encoding  "~P" = 3("P") + 2 .  The LHS  4J(J(num x,1),x) + 1  is a
-- SPECIFIC BRA term whose value (at runtime, depending on x's value)
-- equals this negation-encoded Goedel number BY CONSTRUCTION — no
-- proof of the equation itself is needed.  th just routes through the
-- formula-level-negation dispatch.
--
-- Our tree system works at the EQUATIONAL layer only: our thmT
-- validates encoded proofs of Deriv-level equations, and every
-- validator output is the Goedel code of a VALID equational conclusion
-- (provable under the Deriv system).  There is no  3P + 2  negation-
-- dispatch.  Instead we encode "A ≠ B" as the equation
-- "TreeEq A B = poo".
--
-- Obstruction: to have Y such that  thmT trivCT Y = encEq("TreeEq thx
-- rhsT = poo") , Y would have to encode an actual Deriv proof of
--  TreeEq thx rhsT = poo .  But  TreeEq thx rhsT = poo  IS (the
-- substituted form of) gsCR — the Gödel sentence, unprovable in our
-- system by Gödel I.  So no such Y exists polymorphically.
--
-- Under the inner hyp  thx = j , we can go the OPPOSITE way:
--   thx = j      (hyp)
--   rhsT = j     (closed, diagFTargetCR)
--   ~> thx = rhsT
--   ~> TreeEq thx rhsT = TreeEq rhsT rhsT  (via axEqCongL TreeEq)
--   ~> TreeEq rhsT rhsT = O                (treeEqSelfReify cGSCR +
--                                           rhsT = reify cGSCR rewrite)
--   ~> TreeEq thx rhsT = O
-- which is the NEGATION of what step 4 wants (O vs poo).  So our
-- equational framework proves the step-4-OPPOSITE, not step 4 itself.
--
-- This asymmetry is intrinsic to having replaced BRA's formula-level
-- negation with the  TreeEq-returns-poo  convention: equational
-- reasoning alone cannot manufacture a "negative" validator output
-- without an actual positive proof of the equation.
--
-- Resolution options (deferred, each is a substantial extension):
--
--  (Q1) Add a formula-level negation encoder to the Deriv/ProofEnc
--       system: a new encoded-proof combinator whose validator output
--       is ~(encoded-equation) per Def 11.3.  This would add BRA's
--       formula-level reasoning to our otherwise equational Deriv.
--       Requires extending  thmTStep  with a new dispatch case.
--       Estimated ~500-1000 lines.
--
--  (Q2) Reframe the chain to use EQUATIONAL-level reasoning only,
--       skipping the formula-level-negation step.  Specifically,
--       replace step 4's  "th(Y) = 'th(x) ≠ sub(i,i)'"  with
--       "Y = encoded proof of  TreeEq thx rhsT = O  (NOT poo)"
--       — which IS derivable under  thx = j  + diagFTargetCR +
--       treeEqSelfReify .  Then step 5 becomes: from  ConBRA
--       substituted + (TreeEq thx rhsT = O) via the formula-
--       substitution at var zero := combined_new , derive
--        O = falseT , i.e., codeBot.
--       Requires redesigning combined_new and step 5's Provable
--       derivation.  Estimated ~300-500 lines.
--
--  (Q3) Move the contradiction-extraction to the closure step
--       (step 6) entirely, bypassing step 4 and 5.  Under ConBRA +
--       Formula-substitute var zero := (reify cGSCR) = j  (a specific
--       closed term in the image of reify): ConBRA@j gives  TreeEq
--       (th j) codeBotT = falseT .  Under the semantic interpretation
--       (provExtract), this means there's NO Deriv proof of 0 = 1 via
--       j.  Combined with godelIClassical's use of j as the Gödel
--       sentence — this is exactly the closed form of the chain we
--       already have in Guard.ProvableGodelIBridge!  May short-circuit
--       the chain construction.  Requires verifying that the
--       substituted ConBRA's content equals gsCR's content modulo
--       closed facts — which it may or may not, depending on the
--       exact Provable vs Deriv semantic mapping.
--
-- Given the complexity, further progress requires picking one of
-- (Q1)-(Q3).  This file commits chain steps 1-3 as a clean partial
-- deliverable.

------------------------------------------------------------------------
-- Typechecks under --safe --without-K --exact-split.  No postulates,
-- no holes.

------------------------------------------------------------------------
-- Typechecks under --safe --without-K --exact-split.  No postulates,
-- no holes.
