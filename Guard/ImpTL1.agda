{-# OPTIONS --safe --without-K --exact-split #-}

-- Guard.ImpTL1 -- Rose's Lemma 1 in object-level impT form.
--
-- Given a derivation  d : Deriv H B , produce  V : Term -> Term -> Term
-- (via the same structural construction as  Guard.RoseLemma1T ) and an
-- UNCONDITIONAL derivation at Triv of the impT equation:
--
--   impT (TreeEq (thmT trivCT (Pair tPa tPb)) [H])
--        (TreeEq (thmT trivCT (Pair (vPaF tPa tPb) (vPbF tPa tPb))) [B])
--     = trueT
--
-- This is Rose 1967 Lemma 1 at n=1 stated with object-level arithmetic
-- implication ( impT ) rather than meta-level conditional (Agda arrow).
-- Unlike  roseLemma1T , the impT form does NOT require caller-supplied
-- polymorphic-in-hyp tCorr / tPass -- the antecedent is part of the
-- conclusion's structure, not a precondition.
--
-- Each case of the Deriv induction mirrors its  roseLemma1T  counterpart
-- for V construction, but the correctness proof uses  impTSelf ,
-- impTAnyTrueT , impTConsTrue  (Guard.ImpTSchemaF)  to wrap the
-- underlying polymorphic-in-hyp derivation.
--
-- No postulates, no holes.

module Guard.ImpTL1 where

open import Guard.Base
open import Guard.Term
open import Guard.Step
open import Guard.TreeEqSelf using (treeEqSelf)
open import Guard.ThFun using (codeEqn)
open import Guard.ThFunTForV3 using (thmT)
open import Guard.SubstTForPrecompClassical using (trivCT)
open import Guard.ImpT
open import Guard.ImpTSchemaF using (impTSelf ; impTAnyTrueT ; impTConsTrue)
open import Guard.ProofEnc

------------------------------------------------------------------------
-- Abbreviations.

private
  n0  : Nat ; n0  = zero

------------------------------------------------------------------------
-- The impT-form Lemma 1 record.

record ImpTL1 (H B : Equation) : Set where
  constructor mkImpTL1
  field
    vPaF : Term -> Term -> Term
    vPbF : Term -> Term -> Term
    vCorrImpT : (tPa tPb : Term) {hyp : Equation} ->
      Deriv hyp (eqn
        (impT
          (ap2 TreeEq (ap1 (thmT trivCT) (ap2 Pair tPa tPb))
                      (reify (codeEqn H)))
          (ap2 TreeEq (ap1 (thmT trivCT)
                              (ap2 Pair (vPaF tPa tPb) (vPbF tPa tPb)))
                      (reify (codeEqn B))))
        trueT)

open ImpTL1 public

------------------------------------------------------------------------
-- Helper: from  Deriv hyp (th V = reify (codeEqn B))  (polymorphic-in-hyp
-- correctness witness), produce the impT-form Lemma 1 with V constant in
-- tPa/tPb.
--
-- This is the closure used for every CLOSED-AXIOM case (where V does NOT
-- depend on the hypothesis encoding).

fromClosedAxiom : {H B : Equation} ->
  (vPa vPb : Term) ->
  ({hyp : Equation} ->
    Deriv hyp (eqn (ap1 (thmT trivCT) (ap2 Pair vPa vPb)) (reify (codeEqn B)))) ->
  ImpTL1 H B
fromClosedAxiom {H} {B} vPa vPb corr = mkImpTL1
  (\_ _ -> vPa)
  (\_ _ -> vPb)
  (\tPa tPb {hyp} -> impTConsTrue _ _ (consequentIsTrueT {hyp}))
  where
  -- Given corr, TreeEq (th V) [B] = TreeEq [B] [B] = O = trueT.
  consequentIsTrueT : {hyp : Equation} ->
    Deriv hyp (eqn (ap2 TreeEq (ap1 (thmT trivCT) (ap2 Pair vPa vPb))
                                (reify (codeEqn B))) trueT)
  consequentIsTrueT {hyp} = ruleTrans
    (congL TreeEq (reify (codeEqn B)) (corr {hyp}))
    (treeEqSelf (reify (codeEqn B)))

------------------------------------------------------------------------
-- Closed axiom: axI.
--
-- encAxI tC encodes axI t.  encAxICorr is the polymorphic-in-hyp
-- correctness witness.

impTL1_AxI : (H : Equation) (t : Term) -> ImpTL1 H (eqn (ap1 I t) t)
impTL1_AxI H t =
  fromClosedAxiom O (ap2 Pair (reify (code t)) O)
    (\{hyp} -> encAxICorr trivCT (reify (code t)) {hyp})

------------------------------------------------------------------------
-- Hypothesis case: ruleHyp.
--
-- vPaF tPa tPb = tPa , vPbF tPa tPb = tPb .
-- The antecedent and consequent of the impT are LITERALLY THE SAME
-- equation, so the impT reduces to  impT X X = trueT  via impTSelf.

impTL1_Hyp : (H : Equation) -> ImpTL1 H H
impTL1_Hyp H = mkImpTL1
  (\tPa _ -> tPa)
  (\_ tPb -> tPb)
  (\tPa tPb {hyp} -> impTSelf _ {hyp})

------------------------------------------------------------------------
-- Summary (so far)
--
-- Record ImpTL1 H B packages the impT-form Lemma 1 output.
-- Two cases implemented:
--   * impTL1_AxI H t             : closed-axiom case (generalises)
--   * impTL1_Hyp H               : ruleHyp, uses impTSelf.
--
-- Next steps (structural cases): ruleSym, ruleTrans, cong1, congL,
-- congR, ruleInst, ruleF.  Each will require a bridge from IH's impT
-- to the transformed output, most likely via a new helper for
-- chaining impT equations.
