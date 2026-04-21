{-# OPTIONS --safe --without-K --exact-split #-}

-- Guard.EncCorrPfAnalysis -- feasibility of encCorrPf via meta-reflection.
--
-- Goal: the load-bearing encCorrPf encoder needed by
-- Guard.GodelIIClassicalSkel.  Specification:
--   encCorrPf : Term -> Term
--   encCorrPfCorr : (v0 : Term) {hyp : Equation} ->
--     Deriv hyp (eqn (ap1 (thmT trivCT) (encCorrPf v0))
--                    (reify (codeEqn (eqn (ap1 (thmT trivCT) v0) (reify cGSCR)))))
--
-- Outcome: direct construction via axiomatic reduction (Schema F,
-- congruence, ruleInst on existing Deriv axioms) is intractable for the
-- same reason as approach (C) for strongPhiCorr --- the target equation
-- hinges on a closed "template" sub-derivation
--   Deriv Triv (eqn (ap1 (thmT trivCT) (var zero)) (reify cGSCR))
-- which does not exist under Triv's axioms (thmT of a free variable has
-- no axiomatic reduction to reify cGSCR).
--
-- We isolate the exact obstruction by constructing a CONDITIONAL
-- encCorrPf that succeeds GIVEN the missing template derivation, via
-- meta-reflection (thm14EV3 applied to the template, then ruleInst'd at
-- v0 at the Deriv level).  The conditional is real Agda, no holes /
-- postulates: it proves
--   MissingTemplateDeriv -> EncCorrPfSpec .
-- The "MissingTemplateDeriv" is the analog of  MissingFactCgsBot  in
-- Guard.StrongPhiCorrAnalysis.
--
-- The intended fall-back is approach (A): internalise godelIClassical
-- via the existing 27-encoder library (encAxI..encRuleF, encRuleHyp) to
-- construct Phi with diagonal-awareness.  See
-- NEXT-SESSION-ENCCORRPF-FALLBACK.md.
--
-- No postulates, no holes.

module Guard.EncCorrPfAnalysis where

open import Guard.Base
open import Guard.Term
open import Guard.Step
open import Guard.ThFun using (codeEqn)
open import Guard.ThFunTForV3 using (thmT)
open import Guard.Nelson.SubstReify using (substReify)
open import Guard.SubstTForPrecompClassical
  using (Triv ; trivCT ; trivCTDef ; cGSCR ; substThmTCRFact)
open import Guard.Thm14EV3 using (ProofE3 ; thm14EV3 ; encT ; corr)

------------------------------------------------------------------------
-- The target specification of encCorrPf.

EncCorrPfSpec : Set
EncCorrPfSpec =
  Sigma (Term -> Term) (\encCorrPf ->
    (v0 : Term) {hyp : Equation} ->
    Deriv hyp (eqn (ap1 (thmT trivCT) (encCorrPf v0))
                   (reify (codeEqn (eqn (ap1 (thmT trivCT) v0)
                                        (reify cGSCR))))))

------------------------------------------------------------------------
-- The "missing fact":  a closed (under Triv) derivation of the
-- template equation with  var 0  in the proof slot.
--
-- This is the analog of  MissingFactCgsBot  in
-- Guard.StrongPhiCorrAnalysis.  The equation is NOT derivable from
-- Triv's axioms:
--
--   * Triv = eqn O O gives only the trivial hypothesis.
--   * ap1 (thmT trivCT) (var 0)  is "stuck": thmT = Rec O stepFn, but
--     axRecLf requires argument = O and axRecNd requires argument =
--     Pair _ _; var 0 is neither, so no Rec-axiom fires.
--   * cong1 / ruleTrans cannot bridge a stuck term with  reify cGSCR
--     (a specific closed reified tree) without an additional lemma
--     equating thmT-of-var-0 with something concrete.
--   * ruleInst only instantiates variables post-hoc; it cannot
--     CREATE a non-trivial equation where none exists.
--
-- Schema F (ruleF) also does not apply: ruleF requires BOTH functors
-- to satisfy the same Rec base/step, but  KT (reify cGSCR)  (the
-- "obvious" witness on one side) has base  ap1 (KT (reify cGSCR)) O
-- = reify cGSCR,  not  O  (thmT trivCT's base).  So Rec-style
-- extensionality cannot bridge.
--
-- We accept this as a formal hypothesis, matching the conditional
-- lemma style of Guard.StrongPhiCorrAnalysis.

MissingTemplateDeriv : Set
MissingTemplateDeriv =
  Deriv Triv (eqn (ap1 (thmT trivCT) (var zero)) (reify cGSCR))

------------------------------------------------------------------------
-- Subst reduction lemma: substituting  var 0 -> v0  in the template
-- yields the target equation.
--
-- subst 0 v0 (ap1 (thmT trivCT) (var 0)) = ap1 (thmT trivCT) v0
--   - subst on (var 0) hits (natEq 0 0 = true), yielding v0.
--   - subst on (thmT trivCT) is identity via  substThmTCRFact
--     (trivCT is closed).
-- subst 0 v0 (reify cGSCR) = reify cGSCR via  substReify  (reified
-- trees are subst-invariant: reify only introduces O and ap2 Pair, and
-- substF2 0 v0 Pair = Pair definitionally).

substTemplateReduce : (v0 : Term) ->
  Eq (substEq zero v0
       (eqn (ap1 (thmT trivCT) (var zero)) (reify cGSCR)))
     (eqn (ap1 (thmT trivCT) v0) (reify cGSCR))
substTemplateReduce v0 =
  eqCong2 eqn
    (eqCong (\f -> ap1 f v0) (substThmTCRFact zero v0))
    (substReify zero v0 cGSCR)

------------------------------------------------------------------------
-- Conditional construction of encCorrPf.
--
-- Strategy: use thm14EV3 as a "meta-reflection" from Deriv to encoded
-- Terms.  The key insight (same as Guard.EncSelfEq) is:
--
--   If  d : Deriv Triv G  then  encT (thm14EV3 d) : Term  and its
--   corr is POLYMORPHIC in ambient hyp with hCode = reify (codeEqn Triv)
--   = trivCT after a bridge via trivCTDef.
--
-- Here  G = eqn (ap1 (thmT trivCT) v0) (reify cGSCR)  which we obtain
-- by applying  ruleInst 0 v0  to the MissingTemplateDeriv  dBase  and
-- rewriting via  substTemplateReduce.  The resulting encoding
-- encT (thm14EV3 ...) satisfies the full EncCorrPfSpec.

encCorrPfFromTemplate : MissingTemplateDeriv -> EncCorrPfSpec
encCorrPfFromTemplate dBase = mkSigma encFn corrFn
  where
  -- For each v0, instantiate dBase and produce a Deriv of the target
  -- equation under Triv.
  dInst : (v0 : Term) ->
          Deriv Triv (eqn (ap1 (thmT trivCT) v0) (reify cGSCR))
  dInst v0 = eqSubst (Deriv Triv) (substTemplateReduce v0)
                     (ruleInst zero v0 dBase)

  -- Apply thm14EV3 meta-reflection.
  peInst : (v0 : Term) ->
           ProofE3 Triv (eqn (ap1 (thmT trivCT) v0) (reify cGSCR))
  peInst v0 = thm14EV3 (dInst v0)

  -- The encoded Term.
  encFn : Term -> Term
  encFn v0 = encT (peInst v0)

  -- The correctness proof, via corr + trivCTDef bridge.
  corrFn : (v0 : Term) {hyp : Equation} ->
    Deriv hyp (eqn (ap1 (thmT trivCT) (encFn v0))
                   (reify (codeEqn (eqn (ap1 (thmT trivCT) v0)
                                        (reify cGSCR)))))
  corrFn v0 {hyp} =
    eqSubst (\c -> Deriv hyp
             (eqn (ap1 (thmT c) (encFn v0))
                  (reify (codeEqn (eqn (ap1 (thmT trivCT) v0)
                                       (reify cGSCR))))))
            (eqSym trivCTDef)
            (corr (peInst v0))

------------------------------------------------------------------------
-- Summary / obstruction analysis.
--
-- The conditional  encCorrPfFromTemplate  proves that the ONLY missing
-- ingredient is  MissingTemplateDeriv .  Any construction of that
-- derivation would immediately yield  encCorrPf .
--
-- Options for supplying  MissingTemplateDeriv :
--
--   (I) Axiomatise it as a module parameter (analogous to
--       GodelIIClassicalSkel's Phi + strongPhiCorr).  This is
--       RULED OUT here: the project convention forbids postulates
--       and the "no holes" guarantee. Only meta-level facts that are
--       derivable from axioms are admissible.
--
--  (II) Change the hypothesis: if we were to work under H = eqn
--       (ap1 (thmT trivCT) (var 0)) (reify cGSCR)  (i.e. assume the
--       template as the ambient hypothesis), then  ruleHyp  would
--       give the derivation.  But then  hCode = reify (codeEqn H) !=
--       trivCT, and the encCorrPfCorr spec requires hCode = trivCT.
--       There is no rewrite rule bridging thmT at different hCodes
--       (they are different Fun1 constants).
--
-- (III) Approach (A): construct a NON-trivial Phi : Fun1 that
--       internalises the godelIClassical derivation, using the
--       existing 27 encoders in Guard.ProofEnc (encAxI..encRuleF,
--       encRuleHyp) to build the encoded proof tree transformation
--       step by step.  Phi v0 would then be the encoded form of
--       godelIClassical applied to v0 (treating v0 as the
--       hypothetical proof encoding).  The resulting strongPhiCorr
--       becomes derivable via the combinator-level correctness
--       lemmas in Guard.ProofEnc, WITHOUT needing a standalone
--       encCorrPf at all.
--
-- Approach (III) is the recommended path.  It sidesteps encCorrPf by
-- inlining the encoder chain directly into Phi's construction.  Size
-- estimate: ~500-1000 lines of encoder composition + Fun2 dispatch
-- code, mechanical given the 27 existing combinators.  See
-- NEXT-SESSION-ENCCORRPF-FALLBACK.md for the detailed plan.
