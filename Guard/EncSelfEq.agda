{-# OPTIONS --safe --without-K --exact-split #-}

-- Guard.EncSelfEq — proof-of-concept for the meta-level reflection
-- approach to encoding closed derivations.
--
-- The key insight from the April 2026 session: for any CLOSED Deriv
-- (one that doesn't depend on the hypothetical  d  we're internalising),
-- we can encode it via  encT ∘ thm14EV3  at the meta level.  The
-- correctness comes for free from  corr ∘ thm14EV3 .
--
-- This file tests the insight on  treeEqSelf (reify cGSCR) , which is
-- the  selfEq  sub-derivation used by  godelIClassical .

module Guard.EncSelfEq where

open import Guard.Base
open import Guard.Term
open import Guard.Step
open import Guard.ThFun using (codeEqn)
open import Guard.ThFunTForV3 using (thmT)
open import Guard.Thm14EV3 using (ProofE3 ; thm14EV3 ; encT ; corr)
open import Guard.TreeEqSelf using (treeEqSelf)
open import Guard.SubstTForPrecompClassical using (Triv ; trivCT ; trivCTDef ; cGSCR)

private
  cGSCRT : Term
  cGSCRT = reify cGSCR

------------------------------------------------------------------------
-- The specific derivation we want to encode:  treeEqSelf  at  reify cGSCR
-- under hypothesis  Triv.

selfEqDeriv : Deriv Triv (eqn (ap2 TreeEq cGSCRT cGSCRT) O)
selfEqDeriv = treeEqSelf cGSCRT

------------------------------------------------------------------------
-- The encoded ProofE3 package — produced by thm14EV3 meta-level.

selfEqPE : ProofE3 Triv (eqn (ap2 TreeEq cGSCRT cGSCRT) O)
selfEqPE = thm14EV3 selfEqDeriv

------------------------------------------------------------------------
-- encSelfEq : the closed encoded Term.

encSelfEq : Term
encSelfEq = encT selfEqPE

------------------------------------------------------------------------
-- Correctness — comes for free from corr (thm14EV3 _).
--
-- Polymorphic in hyp.  Says: thmT (reify (codeEqn Triv)) of encSelfEq
-- equals  reify (codeEqn (eqn (TreeEq cGSCRT cGSCRT) O)) .

encSelfEqCorrRaw : {hyp : Equation} ->
  Deriv hyp (eqn (ap1 (thmT (reify (codeEqn Triv))) encSelfEq)
                 (reify (codeEqn (eqn (ap2 TreeEq cGSCRT cGSCRT) O))))
encSelfEqCorrRaw = corr selfEqPE

------------------------------------------------------------------------
-- Specialised form using trivCT (same thing; trivCT is abstract-defined
-- to be  reify (codeEqn Triv) , bridged via trivCTDef).

encSelfEqCorr : {hyp : Equation} ->
  Deriv hyp (eqn (ap1 (thmT trivCT) encSelfEq)
                 (reify (codeEqn (eqn (ap2 TreeEq cGSCRT cGSCRT) O))))
encSelfEqCorr {hyp} =
  eqSubst (\c -> Deriv hyp (eqn (ap1 (thmT c) encSelfEq)
                                (reify (codeEqn (eqn (ap2 TreeEq cGSCRT cGSCRT) O)))))
          (eqSym trivCTDef) encSelfEqCorrRaw

------------------------------------------------------------------------
-- End-to-end test: chain encSelfEq through encRuleSym to produce the
-- encoded (sym selfEq) sub-proof, verifying the meta-reflection-based
-- encoding integrates with the combinator-based encoders in ProofEnc.
--
-- encSelfEq has shape  Pair (reify (pa selfEqPE)) (reify (pb selfEqPE)) ,
-- i.e. definitionally a Pair.  encRuleSymCorr requires the sub-encoding
-- be literally Pair paR pbR — this test forces Agda to confirm encSelfEq
-- has that shape.

open import Guard.ProofEnc using (encRuleSym ; encRuleSymCorr)

private
  selfEqCodedEqn : Term
  selfEqCodedEqn = reify (codeEqn (eqn (ap2 TreeEq cGSCRT cGSCRT) O))

  -- The codeEqn above reifies to  Pair (reify (code (TreeEq cGSCRT cGSCRT)))
  --                                    (reify (code O)) .
  -- Both sides are reified codes.  We name them.
  lhsC : Term
  lhsC = reify (code (ap2 TreeEq cGSCRT cGSCRT))

  rhsC : Term
  rhsC = reify (code O)

-- encRuleSym-wrapping of encSelfEq.
encSymSelfEq : Term
encSymSelfEq = encRuleSym encSelfEq

-- Correctness: thmT trivCT (encSymSelfEq) = Pair rhsC lhsC (sides flipped).
encSymSelfEqCorr : {hyp : Equation} ->
  Deriv hyp (eqn (ap1 (thmT trivCT) encSymSelfEq) (ap2 Pair rhsC lhsC))
encSymSelfEqCorr =
  encRuleSymCorr trivCT (reify (ProofE3.pa selfEqPE)) (reify (ProofE3.pb selfEqPE))
    lhsC rhsC encSelfEqCorr
