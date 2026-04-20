{-# OPTIONS --safe --without-K --exact-split #-}

-- Classical (Ryan-style) Gödel I.
--
-- Consistent(Triv) ==> Triv ⊬ gsCR
--
-- gsCR is Ryan's Lemma 3 Gödel sentence in our tree-setting:
-- a one-free-variable equation (only v_0, the proof slot; v_11', v_12'
-- are NOT present).  The self-referential diagonal is closed via
-- codeOfReify (cor) which is a pure Rec-based Fun1 — no new primitives.
--
-- Proof structure (Ryan's Lemma 3 pattern):
--   1. Assume d : Deriv Triv gsCR.
--   2. pe = thm14EV3 d : ProofE3 Triv gsCR  (DC1 reflection).
--      enc = encT pe ; corr pe : polymorphic  thmT(trivCT)(enc) = reify cGSCR .
--   3. Instantiate gsCR at v_0 := enc.  Rewrite LHS via corr,
--      rewrite RHS via diagFTargetCR (which uses corOfReify + V3
--      diagonal).  Both sides land on  reify cGSCR .
--   4. treeEqSelf closes ⊥.
--
-- Non-trivial because gsCR has no closed instance that is trivially
-- refuted without the hypothesis: the diagonal collapse requires
-- enc built from the hypothetical d via thm14EV3.

module Guard.GodelIClassical where

open import Guard.Base
open import Guard.Term
open import Guard.Step
open import Guard.StepReduce
open import Guard.SubstCorrect
open import Guard.SubstTForCorrect
open import Guard.SubstOp using (substOp ; substOpEquiv)
open import Guard.ThFun using (codeEqn)
open import Guard.ThFunTForV3 using (thmT)
open import Guard.CodeOfReify using (cor ; corOfReify)
open import Guard.SubstTForPrecompClassical
open import Guard.TreeEqSelf using (treeEqSelf)
open import Guard.Thm14EV3 using (ProofE3 ; thm14EV3 ; encT ; corr)
open import Guard.Nelson.SubstReify using (substReify)

private
  v1 : Nat ; v1 = suc zero
  tgtT : Tree ; tgtT = natCode v1
  poo : Term ; poo = ap2 Pair O O

  trueT : Term ; trueT = O
  falseT : Term ; falseT = poo

------------------------------------------------------------------------
-- Diagonal identity for the classical template.
--
-- substOp(Pair (ap1 cor (reify templateCodeCR)) (reify (natCode v1)))
--        (reify templateCodeCR)
--   == reify cGSCR.
--
-- Step A: rewrite  ap1 cor (reify templateCodeCR)  to  reify crTCCR
--         via  corOfReify templateCodeCR .
-- Step B: apply the V3-style diagonal with replT = crTCCR,
--         target-tree = templateCodeCR.

diagFTargetCR : {hyp : Equation} ->
  Deriv hyp (eqn (ap2 substOp (ap2 Pair (ap1 cor (reify templateCodeCR))
                                        (reify (natCode v1)))
                              (reify templateCodeCR))
                 (reify cGSCR))
diagFTargetCR {hyp} =
  let
    -- Step A: corOfReify bridges cor to the reified code.  Then
    -- replace  code (reify templateCodeCR)  with  crTCCR  via
    -- crTCCRDef (abstract-defined equality).
    corStep0 : Deriv hyp (eqn (ap1 cor (reify templateCodeCR))
                              (reify (code (reify templateCodeCR))))
    corStep0 = corOfReify templateCodeCR

    corStep : Deriv hyp (eqn (ap1 cor (reify templateCodeCR))
                             (reify crTCCR))
    corStep = eqSubst
      (\c -> Deriv hyp (eqn (ap1 cor (reify templateCodeCR)) (reify c)))
      (eqSym crTCCRDef) corStep0

    -- Rewrite the first Pair arg of substOp.
    rewriteA : Deriv hyp
      (eqn (ap2 substOp (ap2 Pair (ap1 cor (reify templateCodeCR))
                                  (reify (natCode v1)))
                        (reify templateCodeCR))
           (ap2 substOp (ap2 Pair (reify crTCCR)
                                  (reify (natCode v1)))
                        (reify templateCodeCR)))
    rewriteA = congL substOp (reify templateCodeCR)
                 (congL Pair (reify (natCode v1)) corStep)

    -- Step B: V3-style diagonal.
    combined : Deriv hyp (eqn (ap1 (closedSubstTFor (reify crTCCR) (reify tgtT))
                                (ap2 Pair (reify codeLhsTCR) (reify codePoo)))
                              (reify (codedSubst crTCCR tgtT
                                        (nd codeLhsTCR codePoo))))
    combined = closedSTFNd crTCCR tgtT codeLhsTCR codePoo
                 codeLhsTCRNeqTagVar codeLhsTCRNotVar
                 (lhsTCRSTF crTCCR) (pooSTF crTCCR)

    combinedTC : Deriv hyp (eqn (ap1 (closedSubstTFor (reify crTCCR) (reify tgtT))
                                  (reify templateCodeCR))
                                (reify (codedSubst crTCCR tgtT templateCodeCR)))
    combinedTC = eqSubst (\tc -> Deriv hyp
                            (eqn (ap1 (closedSubstTFor (reify crTCCR) (reify tgtT))
                                   (reify tc))
                                 (reify (codedSubst crTCCR tgtT tc))))
                         (eqSym templateCodeCRForm) combined

    fp : Eq (codedSubst crTCCR tgtT templateCodeCR) cGSCR
    fp = eqTrans
           (eqSubst (\tc -> Eq (codedSubst crTCCR tgtT tc)
                               (codedSubst crTCCR tgtT (nd codeLhsTCR codePoo)))
                    (eqSym templateCodeCRForm) refl)
           (eqTrans
             (codedSubstNd crTCCR tgtT codeLhsTCR codePoo codeLhsTCRNotVar)
             (eqSym cGSisCSCR))

    combinedCGS : Deriv hyp (eqn (ap1 (closedSubstTFor (reify crTCCR) (reify tgtT))
                                  (reify templateCodeCR))
                                (reify cGSCR))
    combinedCGS = eqSubst (\c -> Deriv hyp
                            (eqn (ap1 (closedSubstTFor (reify crTCCR) (reify tgtT))
                                   (reify templateCodeCR))
                                 (reify c)))
                          fp combinedTC

    substOpStep : Deriv hyp (eqn (ap2 substOp (ap2 Pair (reify crTCCR) (reify (natCode v1)))
                                              (reify templateCodeCR))
                                 (ap1 (closedSubstTFor (reify crTCCR) (reify (natCode v1)))
                                      (reify templateCodeCR)))
    substOpStep = substOpEquiv (reify crTCCR) (reify (natCode v1)) templateCodeCR
  in ruleTrans rewriteA (ruleTrans substOpStep combinedCGS)

------------------------------------------------------------------------
-- Classical Gödel I.

godelIClassical : Deriv Triv gsCR -> Deriv Triv (eqn trueT falseT)
godelIClassical d = ruleTrans (ruleSym selfEq) stepB
  where
  pe : ProofE3 Triv gsCR
  pe = thm14EV3 d

  enc : Term
  enc = encT pe

  corrPf : Deriv Triv (eqn (ap1 (thmT trivCT) enc) (reify cGSCR))
  corrPf =
    eqSubst (\t -> Deriv Triv (eqn (ap1 (thmT t) enc) (reify cGSCR)))
      (eqSym trivCTDef)
      (eqSubst (\c -> Deriv Triv (eqn (ap1 (thmT (reify (codeEqn Triv))) enc) (reify c)))
        (eqSym cGSdefCR)
        (corr pe))

  -- ruleInst the proof slot v_0 := enc.
  d1 : Deriv Triv (substEq zero enc gsCR)
  d1 = ruleInst zero enc d

  lhsT : Term
  lhsT = ap1 (thmT trivCT) enc

  rhsT : Term
  rhsT = ap2 substOp (ap2 Pair (ap1 cor (reify templateCodeCR))
                               (reify (natCode v1)))
                     (reify templateCodeCR)

  expected : Equation
  expected = eqn (ap2 TreeEq lhsT rhsT) poo

  d1Conv : Deriv Triv expected
  d1Conv = eqSubst (\eq -> Deriv Triv eq) (subst0GSCR enc) d1

  -- Rewrite LHS via corrPf.
  stepA : Deriv Triv (eqn (ap2 TreeEq (reify cGSCR) rhsT) poo)
  stepA = ruleTrans (ruleSym (congL TreeEq rhsT corrPf)) d1Conv

  -- Rewrite RHS via diagFTargetCR.
  stepB : Deriv Triv (eqn (ap2 TreeEq (reify cGSCR) (reify cGSCR)) poo)
  stepB = ruleTrans (ruleSym (congR TreeEq (reify cGSCR) diagFTargetCR)) stepA

  selfEq : Deriv Triv (eqn (ap2 TreeEq (reify cGSCR) (reify cGSCR)) O)
  selfEq = treeEqSelf (reify cGSCR)

------------------------------------------------------------------------
-- Contrapositive: if Triv is consistent, Triv does not prove gsCR.

godelIClassicalContra : Consistent Triv ->
                        Deriv Triv gsCR ->
                        Empty
godelIClassicalContra con d = con (godelIClassical d)
