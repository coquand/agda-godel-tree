{-# OPTIONS --safe --without-K --exact-split #-}

-- V3 Gödel I: Deriv godelSentenceV3 (eqn trueT falseT).
--
-- Direct analog of Guard.archive.v2.GodelIIFast.botDeriv0, adapted to
-- use V3's  thmT (var v2)  evaluator and  substOp  substitution.
--
-- The key differences from V2:
--   * V3 uses  thm14EV3Hyp godelSentenceV3  (no mkProofEAny loophole)
--     to build a genuine encoding of the Gödel sentence as its own proof.
--   * The V2 diagonal trick is preserved but now uses TWO free variables:
--       var v1  — the template self-code placeholder (substituted in template).
--       var v2  — the  thmT  hCode placeholder (free until ruleInst v2).
--     This lets  corr pe 's hCode (reify cGSV3) match the sentence's
--     embedded hCode at the right point in the ruleInst chain.

module Guard.GodelIV3 where

open import Guard.Base
open import Guard.Term
open import Guard.Step
open import Guard.StepReduce
open import Guard.SubstCorrect
open import Guard.SubstTForCorrect
open import Guard.SubstOp using (substOp ; substOpEquiv)
open import Guard.ThFun using (codeEqn)
open import Guard.ThFunTForV3 using (thmT)
open import Guard.SubstTForPrecompV3
open import Guard.TreeEqSelf using (treeEqSelf)
open import Guard.Thm14EV3 using (ProofE3 ; thm14EV3 ; thm14EV3Hyp ; encT ; corr)

private
  v1 : Nat ; v1 = suc zero
  v2 : Nat ; v2 = suc v1
  v11' : Nat ; v11' = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))
  v12' : Nat ; v12' = suc v11'
  tgtT : Tree ; tgtT = natCode v1
  poo : Term ; poo = ap2 Pair O O

  trueT : Term ; trueT = O
  falseT : Term ; falseT = poo

------------------------------------------------------------------------
-- The V3 diagonal identity:
--   substOp (Pair (reify crTCV3) (reify (natCode v1))) (reify templateCodeV3)
--     = reify cGSV3.
--
-- Proof: substOpEquiv bridges substOp → cstfV3 (= closedSubstTFor); then
-- closedSTFNd decomposes cstfV3 at (nd codeLhsTV3 codePoo); then cGSisCSV3
-- re-expresses the codedSubst result as cGSV3.

diagFTargetV3 : {hyp : Equation} ->
  Deriv hyp (eqn (ap2 substOp (ap2 Pair (reify crTCV3) (reify (natCode v1)))
                              (reify templateCodeV3))
                 (reify cGSV3))
diagFTargetV3 {hyp} =
  let
    -- Start from closedSTFNd at (nd codeLhsTV3 codePoo).
    combined : Deriv hyp (eqn (ap1 (closedSubstTFor (reify crTCV3) (reify tgtT))
                                (ap2 Pair (reify codeLhsTV3) (reify codePoo)))
                              (reify (codedSubst crTCV3 tgtT
                                        (nd codeLhsTV3 codePoo))))
    combined = closedSTFNd crTCV3 tgtT codeLhsTV3 codePoo
                 codeLhsTV3NeqTagVar codeLhsTV3NotVar
                 (lhsTV3STF crTCV3) (pooSTF crTCV3)

    -- Bridge (ap2 Pair (reify codeLhsTV3) (reify codePoo)) to (reify templateCodeV3)
    -- via eqSym templateCodeV3Form: templateCodeV3 ≡ nd codeLhsTV3 codePoo.
    combinedTC : Deriv hyp (eqn (ap1 (closedSubstTFor (reify crTCV3) (reify tgtT))
                                  (reify templateCodeV3))
                                (reify (codedSubst crTCV3 tgtT templateCodeV3)))
    combinedTC = eqSubst (\tc -> Deriv hyp
                            (eqn (ap1 (closedSubstTFor (reify crTCV3) (reify tgtT))
                                   (reify tc))
                                 (reify (codedSubst crTCV3 tgtT tc))))
                         (eqSym templateCodeV3Form) combined

    -- Replace codedSubst crTCV3 tgtT templateCodeV3 with cGSV3.
    fp : Eq (codedSubst crTCV3 tgtT templateCodeV3) cGSV3
    fp = eqTrans
           (eqSubst (\tc -> Eq (codedSubst crTCV3 tgtT tc)
                               (codedSubst crTCV3 tgtT (nd codeLhsTV3 codePoo)))
                    (eqSym templateCodeV3Form) refl)
           (eqTrans
             (codedSubstNd crTCV3 tgtT codeLhsTV3 codePoo codeLhsTV3NotVar)
             (eqSym cGSisCSV3))

    combinedCGS : Deriv hyp (eqn (ap1 (closedSubstTFor (reify crTCV3) (reify tgtT))
                                  (reify templateCodeV3))
                                (reify cGSV3))
    combinedCGS = eqSubst (\c -> Deriv hyp
                            (eqn (ap1 (closedSubstTFor (reify crTCV3) (reify tgtT))
                                   (reify templateCodeV3))
                                 (reify c)))
                          fp combinedTC

    -- Finally, bridge substOp → closedSubstTFor via substOpEquiv.
    step1 : Deriv hyp (eqn (ap2 substOp (ap2 Pair (reify crTCV3) (reify (natCode v1)))
                                        (reify templateCodeV3))
                           (ap1 (closedSubstTFor (reify crTCV3) (reify (natCode v1)))
                                (reify templateCodeV3)))
    step1 = substOpEquiv (reify crTCV3) (reify (natCode v1)) templateCodeV3
  in ruleTrans step1 combinedCGS

------------------------------------------------------------------------
-- Gödel I on V3 — pending.
--
-- Blocker: need schematic substEq-lemmas for the ruleInst chain
-- (v2, v11', v12', 0) on godelSentenceV3.  Direct  refl  proofs cost
-- ~430s because each of the four substitutions re-traverses the large
-- (reify templateCodeV3) sub-term.  Must be written V2-Fast-style via
-- substReify + substClosedSTF + analogous lemmas for  thmT  and
--  substOp .  See the Guard.Nelson.SubstReify / Guard.Nelson.InstForm
-- template in V2.
--
-- diagFTargetV3 (above) is the main "mathematical" content of the
-- diagonal; the remaining work is purely the ruleInst plumbing.

{- Deferred: godelIDerivV3 : Deriv godelSentenceV3 (eqn trueT falseT)

------------------------------------------------------------------------
-- Gödel I on V3.
--
-- Under ambient hypothesis  godelSentenceV3 :
--   1. pe  = thm14EV3Hyp godelSentenceV3  gives ProofE3 gs gs.
--   2. corr pe : thmT (reify cGSV3) enc = reify cGSV3.
--   3. Four ruleInst's thread through the sentence (v2, v11', v12', 0):
--        v2   ↦ reify cGSV3            -- bind thmT's hCode
--        v11' ↦ reify crTCV3           -- bind substOp's first Pair arg
--        v12' ↦ reify (natCode v1)      -- bind substOp's second Pair arg
--        0    ↦ enc                     -- bind the proof slot
--   4. Rewrite LHS of TreeEq using corr pe; rewrite RHS using diagFTargetV3.
--      Both sides become (reify cGSV3).
--   5. treeEqSelf gives TreeEq(reify cGSV3)(reify cGSV3) = O.
--   6. ⊢ eqn O poo  =  eqn trueT falseT.

godelIDerivV3 : Deriv godelSentenceV3 (eqn trueT falseT)
godelIDerivV3 =
  let
    hyp = godelSentenceV3

    dG : Deriv hyp hyp
    dG = ruleHyp {hyp}

    pe : ProofE3 hyp hyp
    pe = thm14EV3Hyp hyp

    enc : Term
    enc = encT pe

    corrPf : Deriv hyp (eqn (ap1 (thmT (reify cGSV3)) enc) (reify cGSV3))
    corrPf = eqSubst
      (\c -> Deriv hyp (eqn (ap1 (thmT (reify c)) enc) (reify c)))
      (eqSym cGSdefV3)
      (corr pe)

    -- Four successive ruleInst's to bind the free variables in the sentence.
    d1 : Deriv hyp (substEq v2 (reify cGSV3) hyp)
    d1 = ruleInst v2 (reify cGSV3) dG

    d2 : Deriv hyp (substEq v11' (reify crTCV3) (substEq v2 (reify cGSV3) hyp))
    d2 = ruleInst v11' (reify crTCV3) d1

    d3 : Deriv hyp (substEq v12' (reify (natCode v1))
                     (substEq v11' (reify crTCV3) (substEq v2 (reify cGSV3) hyp)))
    d3 = ruleInst v12' (reify (natCode v1)) d2

    d4 : Deriv hyp (substEq zero enc
                     (substEq v12' (reify (natCode v1))
                       (substEq v11' (reify crTCV3)
                         (substEq v2 (reify cGSV3) hyp))))
    d4 = ruleInst zero enc d3

    -- d4's conclusion is a specific equation.  Claim: it equals
    --   eqn (ap2 TreeEq (ap1 (thmT (reify cGSV3)) enc)
    --                   (ap2 substOp (ap2 Pair (reify crTCV3) (reify (natCode v1)))
    --                                (reify templateCodeV3)))
    --       poo
    -- This reduces by substEq pushed through the sentence's structure.

    lhsT : Term
    lhsT = ap1 (thmT (reify cGSV3)) enc

    rhsT : Term
    rhsT = ap2 substOp (ap2 Pair (reify crTCV3) (reify (natCode v1)))
                       (reify templateCodeV3)

    expected : Equation
    expected = eqn (ap2 TreeEq lhsT rhsT) poo

    -- After the four ruleInst's, d4 should directly have conclusion `expected`
    -- by Agda's definitional unfolding of substEq through the open template.
    d4Conv : Deriv hyp expected
    d4Conv = d4

    -- Rewrite LHS: thmT(reify cGSV3)(enc) = reify cGSV3 (via corrPf).
    -- congL TreeEq rhsT corrPf : TreeEq(ap1 ..., rhsT) = TreeEq(reify cGSV3, rhsT).
    stepA : Deriv hyp (eqn (ap2 TreeEq (reify cGSV3) rhsT) poo)
    stepA = ruleTrans (ruleSym (congL TreeEq rhsT corrPf)) d4Conv

    -- Rewrite RHS: rhsT = reify cGSV3 (via diagFTargetV3).
    -- congR TreeEq (reify cGSV3) diagFTargetV3 :
    --   TreeEq(reify cGSV3, rhsT) = TreeEq(reify cGSV3, reify cGSV3).
    stepB : Deriv hyp (eqn (ap2 TreeEq (reify cGSV3) (reify cGSV3)) poo)
    stepB = ruleTrans (ruleSym (congR TreeEq (reify cGSV3) diagFTargetV3)) stepA

    -- treeEqSelf: TreeEq(X, X) = O.
    selfEq : Deriv hyp (eqn (ap2 TreeEq (reify cGSV3) (reify cGSV3)) O)
    selfEq = treeEqSelf (reify cGSV3)

    -- Combine: O = poo.
  in ruleTrans (ruleSym selfEq) stepB
-}
