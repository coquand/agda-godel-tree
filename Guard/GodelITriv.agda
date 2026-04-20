{-# OPTIONS --safe --without-K --exact-split #-}

-- Classical Gödel I for the Triv-based diagonal.
--
-- Statement:  Deriv Triv gsTriv  ->  Deriv Triv (trueT = falseT).
-- Contrapositive:  Consistent Triv  ->  Triv ⊬ gsTriv.
--
-- Unlike godelIDerivV3 (which was mere exhibition because gs_V3 had
-- v_2 free and therefore a trivially-refutable closed instance),
-- gsTriv has no such free evaluator-hCode slot: its thmT hCode is
-- baked in as the closed code of Triv, so the universal is not
-- trivially refutable.  The non-trivial argument uses thm14EV3
-- (DC1 reflection) to construct enc_G from the hypothetical
-- derivation  Deriv Triv gsTriv , then instantiates gsTriv at
-- x_0 := enc_G, rewrites via corr, and applies treeEqSelf.

module Guard.GodelITriv where

open import Guard.Base
open import Guard.Term
open import Guard.Step
open import Guard.StepReduce
open import Guard.SubstCorrect
open import Guard.SubstTForCorrect
open import Guard.SubstOp using (substOp ; substOpEquiv)
open import Guard.ThFun using (codeEqn)
open import Guard.ThFunTForV3 using (thmT)
open import Guard.SubstTForPrecompTriv
open import Guard.TreeEqSelf using (treeEqSelf)
open import Guard.Thm14EV3 using (ProofE3 ; thm14EV3 ; encT ; corr)
open import Guard.Nelson.SubstReify using (substReify)

private
  v1 : Nat ; v1 = suc zero
  v11' : Nat ; v11' = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))
  v12' : Nat ; v12' = suc v11'
  tgtT : Tree ; tgtT = natCode v1
  poo : Term ; poo = ap2 Pair O O

  trueT : Term ; trueT = O
  falseT : Term ; falseT = poo

------------------------------------------------------------------------
-- Diagonal identity for the Triv template.

diagFTargetTriv : {hyp : Equation} ->
  Deriv hyp (eqn (ap2 substOp (ap2 Pair (reify crTCTriv) (reify (natCode v1)))
                              (reify templateCodeTriv))
                 (reify cGSTriv))
diagFTargetTriv {hyp} =
  let
    combined : Deriv hyp (eqn (ap1 (closedSubstTFor (reify crTCTriv) (reify tgtT))
                                (ap2 Pair (reify codeLhsTTriv) (reify codePoo)))
                              (reify (codedSubst crTCTriv tgtT
                                        (nd codeLhsTTriv codePoo))))
    combined = closedSTFNd crTCTriv tgtT codeLhsTTriv codePoo
                 codeLhsTTrivNeqTagVar codeLhsTTrivNotVar
                 (lhsTTrivSTF crTCTriv) (pooSTF crTCTriv)

    combinedTC : Deriv hyp (eqn (ap1 (closedSubstTFor (reify crTCTriv) (reify tgtT))
                                  (reify templateCodeTriv))
                                (reify (codedSubst crTCTriv tgtT templateCodeTriv)))
    combinedTC = eqSubst (\tc -> Deriv hyp
                            (eqn (ap1 (closedSubstTFor (reify crTCTriv) (reify tgtT))
                                   (reify tc))
                                 (reify (codedSubst crTCTriv tgtT tc))))
                         (eqSym templateCodeTrivForm) combined

    fp : Eq (codedSubst crTCTriv tgtT templateCodeTriv) cGSTriv
    fp = eqTrans
           (eqSubst (\tc -> Eq (codedSubst crTCTriv tgtT tc)
                               (codedSubst crTCTriv tgtT (nd codeLhsTTriv codePoo)))
                    (eqSym templateCodeTrivForm) refl)
           (eqTrans
             (codedSubstNd crTCTriv tgtT codeLhsTTriv codePoo codeLhsTTrivNotVar)
             (eqSym cGSisCSTriv))

    combinedCGS : Deriv hyp (eqn (ap1 (closedSubstTFor (reify crTCTriv) (reify tgtT))
                                  (reify templateCodeTriv))
                                (reify cGSTriv))
    combinedCGS = eqSubst (\c -> Deriv hyp
                            (eqn (ap1 (closedSubstTFor (reify crTCTriv) (reify tgtT))
                                   (reify templateCodeTriv))
                                 (reify c)))
                          fp combinedTC

    step1 : Deriv hyp (eqn (ap2 substOp (ap2 Pair (reify crTCTriv) (reify (natCode v1)))
                                        (reify templateCodeTriv))
                           (ap1 (closedSubstTFor (reify crTCTriv) (reify (natCode v1)))
                                (reify templateCodeTriv)))
    step1 = substOpEquiv (reify crTCTriv) (reify (natCode v1)) templateCodeTriv
  in ruleTrans step1 combinedCGS

------------------------------------------------------------------------
-- Classical Gödel I.
--
-- From any derivation  d : Deriv Triv gsTriv , construct a derivation
--   Deriv Triv (trueT = falseT).
--
-- Equivalently (contrapositive): if Triv is consistent, then Triv does
-- not prove gsTriv.  Unlike godelIDerivV3, this is not mere
-- exhibition: the diagonal instance that collapses the TreeEq
-- uses  enc_G  built from  d  via thm14EV3 — no  enc_G  exists
-- until  d  is supplied.  So the conclusion genuinely depends on
-- the premise.

godelITriv : Deriv Triv gsTriv -> Deriv Triv (eqn trueT falseT)
godelITriv d = ruleTrans (ruleSym selfEq) stepB
  where
  -- Apply thm14EV3 (DC1) to the hypothetical derivation.
  pe : ProofE3 Triv gsTriv
  pe = thm14EV3 d

  enc : Term
  enc = encT pe

  -- corr pe : Deriv hyp (ap1 (thmT (reify (codeEqn Triv))) enc = reify (codeEqn gsTriv))
  -- Bridge  codeEqn Triv = trivC  and  codeEqn gsTriv = cGSTriv  via
  -- cGSdefTriv.  (codeEqn Triv = trivC is definitional by the abstract
  -- definition  trivC = codeEqn Triv .)
  corrPf : Deriv Triv (eqn (ap1 (thmT trivCT) enc) (reify cGSTriv))
  corrPf =
    eqSubst (\t -> Deriv Triv (eqn (ap1 (thmT t) enc) (reify cGSTriv)))
      (eqSym trivCTDef)
      (eqSubst (\c -> Deriv Triv (eqn (ap1 (thmT (reify (codeEqn Triv))) enc) (reify c)))
        (eqSym cGSdefTriv)
        (corr pe))

  -- Three ruleInst's: v_11' ↦ reify crTCTriv, v_12' ↦ reify (natCode v_1), 0 ↦ enc.
  d1 : Deriv Triv (substEq v11' (reify crTCTriv) gsTriv)
  d1 = ruleInst v11' (reify crTCTriv) d

  d2 : Deriv Triv (substEq v12' (reify (natCode v1))
                    (substEq v11' (reify crTCTriv) gsTriv))
  d2 = ruleInst v12' (reify (natCode v1)) d1

  d3 : Deriv Triv (substEq zero enc
                    (substEq v12' (reify (natCode v1))
                      (substEq v11' (reify crTCTriv) gsTriv)))
  d3 = ruleInst zero enc d2

  -- Target form: the expected closed instantiation.
  lhsT : Term
  lhsT = ap1 (thmT trivCT) enc

  rhsT : Term
  rhsT = ap2 substOp (ap2 Pair (reify crTCTriv) (reify (natCode v1)))
                     (reify templateCodeTriv)

  expected : Equation
  expected = eqn (ap2 TreeEq lhsT rhsT) poo

  -- The subst-chain reduces to the expected form, because all
  -- substituted values are closed reified-tree Terms.
  substsAreIdentities :
    Eq (eqn (ap2 TreeEq (ap1 (thmT trivCT) enc)
              (ap2 substOp
                (ap2 Pair
                  (subst zero enc (subst v12' (reify (natCode v1)) (reify crTCTriv)))
                  (subst zero enc (reify (natCode v1))))
                (reify templateCodeTriv)))
            poo)
       expected
  substsAreIdentities =
    eqCong2 (\X11' X12' ->
               eqn (ap2 TreeEq (ap1 (thmT trivCT) enc)
                               (ap2 substOp (ap2 Pair X11' X12')
                                            (reify templateCodeTriv)))
                   poo)
      (eqTrans (eqCong (subst zero enc)
                       (substReify v12' (reify (natCode v1)) crTCTriv))
               (substReify zero enc crTCTriv))
      (substReify zero enc (natCode v1))

  d3Conv : Deriv Triv expected
  d3Conv =
    eqSubst (\eq -> Deriv Triv eq)
      (eqTrans (fullyInstGSTriv enc (reify crTCTriv) (reify (natCode v1)))
               substsAreIdentities)
      d3

  -- Rewrite LHS using corrPf:  ap1 (thmT trivCT) enc = reify cGSTriv.
  stepA : Deriv Triv (eqn (ap2 TreeEq (reify cGSTriv) rhsT) poo)
  stepA = ruleTrans (ruleSym (congL TreeEq rhsT corrPf)) d3Conv

  -- Rewrite RHS using diagFTargetTriv:  rhsT = reify cGSTriv.
  stepB : Deriv Triv (eqn (ap2 TreeEq (reify cGSTriv) (reify cGSTriv)) poo)
  stepB = ruleTrans (ruleSym (congR TreeEq (reify cGSTriv) diagFTargetTriv)) stepA

  -- treeEqSelf: TreeEq(c, c) = O.
  selfEq : Deriv Triv (eqn (ap2 TreeEq (reify cGSTriv) (reify cGSTriv)) O)
  selfEq = treeEqSelf (reify cGSTriv)

------------------------------------------------------------------------
-- Contrapositive form: if Triv is consistent, Triv does not prove gsTriv.

godelITrivContra : Consistent Triv ->
                   Deriv Triv gsTriv ->
                   Empty
godelITrivContra con d = con (godelITriv d)
