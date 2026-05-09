{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA2.Thm14SubLemma
--
-- Definition 12 line 2 stated as a parametric lemma, SHAPE-FREE:
--
--   given  Deriv (thmT y = codeP) ,
--   derive  Deriv (thmT (sb-encoded-tree-with-proof-index-y) =
--                  subT (Pair (reify (code (var n))) tT) codeP).
--
-- Built on top of  BRA2.Thm.ThmT.thmTDispRuleInst_param  (which is
-- itself shape-free under the new encRuleInst layout — see the
-- 2026-05-02 refactor in BRA/Thm/Parts/RuleInst.agda) by transitively
-- rewriting the result's  ap1 thmT y  to  codeP  via the supplied
-- hypothesis.  No new axioms; no body_ruleInst / cascade surgery.
--
-- The new encRuleInst payload places the open proof-index  y  at the
-- OUTER Snd position, with the closed (varCode, tCode) pair at inner
-- Fst.  thmT distributes through this Pair without any shape
-- obligation on  y , parametrically in y .
--
-- Soundification status (2026-05-03): when the body_ruleInst eventually
-- swaps to the verifying body_ruleInst_v (BRA2.SoundRuleInstProto), this
-- module's  thmTSubLemma  signature will need an additional Pair-shape
-- witness  Deriv (codeP = ap2 Pair fp sp) .  The auxiliary
-- subTOfCodeFormulaImp_isPair  helper in this file derives that
-- witness for the common case where codeP = subT(args, reify(codeFormula
-- (Q imp R))) .  Still missing: a "chained" version for nested subT
-- forms in Th14Step3 Layer 2 / Th14StepHPre Layer 1.

module BRA2.Thm14SubLemma where

open import BRA2.Base
open import BRA2.Term
open import BRA2.Formula
open import BRA2.DerivThreshold

open import BRA2.SubT using (subT ; subTDef)
open import BRA2.CodeCommutes using (codeCommutesFormula)
open import BRA2.SoundRuleInstVProof using (codeFormulaPairShape)

open import BRA2.Thm.ThmT
  using ( thmT
        ; thmTDispRuleInst_param
        ; tagCode_ruleInst )

----------------------------------------------------------------------
-- thmTSubLemma : the parametric Def 12 line 2 (sb-clause) for thmT.
--
-- Inputs:
--   * n      : Nat       -- the variable index being substituted.
--   * tT     : Term      -- the substituent (a Term, may be open).
--   * y      : Term      -- the proof-index Term (may be open;
--                          NO shape obligation under the new layout).
--   * codeP  : Term      -- the closed encoded conclusion of the
--                          proof referenced by y (under hypothesis).
--   * d_h    : Deriv (thmT y = codeP)   -- the hypothesis.
--
-- Output:
--   thmT (Pair tagCode_ruleInst (Pair (Pair varCode tT) y))
--     = subT (Pair varCode tT) codeP

thmTSubLemma :
  (n : Nat) (tT y codeP fstPart sndPart : Term) ->
  Deriv (atomic (eqn (ap1 thmT y) codeP)) ->
  -- NEW dh (load-bearing for verifying body_ruleInst):
  -- codeP = Pair fstPart sndPart.  The Pair-shape is derivable from
  -- codeFormulaPairShape when codeP = reify(codeFormula F), or from
  -- subTOfCodeFormulaImp_isPair when codeP is a subT-form on a
  -- reify(codeFormula (Q imp R)), etc.
  Deriv (atomic (eqn codeP (ap2 Pair fstPart sndPart))) ->
  Deriv (atomic (eqn
    (ap1 thmT (ap2 Pair tagCode_ruleInst
                (ap2 Pair (ap2 Pair (reify (code (var n))) tT) y)))
    (ap2 subT (ap2 Pair (reify (code (var n))) tT) codeP)))
thmTSubLemma n tT y codeP fstPart sndPart d_h dh =
  let
      varCodeT : Term
      varCodeT = reify (code (var n))

      -- Combine d_h and dh to get  thmT y = Pair fstPart sndPart .
      dhCombined : Deriv (atomic (eqn (ap1 thmT y) (ap2 Pair fstPart sndPart)))
      dhCombined = ruleTrans d_h dh

      -- Step 1: dispatch via thmTDispRuleInst_param (with inner check).
      -- Result has  ap1 thmT y  on the RHS (not yet codeP).
      step1 :
        Deriv (atomic (eqn
          (ap1 thmT (ap2 Pair tagCode_ruleInst
                      (ap2 Pair (ap2 Pair varCodeT tT) y)))
          (ap2 subT (ap2 Pair varCodeT tT) (ap1 thmT y))))
      step1 = thmTDispRuleInst_param n tT y fstPart sndPart dhCombined

      -- Step 2: rewrite  ap1 thmT y  to  codeP  via the hypothesis d_h .
      step2 :
        Deriv (atomic (eqn
          (ap2 subT (ap2 Pair varCodeT tT) (ap1 thmT y))
          (ap2 subT (ap2 Pair varCodeT tT) codeP)))
      step2 = congR subT (ap2 Pair varCodeT tT) d_h

  in ruleTrans step1 step2

----------------------------------------------------------------------
-- subTOfCodeFormulaImp_isPair : Pair-shape witness for subT applied to
-- a reified codeFormula of an implication formula (Q imp R).
--
-- Auxiliary infrastructure for the in-progress soundification of
-- body_ruleInst (BRA2.SoundRuleInstProto / BRA2.SoundRuleInstVProof).
-- Currently UNUSED by thmTSubLemma (which retains the legacy non-
-- verifying signature) but kept here so the eventual swap can reuse it.
--
-- Mathematically:
--   subT (Pair (reify (code (var n))) (reify codeT)) (reify (codeFormula (Q imp R)))
--     = reify (codedSubst codeT (code (var n)) (codeFormula (Q imp R)))   [subTDef]
--     = reify (nd (codedSubst codeT (code (var n)) tagImp)
--                 (codedSubst codeT (code (var n)) (nd (codeFormula Q) (codeFormula R))))
--                                                                   [codedSubst red, false branch]
--     = ap2 Pair fp sp                                              [reify of nd]
--
-- The codedSubst reduction is definitional: codeFormula (Q imp R)
-- starts with tagImp, treeEq (code (var n)) (nd tagImp ...) is
-- statically false (tagVar != tagImp), so the codedSubst falls into
-- the nd-branch.

subTOfCodeFormulaImp_isPair :
  (n : Nat) (codeT : Term) -> IsValue codeT -> (Q R : Formula) ->
  Sigma Term (\ fp -> Sigma Term (\ sp ->
    Deriv (atomic (eqn
      (ap2 subT (ap2 Pair (reify (code (var n))) (reify codeT))
                  (reify (codeFormula (Q imp R))))
      (ap2 Pair fp sp)))))
subTOfCodeFormulaImp_isPair n codeT cT Q R =
  let
      fp : Term
      fp = reify (codedSubst codeT (code (var n)) tagImp)
      sp : Term
      sp = reify (codedSubst codeT (code (var n))
                              (nd (codeFormula Q) (codeFormula R)))

      eA : Deriv (atomic (eqn
        (ap2 subT (ap2 Pair (reify (code (var n))) (reify codeT))
                    (reify (codeFormula (Q imp R))))
        (reify (codedSubst codeT (code (var n)) (codeFormula (Q imp R))))))
      eA = subTDef n codeT cT (codeFormula (Q imp R)) (codeFormula_isValue (Q imp R))

      eB : Deriv (atomic (eqn
        (reify (codedSubst codeT (code (var n)) (codeFormula (Q imp R))))
        (ap2 Pair fp sp)))
      eB = axRefl (ap2 Pair fp sp)
  in mkSigma fp (mkSigma sp (ruleTrans eA eB))

----------------------------------------------------------------------
-- subToFormulaBridge : identify subT-of-codeFormula with
-- codeFormula-of-substF, when the substituent has the canonical form
-- `reify (code r)` for some Term r.  Required by Th14Step3 Layer 2's
-- dh derivation, where the inner codeP is itself a subT-form on a
-- codeFormula and must be flattened to a `reify(codeFormula F)` form
-- before subTOfCodeFormulaImp_isPair can apply on the outer subT.
--
-- Mathematically:
--   subT (Pair (reify (code (var n))) (reify (code r))) (reify (codeFormula P))
--     = reify (codedSubst (code r) (code (var n)) (codeFormula P))   [subTDef]
--     = reify (codeFormula (substF n r P))                           [codeCommutesFormula, swapped]

subToFormulaBridge :
  (n : Nat) (r : Term) (P : Formula) ->
  Deriv (atomic (eqn
    (ap2 subT (ap2 Pair (reify (code (var n))) (reify (code r)))
                (reify (codeFormula P)))
    (reify (codeFormula (substF n r P)))))
subToFormulaBridge n r P =
  let eA : Deriv (atomic (eqn
                    (ap2 subT (ap2 Pair (reify (code (var n))) (reify (code r)))
                                (reify (codeFormula P)))
                    (reify (codedSubst (code r) (code (var n)) (codeFormula P)))))
      eA = subTDef n (code r) (code_isValue r) (codeFormula P) (codeFormula_isValue P)
      eqStep : Eq (codedSubst (code r) (code (var n)) (codeFormula P))
                  (codeFormula (substF n r P))
      eqStep = eqSym (codeCommutesFormula n r P)
      eB : Deriv (atomic (eqn
                    (reify (codedSubst (code r) (code (var n)) (codeFormula P)))
                    (reify (codeFormula (substF n r P)))))
      eB = eqSubst (\ T -> Deriv (atomic (eqn
                            (reify (codedSubst (code r) (code (var n)) (codeFormula P)))
                            (reify T))))
                    eqStep
                    (axRefl (reify (codedSubst (code r) (code (var n)) (codeFormula P))))
  in ruleTrans eA eB
