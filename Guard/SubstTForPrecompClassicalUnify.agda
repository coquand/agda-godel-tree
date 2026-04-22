{-# OPTIONS --safe --without-K --exact-split #-}

-- Classical-form diagonal for Gödel I.
--
-- Compared with Guard.SubstTForPrecompTriv:
--   * The template's substOp first Pair arg is now  (ap1 cor (var v_1)) ,
--     not  (var v_11') .  After substEq v_1 := (reify N_CR), this
--     reduces via  corOfReify N_CR  to  reify crTC_CR , exactly what
--     the diagonal identity needs.
--   * The template has ONLY v_0 and v_1 free (proof slot and self-code
--     slot).  After substEq v_1, the Gödel sentence has only v_0 free —
--     matching Ryan's single-free-variable classical form.
--
-- No new primitives: cor is plain Rec-based.

module Guard.SubstTForPrecompClassicalUnify where

open import Guard.Base
open import Guard.Term
open import Guard.Formula
open import Guard.DerivF
open import Guard.SubstCorrect
open import Guard.SubstTForCorrectUnify
open import Guard.SubstOpUnify using (substOp ; substOpEquiv)
open import Guard.ThFun using (codeEqn)
open import Guard.ThFunTForV3Unify using (thmT)
open import Guard.CodeOfReify using (cor)

private
  v1 : Nat ; v1 = suc zero
  tgtT : Tree ; tgtT = natCode v1

abstract
  -- Trivially-consistent hypothesis (same as Guard.SubstTForPrecompTriv).
  Triv : Equation
  Triv = eqn O O

  trivC : Tree
  trivC = codeEqn Triv

  trivCT : Term
  trivCT = reify trivC

  trivCTDef : Eq trivCT (reify (codeEqn Triv))
  trivCTDef = refl

  -- Triv is closed: substitution at any (x, t) is identity on Triv.
  -- Used to discharge the ruleInst Hilbert-Bernays side condition at
  -- hyp = Triv (the standard sound use of variable instantiation).
  trivClosed : (x : Nat) (t : Term) -> Eq (substEq x t Triv) Triv
  trivClosed x t = refl

  -- The NEW template LHS: substOp's first Pair arg is  (ap1 cor (var v_1)) .
  lhsTermCR : Term
  lhsTermCR = ap2 TreeEq (ap1 (thmT trivCT) (var zero))
                         (ap2 substOp
                           (ap2 Pair (ap1 cor (var v1)) (reify (natCode v1)))
                           (var v1))

  codeLhsTCR : Tree
  codeLhsTCR = code lhsTermCR

  codePoo : Tree
  codePoo = code falseT

  codeLhsTCRNeqTagVar :
    Deriv (eqF (ap2 TreeEq (reify codeLhsTCR) (reify tagVar)) falseT)
  codeLhsTCRNeqTagVar = codeNeqTagVarGen lhsTermCR

  codeLhsTCRNotVar : Eq (treeEq codeLhsTCR tagVar) false
  codeLhsTCRNotVar = codeNotVar lhsTermCR

  falseTSTF : (replT : Tree) ->
    Deriv (eqF (ap1 (closedSubstTFor (reify replT) (reify tgtT)) (reify codePoo))
                   (reify (codedSubst replT tgtT codePoo)))
  falseTSTF replT = closedSTFCode replT tgtT falseT

  csLhsTCR : (r : Term) ->
    Eq (codedSubst (code r) tgtT codeLhsTCR) (code (subst v1 r lhsTermCR))
  csLhsTCR r = csCorrect r v1 lhsTermCR

  csPoo : (r : Term) ->
    Eq (codedSubst (code r) tgtT codePoo) (code (subst v1 r falseT))
  csPoo r = csCorrect r v1 falseT

  lhsTCRSTF : (replT : Tree) ->
    Deriv (eqF (ap1 (closedSubstTFor (reify replT) (reify tgtT)) (reify codeLhsTCR))
                   (reify (codedSubst replT tgtT codeLhsTCR)))
  lhsTCRSTF replT = closedSTFCode replT tgtT lhsTermCR

  templateCodeCR : Tree
  templateCodeCR = nd codeLhsTCR codePoo

  templateCodeCRForm : Eq templateCodeCR (nd codeLhsTCR codePoo)
  templateCodeCRForm = refl

  crTCCR : Tree
  crTCCR = code (reify templateCodeCR)

  crTCCRDef : Eq crTCCR (code (reify templateCodeCR))
  crTCCRDef = refl

  templateCR : Equation
  templateCR = eqn lhsTermCR falseT

  gsCR : Equation
  gsCR = substEq v1 (reify templateCodeCR) templateCR

  cGSCR : Tree
  cGSCR = codeEqn gsCR

  cGSisCSCR : Eq cGSCR (nd (codedSubst crTCCR tgtT codeLhsTCR)
                          (codedSubst crTCCR tgtT codePoo))
  cGSisCSCR = eqSym
    (eqTrans (eqCong2 nd (csLhsTCR (reify templateCodeCR))
                         (csPoo (reify templateCodeCR)))
             (eqSym (codedSubstNd crTCCR tgtT codeLhsTCR codePoo codeLhsTCRNotVar)))

  cGSdefCR : Eq cGSCR (codeEqn gsCR)
  cGSdefCR = refl

  -- Expanded form of gsCR (v_1 substituted).  Note the  ap1 cor (reify templateCodeCR)
  -- slot where the free  var v_1  used to be.
  gsCRForm : Eq gsCR
    (eqn (ap2 TreeEq (ap1 (thmT trivCT) (var zero))
                     (ap2 substOp
                       (ap2 Pair (ap1 cor (reify templateCodeCR)) (reify (natCode v1)))
                       (reify templateCodeCR)))
         falseT)
  gsCRForm = refl

  substThmTCRFact : (x : Nat) (r : Term) ->
    Eq (substF1 x r (thmT trivCT)) (thmT trivCT)
  substThmTCRFact x r = refl

  substCorFact : (x : Nat) (r : Term) ->
    Eq (substF1 x r cor) cor
  substCorFact x r = refl

  -- The substEq chain for the Gödel I argument.  Only two variables
  -- remain free in gsCR: v_0 and (implicitly) v_1 is already
  -- substituted.  Actually v_1 was already substituted (gsCR has no
  -- free v_1).  So this is just  substEq zero X  on the closed form.
  subst0GSCR : (X0 : Term) ->
    Eq (substEq zero X0 gsCR)
       (eqn (ap2 TreeEq (ap1 (thmT trivCT) X0)
                        (ap2 substOp
                          (ap2 Pair (ap1 cor (reify templateCodeCR))
                                    (reify (natCode v1)))
                          (reify templateCodeCR)))
            falseT)
  subst0GSCR X0 = refl
