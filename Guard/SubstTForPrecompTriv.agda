{-# OPTIONS --safe --without-K --exact-split #-}

-- Diagonal machinery for a classical Gödel-I argument with a
-- fixed, trivially-consistent hypothesis  Triv = eqn O O .
--
-- Parallels Guard.SubstTForPrecompV3 but with Triv baked in instead
-- of a free variable x_2.  That change makes the template's internal
-- consistency statement mean "Triv does not prove gs_Triv" rather
-- than "the sentence's own evaluator hCode does not equal anything"
-- --- which restores the classical reading of the Gödel sentence.

module Guard.SubstTForPrecompTriv where

open import Guard.Base
open import Guard.Term
open import Guard.Step
open import Guard.SubstCorrect
open import Guard.SubstTForCorrect
open import Guard.SubstOp using (substOp ; substOpEquiv)
open import Guard.ThFun using (codeEqn)
open import Guard.ThFunTForV3 using (thmT)

private
  v1 : Nat ; v1 = suc zero
  tgtT : Tree ; tgtT = natCode v1
  poo : Term ; poo = ap2 Pair O O
  v11' : Nat ; v11' = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))
  v12' : Nat ; v12' = suc v11'

abstract
  -- A trivially-consistent hypothesis.  Derivations from  Triv = eqn O O
  -- coincide with plain structural derivations extended by the
  -- tautological axiom O = O ; in particular Consistent(Triv) is
  -- equivalent to consistency of the base equational system.
  Triv : Equation
  Triv = eqn O O

  trivC : Tree
  trivC = codeEqn Triv

  trivCT : Term
  trivCT = reify trivC

  trivCDef : Eq trivC (codeEqn Triv)
  trivCDef = refl

  trivCTDef : Eq trivCT (reify (codeEqn Triv))
  trivCTDef = refl

  -- Template LHS: the free variable v_2 of V3 is replaced by the
  -- closed term  trivCT  (the reified code of Triv).
  lhsTermTriv : Term
  lhsTermTriv = ap2 TreeEq (ap1 (thmT trivCT) (var zero))
                           (ap2 substOp (ap2 Pair (var v11') (var v12')) (var v1))

  codeLhsTTriv : Tree
  codeLhsTTriv = code lhsTermTriv

  codePoo : Tree
  codePoo = code poo

  codeLhsTTrivNeqTagVar : {hyp : Equation} ->
    Deriv hyp (eqn (ap2 TreeEq (reify codeLhsTTriv) (reify tagVar)) poo)
  codeLhsTTrivNeqTagVar = codeNeqTagVarGen lhsTermTriv

  codeLhsTTrivNotVar : Eq (treeEq codeLhsTTriv tagVar) false
  codeLhsTTrivNotVar = codeNotVar lhsTermTriv

  pooSTF : (replT : Tree) -> {hyp : Equation} ->
    Deriv hyp (eqn (ap1 (closedSubstTFor (reify replT) (reify tgtT)) (reify codePoo))
                   (reify (codedSubst replT tgtT codePoo)))
  pooSTF replT = closedSTFCode replT tgtT poo

  csLhsTTriv : (r : Term) ->
    Eq (codedSubst (code r) tgtT codeLhsTTriv) (code (subst v1 r lhsTermTriv))
  csLhsTTriv r = csCorrect r v1 lhsTermTriv

  csPoo : (r : Term) ->
    Eq (codedSubst (code r) tgtT codePoo) (code (subst v1 r poo))
  csPoo r = csCorrect r v1 poo

  lhsTTrivSTF : (replT : Tree) -> {hyp : Equation} ->
    Deriv hyp (eqn (ap1 (closedSubstTFor (reify replT) (reify tgtT)) (reify codeLhsTTriv))
                   (reify (codedSubst replT tgtT codeLhsTTriv)))
  lhsTTrivSTF replT = closedSTFCode replT tgtT lhsTermTriv

  templateCodeTriv : Tree
  templateCodeTriv = nd codeLhsTTriv codePoo

  templateCodeTrivForm : Eq templateCodeTriv (nd codeLhsTTriv codePoo)
  templateCodeTrivForm = refl

  crTCTriv : Tree
  crTCTriv = code (reify templateCodeTriv)

  templateTriv : Equation
  templateTriv = eqn lhsTermTriv poo

  -- The V3-style Gödel sentence for the Triv hypothesis.
  gsTriv : Equation
  gsTriv = substEq v1 (reify templateCodeTriv) templateTriv

  cGSTriv : Tree
  cGSTriv = codeEqn gsTriv

  cGSisCSTriv : Eq cGSTriv (nd (codedSubst crTCTriv tgtT codeLhsTTriv)
                              (codedSubst crTCTriv tgtT codePoo))
  cGSisCSTriv = eqSym
    (eqTrans (eqCong2 nd (csLhsTTriv (reify templateCodeTriv))
                         (csPoo (reify templateCodeTriv)))
             (eqSym (codedSubstNd crTCTriv tgtT codeLhsTTriv codePoo codeLhsTTrivNotVar)))

  cGSdefTriv : Eq cGSTriv (codeEqn gsTriv)
  cGSdefTriv = refl

  cstfTriv : Fun1
  cstfTriv = closedSubstTFor (reify crTCTriv) (reify (natCode v1))

  cstfTrivDef : Eq cstfTriv (closedSubstTFor (reify crTCTriv) (reify (natCode v1)))
  cstfTrivDef = refl

  -- Expanded form: gsTriv unfolded once so its substitution chain
  -- reduces quickly.  Only v_1 has been substituted; v_11', v_12', v_0
  -- remain.
  gsTrivForm : Eq gsTriv
    (eqn (ap2 TreeEq (ap1 (thmT trivCT) (var zero))
                     (ap2 substOp (ap2 Pair (var v11') (var v12'))
                                  (reify templateCodeTriv)))
         poo)
  gsTrivForm = refl

  -- Schematic substitution lemma for thmT applied to the closed term
  -- trivCT: substitution on any variable is identity here.  (trivCT
  -- is the reified code of a closed equation; no free variables.)
  substThmTTriv : (x : Nat) (r : Term) ->
    Eq (substF1 x r (thmT trivCT)) (thmT trivCT)
  substThmTTriv x r = refl

  -- Fused three-step substEq lemma for the Gödel I ruleInst chain.
  fullyInstGSTriv : (X0 X11 X12 : Term) ->
    Eq (substEq zero X0
         (substEq v12' X12
           (substEq v11' X11 gsTriv)))
       (eqn (ap2 TreeEq (ap1 (thmT trivCT) X0)
                        (ap2 substOp
                             (ap2 Pair (subst zero X0 (subst v12' X12 X11))
                                       (subst zero X0 X12))
                             (reify templateCodeTriv)))
            poo)
  fullyInstGSTriv X0 X11 X12 = refl
