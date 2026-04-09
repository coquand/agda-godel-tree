{-# OPTIONS --safe --without-K --exact-split #-}

-- Fast variant of SubstTForPrecomp without instForm2.
--
-- The original SubstTForPrecomp.agda contains an `instForm2 = refl`
-- declaration that takes ~108 seconds to type-check, because it forces
-- Agda to materialize and traverse `reify crTC` (~400K Term nodes).
--
-- This file contains all the same abstract definitions but omits
-- instForm2.  Downstream files that go via the schematic
-- substitution lemmas (Guard/Nelson/SubstReify, SubstTForClose,
-- ThFunTForSubst, InstForm) do not need instForm2.
--
-- The original Guard.SubstTForPrecomp is preserved unchanged.

module Guard.SubstTForPrecompFast where

open import Guard.Base
open import Guard.Term
open import Guard.Step
open import Guard.SubstCorrect
open import Guard.SubstTFor using (substTFor)
open import Guard.SubstTForCorrect
open import Guard.ThFun using (codeEqn)
open import Guard.ThFunTFor using (thFunTFor)

private
  v1 : Nat ; v1 = suc zero
  tgtT : Tree ; tgtT = natCode v1
  poo : Term ; poo = ap2 Pair O O

abstract
  thfCode : Tree
  thfCode = codeF1 thFunTFor

  stfCode : Tree
  stfCode = codeF1 substTFor

  thfCodeDef : Eq thfCode (codeF1 thFunTFor)
  thfCodeDef = refl

  stfCodeDef : Eq stfCode (codeF1 substTFor)
  stfCodeDef = refl

  thfCodeNeqTagVar : {hyp : Equation} ->
    Deriv hyp (eqn (ap2 TreeEq (reify thfCode) (reify tagVar)) poo)
  thfCodeNeqTagVar = codeF1NeqTagVar thFunTFor

  thfCodeNotVar : Eq (treeEq thfCode tagVar) false
  thfCodeNotVar = codeF1NotVar thFunTFor

  stfCodeNeqTagVar : {hyp : Equation} ->
    Deriv hyp (eqn (ap2 TreeEq (reify stfCode) (reify tagVar)) poo)
  stfCodeNeqTagVar = codeF1NeqTagVar substTFor

  stfCodeNotVar : Eq (treeEq stfCode tagVar) false
  stfCodeNotVar = codeF1NotVar substTFor

  thfSTF : (replT : Tree) -> {hyp : Equation} ->
    Deriv hyp (eqn (ap1 (closedSubstTFor (reify replT) (reify tgtT)) (reify thfCode))
                   (reify (codedSubst replT tgtT thfCode)))
  thfSTF replT = closedSTFF1 replT tgtT thFunTFor

  stfSTF : (replT : Tree) -> {hyp : Equation} ->
    Deriv hyp (eqn (ap1 (closedSubstTFor (reify replT) (reify tgtT)) (reify stfCode))
                   (reify (codedSubst replT tgtT stfCode)))
  stfSTF replT = closedSTFF1 replT tgtT substTFor

  csThF : (r : Term) ->
    Eq (codedSubst (code r) tgtT thfCode) (codeF1 (substF1 v1 r thFunTFor))
  csThF r = csF1Correct r v1 thFunTFor

  csStF : (r : Term) ->
    Eq (codedSubst (code r) tgtT stfCode) (codeF1 (substF1 v1 r substTFor))
  csStF r = csF1Correct r v1 substTFor

  thfNoV1 : (r : Term) -> Eq (substF1 v1 r thFunTFor) thFunTFor
  thfNoV1 r = refl

  stfNoV1 : (r : Term) -> Eq (substF1 v1 r substTFor) substTFor
  stfNoV1 r = refl

  -- code lhsT and code poo (computed once)
  codeLhsT : Tree
  codeLhsT = code (ap2 TreeEq (ap1 thFunTFor (var zero)) (ap1 substTFor (var v1)))

  codePoo : Tree
  codePoo = code poo

  -- Structural decomposition of codeLhsT in terms of abstract thfCode/stfCode
  codeLhsTForm : Eq codeLhsT (nd tagAp2 (nd (codeF2 TreeEq) (nd (nd tagAp1 (nd thfCode (nd tagVar lf))) (nd tagAp1 (nd stfCode (nd tagVar (natCode v1)))))))
  codeLhsTForm = refl

  codeLhsTNeqTagVar : {hyp : Equation} ->
    Deriv hyp (eqn (ap2 TreeEq (reify codeLhsT) (reify tagVar)) poo)
  codeLhsTNeqTagVar = codeNeqTagVarGen (ap2 TreeEq (ap1 thFunTFor (var zero)) (ap1 substTFor (var v1)))

  codeLhsTNotVar : Eq (treeEq codeLhsT tagVar) false
  codeLhsTNotVar = codeNotVar (ap2 TreeEq (ap1 thFunTFor (var zero)) (ap1 substTFor (var v1)))

  -- closedSTFCode for poo (bridges codePoo)
  pooSTF : (replT : Tree) -> {hyp : Equation} ->
    Deriv hyp (eqn (ap1 (closedSubstTFor (reify replT) (reify tgtT)) (reify codePoo))
                   (reify (codedSubst replT tgtT codePoo)))
  pooSTF replT = closedSTFCode replT tgtT poo

  -- csCorrect for lhsT
  csLhsT : (r : Term) ->
    Eq (codedSubst (code r) tgtT codeLhsT) (code (subst v1 r (ap2 TreeEq (ap1 thFunTFor (var zero)) (ap1 substTFor (var v1)))))
  csLhsT r = csCorrect r v1 (ap2 TreeEq (ap1 thFunTFor (var zero)) (ap1 substTFor (var v1)))

  csPoo : (r : Term) ->
    Eq (codedSubst (code r) tgtT codePoo) (code (subst v1 r poo))
  csPoo r = csCorrect r v1 poo

  -- Template code and Godel sentence (all computed once from concrete data)
  templateCode : Tree
  templateCode = nd codeLhsT codePoo

  templateCodeForm : Eq templateCode (nd codeLhsT codePoo)
  templateCodeForm = refl

  crTC : Tree
  crTC = code (reify templateCode)

  godelSentence : Equation
  godelSentence = substEq v1 (reify templateCode) (eqn (ap2 TreeEq (ap1 thFunTFor (var zero)) (ap1 substTFor (var v1))) poo)

  cGS : Tree
  cGS = codeEqn godelSentence

  -- cGS in terms of codedSubst (the fixed-point decomposition)
  cGSisCS : Eq cGS (nd (codedSubst crTC tgtT codeLhsT) (codedSubst crTC tgtT codePoo))
  cGSisCS = eqSym (eqTrans (eqCong2 nd (csLhsT (reify templateCode)) (csPoo (reify templateCode)))
                            (eqSym (codedSubstNd crTC tgtT codeLhsT codePoo codeLhsTNotVar)))

  cGSdef : Eq cGS (codeEqn godelSentence)
  cGSdef = refl

  cstf : Fun1
  cstf = closedSubstTFor (reify crTC) (reify (natCode v1))

  cstfDef : Eq cstf (closedSubstTFor (reify crTC) (reify (natCode v1)))
  cstfDef = refl

  substGodelSentence : (t : Term) ->
    Eq (substEq zero t godelSentence)
       (eqn (ap2 TreeEq (ap1 thFunTFor t) (ap1 substTFor (reify templateCode))) poo)
  substGodelSentence t = refl

  -- NOTE: The original Guard.SubstTForPrecomp had `instForm2 = refl`
  -- here, which forced Agda to fully unfold reify(crTC) (~400K nodes)
  -- and took ~108 seconds.  This file deliberately omits it; the
  -- equivalent type-conversion is built schematically in
  -- Guard/Nelson/InstForm.agda via the lemmas substReify,
  -- substTForClose, thFunTForSubstEq, and substClosedSTF.
