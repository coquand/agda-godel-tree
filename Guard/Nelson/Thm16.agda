{-# OPTIONS --safe --without-K --exact-split #-}

-- Rose Theorem 16 (p.134), specialized to f(x) = TreeEq(cGST, thFunTFor(x)).
--
-- Goal: from hypothesis conR, derive godelSentence.

module Guard.Nelson.Thm16 where

open import Guard.Base
open import Guard.Term
open import Guard.Step
open import Guard.ThFun using (codeEqn)
open import Guard.ThFunTFor using (thFunTFor ; thFunStep)
open import Guard.SubstTForPrecomp
  using (godelSentence ; cGS ; cGSisCS ; codeLhsT ; codePoo ;
         crTC ; cstf ; templateCode ; cGSdef ;
         substGodelSentence ; instForm2)
open import Guard.SubstTForCorrect
open import Guard.GodelII using (treeEqSelf)
open import Guard.Nelson.ComplementEqn using (eF ; eFRed ; conR ; trueT ; falseT)

private
  cGST : Term
  cGST = reify cGS

  v0 : Term ; v0 = var zero
  v1T : Term ; v1T = var (suc zero)

  -- cGS = nd cGS_L cGS_R where:
  cGS_L : Tree
  cGS_L = codedSubst crTC (natCode (suc zero)) codeLhsT

  cGS_R : Tree
  cGS_R = codedSubst crTC (natCode (suc zero)) codePoo

  cGS_eq : Eq cGS (nd cGS_L cGS_R)
  cGS_eq = cGSisCS

  -- cGST = reify(nd cGS_L cGS_R) = Pair(reify cGS_L, reify cGS_R)
  cGST_eq : Eq cGST (ap2 Pair (reify cGS_L) (reify cGS_R))
  cGST_eq = eqCong reify cGS_eq

------------------------------------------------------------------------
-- Base case: TreeEq(cGST, thFunTFor(O)) = falseT.
--
-- thFunTFor(O) = O (by axRecLf).
-- cGST = Pair(_, _) (from cGST_eq).
-- TreeEq(Pair(a,b), O) = falseT (by axTreeEqNL).

baseLemma : {hyp : Equation} ->
  Deriv hyp (eqn (ap2 TreeEq cGST O) falseT)
baseLemma {hyp} = eqSubst (\t -> Deriv hyp (eqn (ap2 TreeEq t O) falseT))
                           (eqSym cGST_eq)
                           (axTreeEqNL (reify cGS_L) (reify cGS_R))

baseFull : {hyp : Equation} ->
  Deriv hyp (eqn (ap2 TreeEq cGST (ap1 thFunTFor O)) falseT)
baseFull = ruleTrans (congR TreeEq cGST (axRecLf O thFunStep)) baseLemma

------------------------------------------------------------------------
-- Next: the step case. Needs:
--   Deriv conR (eqn (ap2 TreeEq cGST (ap1 thFunTFor (ap2 Pair v0 v1T))) falseT)
-- This requires showing thFunStep never produces cGST, using conR.
