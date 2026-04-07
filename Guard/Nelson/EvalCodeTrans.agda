{-# OPTIONS --safe --without-K --exact-split #-}

-- EvalCodeTrans.agda
-- Ground induction step analysis for ruleTrans.
--
-- The composition lemma: if a = b and b = c (equationally),
-- then TreeEq(a, c) = O.
--
-- This is what the ruleTrans induction step reduces to.
-- It works when we have EQUATIONAL hypotheses (a = b, b = c).
-- But Schema F only gives TreeEq(evalCode(L), evalCode(R)) = O,
-- and recovering the equational fact evalCode(L) = evalCode(R) from
-- TreeEq(evalCode(L), evalCode(R)) = O requires INVERTING TreeEq.
--
-- TreeEq inversion (TreeEq(a,b)=O implies a=b) is provable for ground
-- trees by Schema F on the TREE structure. But it's a separate lemma
-- and requires its own induction — this is where the nested recursion
-- issue from the analysis manifests.
--
-- Summary of the obstruction for universal Good(p) via Schema F:
-- 1. Good(lf) fails: thFunTFor(lf) = O, and Fst(O)/Snd(O) are stuck
-- 2. Good(nd(tag19, nd(sp1, sp2))) needs R1 = L2 (middle term match),
--    which is NOT guaranteed for arbitrary trees
-- 3. Even with R1 = L2, going from TreeEq(X,Y)=O to X=Y requires
--    TreeEq inversion, which is a separate Schema F argument

module Guard.Nelson.EvalCodeTrans where

open import Guard.Base
open import Guard.Term
open import Guard.Step
open import Guard.Nelson.EvalCode
open import Guard.GodelII using (treeEqSelf)

------------------------------------------------------------------------
-- The composition lemma (equational version).
-- If a = b and b = c in the equational theory, then TreeEq(a, c) = O.
-- Proof: a = c by transitivity, then TreeEq(a, c) = TreeEq(c, c) = O.

treeEqFromEq : (a b c : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn a b) ->
  Deriv hyp (eqn b c) ->
  Deriv hyp (eqn (ap2 TreeEq a c) O)
treeEqFromEq a b c ab bc =
  let ac = ruleTrans ab bc
  in ruleTrans (congL TreeEq c ac) (treeEqSelf c)

------------------------------------------------------------------------
-- Instantiation for evalCode composition.
-- If evalCode(L1) = evalCode(R1) and evalCode(L2) = evalCode(R2)
-- and R1 = L2 (middle term match), then TreeEq(evalCode(L1), evalCode(R2)) = O.

evalCodeTransCompose :
  (L1 R1 L2 R2 : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn R1 L2) ->
  Deriv hyp (eqn (ap1 evalCode L1) (ap1 evalCode R1)) ->
  Deriv hyp (eqn (ap1 evalCode L2) (ap1 evalCode R2)) ->
  Deriv hyp (eqn (ap2 TreeEq (ap1 evalCode L1) (ap1 evalCode R2)) O)
evalCodeTransCompose L1 R1 L2 R2 match eq1 eq2 =
  let -- evalCode(R1) = evalCode(L2) by congruence of match
      bridge = cong1 evalCode match
      -- evalCode(L1) = evalCode(R1) = evalCode(L2) = evalCode(R2)
      chain = ruleTrans eq1 (ruleTrans bridge eq2)
  in treeEqFromEq (ap1 evalCode L1) (ap1 evalCode L1) (ap1 evalCode R2)
       (axRefl (ap1 evalCode L1)) chain
