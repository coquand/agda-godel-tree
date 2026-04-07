{-# OPTIONS --safe --without-K --exact-split #-}

module Guard.Nelson.SubstTForFull where

open import Guard.Base
open import Guard.Term
open import Guard.Step
open import Guard.SubstTFor
open import Guard.Nelson.SubstTForO
open import Guard.Nelson.SubstTForNonVar
open import Guard.Nelson.SubstTForVar
open import Guard.Nelson.TreeEqLemmas

------------------------------------------------------------------------
-- Helper: code(t) at the reify level is never tagVarT.
-- code t = nd tag payload where tag is tagO/tagVar/tagAp1/tagAp2.
-- reify(code t) = Pair(reify tag, reify payload).
-- All term code tags satisfy TreeEq(reify tag, tagVarT) = Pair(O,O)
-- EXCEPT tagVar, but reify(code(var n)) = Pair(tagVarT, reify(natCode n))
-- and TreeEq(Pair(tagVarT, X), tagVarT) = Pair(O,O) since tagVarT ≠ tagVarT-as-first-component
-- Actually: tagVarT has 4 levels deep, code(var n) adds another level. So ≠ tagVarT.

reifyCodeNotVar : (t : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap2 TreeEq (reify (code t)) tagVarT) (ap2 Pair O O))
reifyCodeNotVar O = natCodeTagNotVar zero lf
reifyCodeNotVar (var n) =
  -- code(var n) = nd tagVar (natCode n)
  -- tagVar = nd(nd(nd lf lf, lf), lf). natCode is lf-based.
  -- reify(code(var n)) = Pair(tagVarT, reify(natCode n))
  -- tagVarT = Pair(Pair(Pair(O,O),O),O)
  -- This is nd(ooo, lf) at tree level where ooo = nd(nd(nd lf lf, lf), lf) wait no.
  -- tagVar = nd(nd(nd lf lf, lf), lf)
  -- code(var n) = nd tagVar (natCode n)
  -- This is nd(nd(nd(nd lf lf, lf), lf), natCode n)
  -- reify = Pair(Pair(Pair(Pair(O,O),O),O), reify(natCode n))
  -- = Pair(tagVarT, reify(natCode n))
  -- TreeEq(Pair(tagVarT, reify(natCode n)), tagVarT)
  -- = TreeEq(Pair(tagVarT, reify(natCode n)), Pair(Pair(Pair(O,O),O),O))
  -- = IfLf(TreeEq(tagVarT, Pair(Pair(O,O),O)), Pair(TreeEq(reify(natCode n), O), Pair(O,O)))
  -- TreeEq(tagVarT, Pair(Pair(O,O),O)): tagVarT = Pair(Pair(Pair(O,O),O),O) vs Pair(Pair(O,O),O)
  -- = IfLf(TreeEq(Pair(Pair(O,O),O), Pair(O,O)), Pair(TreeEq(O, O), Pair(O,O)))
  -- TreeEq(Pair(Pair(O,O),O), Pair(O,O)):
  -- = IfLf(TreeEq(Pair(O,O), O), Pair(TreeEq(O,O), Pair(O,O)))
  -- TreeEq(Pair(O,O), O) = Pair(O,O) [axTreeEqNL]
  -- IfLf(Pair(O,O), ...) = Pair(O,O)
  -- So TreeEq(Pair(Pair(O,O),O), Pair(O,O)) = Pair(O,O)
  -- Then outer IfLf(Pair(O,O), ...) = Pair(O,O)
  -- So TreeEq(tagVarT, Pair(Pair(O,O),O)) = Pair(O,O)
  -- Final: IfLf(Pair(O,O), ...) = Pair(O,O)
  let poo = ap2 Pair O O
      pooo = ap2 Pair poo O
      -- TreeEq(Pair(O,O), O) = Pair(O,O)
      e1 : Deriv _ (eqn (ap2 TreeEq poo O) poo)
      e1 = axTreeEqNL O O
      -- TreeEq(Pair(Pair(O,O),O), Pair(O,O))
      e2 : Deriv _ (eqn (ap2 TreeEq pooo poo) poo)
      e2 = ruleTrans (axTreeEqNN poo O O O)
           (ruleTrans (congL IfLf (ap2 Pair (ap2 TreeEq O O) poo) e1)
                      (axIfLfN O O (ap2 TreeEq O O) poo))
      -- TreeEq(tagVarT, Pair(Pair(O,O),O))
      e3 : Deriv _ (eqn (ap2 TreeEq tagVarT pooo) poo)
      e3 = ruleTrans (axTreeEqNN pooo O poo O)
           (ruleTrans (congL IfLf (ap2 Pair (ap2 TreeEq O O) poo) e2)
                      (axIfLfN O O (ap2 TreeEq O O) poo))
  in ruleTrans (axTreeEqNN tagVarT (reify (natCode n)) pooo O)
     (ruleTrans (congL IfLf (ap2 Pair (ap2 TreeEq (reify (natCode n)) O) poo) e3)
                (axIfLfN O O (ap2 TreeEq (reify (natCode n)) O) poo))
reifyCodeNotVar (ap1 f t)   = natCodeTagNotVar (suc (suc zero)) (nd (codeF1 f) (code t))
reifyCodeNotVar (ap2 g a b) = natCodeTagNotVar (suc (suc (suc zero))) (nd (codeF2 g) (nd (code a) (code b)))

------------------------------------------------------------------------
-- substTForInner: at any non-var level, Pair unfolds

substTForInner : {hyp : Equation} (a b : Tree) ->
  Deriv hyp (eqn (ap2 TreeEq (reify a) tagVarT) (ap2 Pair O O)) ->
  Deriv hyp (eqn (ap1 substTFor (ap2 Pair (reify a) (reify b)))
                 (ap2 Pair (ap1 substTFor (reify a))
                           (ap1 substTFor (reify b))))
substTForInner a b pf = substTForNonVarStep (reify a) (reify b) O O pf

------------------------------------------------------------------------
-- ap1 full unfolding (2 levels)

substTForAp1Full : {hyp : Equation} (f : Fun1) (t : Term) ->
  Deriv hyp (eqn (ap1 substTFor (reify (code (ap1 f t))))
                 (ap2 Pair (ap1 substTFor (reify tagAp1))
                           (ap2 Pair (ap1 substTFor (reify (codeF1 f)))
                                     (ap1 substTFor (reify (code t))))))
substTForAp1Full f t =
  ruleTrans (substTForInner tagAp1 (nd (codeF1 f) (code t)) tagAp1NotVar)
  (congR Pair (ap1 substTFor (reify tagAp1))
    (substTForInner (codeF1 f) (code t) (reifyCodeF1NotVar f)))

------------------------------------------------------------------------
-- ap2 full unfolding (3 levels)

substTForAp2Full : {hyp : Equation} (g : Fun2) (t1 t2 : Term) ->
  Deriv hyp (eqn (ap1 substTFor (reify (code (ap2 g t1 t2))))
                 (ap2 Pair (ap1 substTFor (reify tagAp2))
                           (ap2 Pair (ap1 substTFor (reify (codeF2 g)))
                                     (ap2 Pair (ap1 substTFor (reify (code t1)))
                                               (ap1 substTFor (reify (code t2)))))))
substTForAp2Full g t1 t2 =
  ruleTrans (substTForInner tagAp2 (nd (codeF2 g) (nd (code t1) (code t2))) tagAp2NotVar)
  (congR Pair (ap1 substTFor (reify tagAp2))
    (ruleTrans (substTForInner (codeF2 g) (nd (code t1) (code t2)) (reifyCodeF2NotVar g))
    (congR Pair (ap1 substTFor (reify (codeF2 g)))
      (substTForInner (code t1) (code t2) (reifyCodeNotVar t1)))))
