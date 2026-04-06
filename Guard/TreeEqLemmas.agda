{-# OPTIONS --safe --without-K --exact-split #-}

module Guard.TreeEqLemmas where

open import Guard.Base
open import Guard.Term
open import Guard.Step
open import Guard.SubstTFor

------------------------------------------------------------------------
-- Key lemma: for any natCode k, TreeEq(reify(natCode k), first-of-tagVarT) = false
--
-- first-of-tagVarT = Pair(Pair(O,O),O)  (= reify(nd(nd lf lf, lf)))
-- reify(natCode 0) = O               -> TreeEq(O, Pair(...)) = Pair O O [axTreeEqLN]
-- reify(natCode k) = Pair(O, ...)     -> TreeEq(Pair(O,...), Pair(Pair(O,O),...))
--                                        inner TreeEq(O, Pair(O,O)) = Pair O O [axTreeEqLN]
--                                        IfLf(Pair(O,O),...) = Pair O O [axIfLfN]

private
  ppoo : Term
  ppoo = ap2 Pair (ap2 Pair O O) O

natCodeVsTagVarInner : (k : Nat) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap2 TreeEq (reify (natCode k)) ppoo) (ap2 Pair O O))
natCodeVsTagVarInner zero = axTreeEqLN (ap2 Pair O O) O
natCodeVsTagVarInner (suc k) =
  -- reify(natCode(suc k)) = Pair(O, reify(natCode k))
  -- TreeEq(Pair(O, reify(natCode k)), Pair(Pair(O,O), O))
  -- = IfLf(TreeEq(O, Pair(O,O)), Pair(TreeEq(reify(natCode k), O), Pair(O,O)))
  -- TreeEq(O, Pair(O,O)) = Pair(O,O) [axTreeEqLN]
  -- IfLf(Pair(O,O), ...) = Pair(O,O) [axIfLfN]
  ruleTrans (axTreeEqNN O (reify (natCode k)) (ap2 Pair O O) O)
  (ruleTrans (congL IfLf (ap2 Pair (ap2 TreeEq (reify (natCode k)) O) (ap2 Pair O O))
               (axTreeEqLN O O))
             (axIfLfN O O (ap2 TreeEq (reify (natCode k)) O) (ap2 Pair O O)))

------------------------------------------------------------------------
-- For any functor code nd(natCode k, payload):
-- reify = Pair(reify(natCode k), reify(payload))
-- TreeEq(reify, tagVarT) = IfLf(TreeEq(reify(natCode k), ppoo), Pair(TreeEq(reify(payload), O), Pair(O,O)))
-- = IfLf(Pair(O,O), ...) = Pair(O,O)

natCodeTagNotVar : (k : Nat) (payload : Tree) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap2 TreeEq (ap2 Pair (reify (natCode k)) (reify payload)) tagVarT) (ap2 Pair O O))
natCodeTagNotVar k payload =
  ruleTrans (axTreeEqNN (reify (natCode k)) (reify payload) ppoo O)
  (ruleTrans (congL IfLf (ap2 Pair (ap2 TreeEq (reify payload) O) (ap2 Pair O O))
               (natCodeVsTagVarInner k))
             (axIfLfN O O (ap2 TreeEq (reify payload) O) (ap2 Pair O O)))

------------------------------------------------------------------------
-- Per-constructor proofs: reifyCodeF1NotVar, reifyCodeF2NotVar

-- codeF1/codeF2 tags now start at 26 to avoid natCode collision
private
  n25' : Nat
  n25' = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))))))))))))))
  f0' : Nat ; f0' = suc n25'   -- 26
  f1' : Nat ; f1' = suc f0'    -- 27
  f2' : Nat ; f2' = suc f1'    -- 28
  f3' : Nat ; f3' = suc f2'    -- 29
  f4' : Nat ; f4' = suc f3'    -- 30
  f5' : Nat ; f5' = suc f4'    -- 31
  f6' : Nat ; f6' = suc f5'    -- 32

reifyCodeF1NotVar : (f : Fun1) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap2 TreeEq (reify (codeF1 f)) tagVarT) (ap2 Pair O O))
reifyCodeF1NotVar I             = natCodeTagNotVar f0' lf
reifyCodeF1NotVar Fst           = natCodeTagNotVar f1' lf
reifyCodeF1NotVar Snd           = natCodeTagNotVar f2' lf
reifyCodeF1NotVar (Comp f g)    = natCodeTagNotVar f3' (nd (codeF1 f) (codeF1 g))
reifyCodeF1NotVar (Comp2 h f g) = natCodeTagNotVar f4' (nd (codeF2 h) (nd (codeF1 f) (codeF1 g)))
reifyCodeF1NotVar (Rec z s)     = natCodeTagNotVar f5' (nd (code z) (codeF2 s))
reifyCodeF1NotVar (KT t)        = natCodeTagNotVar f6' (code t)

reifyCodeF2NotVar : (g : Fun2) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap2 TreeEq (reify (codeF2 g)) tagVarT) (ap2 Pair O O))
reifyCodeF2NotVar Pair          = natCodeTagNotVar f0' lf
reifyCodeF2NotVar Const         = natCodeTagNotVar f1' lf
reifyCodeF2NotVar (Lift f)      = natCodeTagNotVar f2' (codeF1 f)
reifyCodeF2NotVar (Post f h)    = natCodeTagNotVar f3' (nd (codeF1 f) (codeF2 h))
reifyCodeF2NotVar (Fan h1 h2 h) = natCodeTagNotVar f4' (nd (codeF2 h1) (nd (codeF2 h2) (codeF2 h)))
reifyCodeF2NotVar IfLf          = natCodeTagNotVar f5' lf
reifyCodeF2NotVar TreeEq        = natCodeTagNotVar f6' lf

------------------------------------------------------------------------
-- Term code tag proofs

tagAp1NotVar : {hyp : Equation} ->
  Deriv hyp (eqn (ap2 TreeEq (reify tagAp1) tagVarT) (ap2 Pair O O))
tagAp1NotVar =
  ruleTrans (axTreeEqNN O (ap2 Pair O O) (ap2 Pair (ap2 Pair O O) O) O)
  (ruleTrans (congL IfLf (ap2 Pair (ap2 TreeEq (ap2 Pair O O) O) (ap2 Pair O O))
               (axTreeEqLN (ap2 Pair O O) O))
             (axIfLfN O O (ap2 TreeEq (ap2 Pair O O) O) (ap2 Pair O O)))

tagAp2NotVar : {hyp : Equation} ->
  Deriv hyp (eqn (ap2 TreeEq (reify tagAp2) tagVarT) (ap2 Pair O O))
tagAp2NotVar =
  ruleTrans (axTreeEqNN O (ap2 Pair O (ap2 Pair O O)) (ap2 Pair (ap2 Pair O O) O) O)
  (ruleTrans (congL IfLf (ap2 Pair (ap2 TreeEq (ap2 Pair O (ap2 Pair O O)) O) (ap2 Pair O O))
               (axTreeEqLN (ap2 Pair O O) O))
             (axIfLfN O O (ap2 TreeEq (ap2 Pair O (ap2 Pair O O)) O) (ap2 Pair O O)))

tagONotVar : {hyp : Equation} ->
  Deriv hyp (eqn (ap2 TreeEq O tagVarT) (ap2 Pair O O))
tagONotVar = axTreeEqLN (ap2 Pair (ap2 Pair O O) O) O
