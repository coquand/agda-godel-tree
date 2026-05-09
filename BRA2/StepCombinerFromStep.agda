{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA2.StepCombinerFromStep -- the payoff lemma converting a raw
-- indBT step premise (in DerivT0) into a value-conditioned
-- StepCombiner.
--
-- Given:
--
--   step : DerivT0 ((atomic e[v1/0]) imp ((atomic e[v2/0])
--                    imp (atomic e[Pair v1 v2/0])))
--
-- with  v1 , v2  fresh in  e  (Geq v_i (maxVarEq e)) and  v1 != v2 ,
-- we derive
--
--   stepCombiner :
--     forall (a b : Term) (va : IsValue a) (vb : IsValue b)
--       (d_a : DerivT0 (atomic e[a/0]))
--       (d_b : DerivT0 (atomic e[b/0])) ->
--     DerivT0 (atomic e[Pair a b/0])
--
-- by:  ruleInst v1 a step ; ruleInst v2 b ; mp d_a ; mp d_b .
--
-- The eqSubst chain after each ruleInst aligns the substituted
-- formula with the cleanly-substituted target form, using
-- substEq_compose_general (BRA2.SubstCompose) plus the
-- subst/value/var-self/var-diff helpers (BRA2.SubstValue).
--
-- Composition with  unfoldAtValue  gives the indBT-elimination at
-- any value-shape conclusion: combining
--
--   stepCombiner = stepCombinerFromStep e v1 v2 ge1 ge2 v2NeV1 step
--
-- with  unfoldAtValue e stepCombiner base t vt  produces a DerivT0
-- proof of  atomic (substEq 0 t e)  for every value t.

module BRA2.StepCombinerFromStep where

open import BRA2.Base
open import BRA2.Term
open import BRA2.Formula
import BRA2.DerivT0 as O
open import BRA2.MaxVar
open import BRA2.SubstCompose
open import BRA2.SubstValue
open import BRA2.UnfoldAtValue using (StepCombiner)

------------------------------------------------------------------------
-- Helper: rewrite three  atomic E_i  positions in an  imp -nested
-- formula via three Eq witnesses.

eqSubstAtomic3 :
  {l1 l2 l3 r1 r2 r3 : Equation} ->
  Eq l1 r1 -> Eq l2 r2 -> Eq l3 r3 ->
  O.DerivT0 ((atomic l1) imp ((atomic l2) imp (atomic l3))) ->
  O.DerivT0 ((atomic r1) imp ((atomic r2) imp (atomic r3)))
eqSubstAtomic3 {l1} {l2} {l3} {r1} {r2} {r3} eq1 eq2 eq3 d =
  let d1 : O.DerivT0 ((atomic r1) imp ((atomic l2) imp (atomic l3)))
      d1 = eqSubst
             (\ x -> O.DerivT0 ((atomic x) imp ((atomic l2) imp (atomic l3))))
             eq1 d
      d2 : O.DerivT0 ((atomic r1) imp ((atomic r2) imp (atomic l3)))
      d2 = eqSubst
             (\ x -> O.DerivT0 ((atomic r1) imp ((atomic x) imp (atomic l3))))
             eq2 d1
  in eqSubst
       (\ x -> O.DerivT0 ((atomic r1) imp ((atomic r2) imp (atomic x))))
       eq3 d2

------------------------------------------------------------------------
-- The main lemma.

stepCombinerFromStep :
  (e : Equation) (v1 v2 : Nat) ->
  Geq v1 (maxVarEq e) ->
  Geq v2 (maxVarEq e) ->
  Eq (natEq v2 v1) false ->
  O.DerivT0 ((atomic (substEq zero (var v1) e))
             imp ((atomic (substEq zero (var v2) e))
                  imp (atomic (substEq zero (ap2 Pair (var v1) (var v2)) e)))) ->
  StepCombiner e
stepCombinerFromStep e v1 v2 ge1 ge2 v2NeV1 step a b va vb d_a d_b = result
  where
    -- ----- After ruleInst v1 a step : substituting v1 := a -----
    -- step1 has type:
    --   atomic (substEq v1 a (substEq 0 (var v1) e))
    --     imp atomic (substEq v1 a (substEq 0 (var v2) e))
    --     imp atomic (substEq v1 a (substEq 0 (ap2 Pair (var v1) (var v2)) e))

    step1 = O.ruleInst v1 a step

    -- substEq v1 a (substEq 0 (var v1) e) = substEq 0 a e
    eq1 : Eq (substEq v1 a (substEq zero (var v1) e)) (substEq zero a e)
    eq1 = eqTrans (substEq_compose_general v1 a (var v1) e ge1)
                   (eqCong (\ s -> substEq zero s e) (subst_var_self v1 a))

    -- substEq v1 a (substEq 0 (var v2) e) = substEq 0 (var v2) e
    -- (because v2 != v1, so subst v1 a (var v2) = var v2)
    eq2 : Eq (substEq v1 a (substEq zero (var v2) e)) (substEq zero (var v2) e)
    eq2 = eqTrans (substEq_compose_general v1 a (var v2) e ge1)
                   (eqCong (\ s -> substEq zero s e) (subst_var_diff v1 v2 a v2NeV1))

    -- substEq v1 a (substEq 0 (ap2 Pair (var v1) (var v2)) e)
    --   = substEq 0 (ap2 Pair a (var v2)) e
    eq3 : Eq (substEq v1 a (substEq zero (ap2 Pair (var v1) (var v2)) e))
              (substEq zero (ap2 Pair a (var v2)) e)
    eq3 = eqTrans (substEq_compose_general v1 a (ap2 Pair (var v1) (var v2)) e ge1)
                   (eqCong (\ s -> substEq zero s e) (subst_pair_var_var v1 v2 a v2NeV1))

    step1' : O.DerivT0 ((atomic (substEq zero a e))
                         imp ((atomic (substEq zero (var v2) e))
                              imp (atomic (substEq zero (ap2 Pair a (var v2)) e))))
    step1' = eqSubstAtomic3 eq1 eq2 eq3 step1

    -- ----- After ruleInst v2 b step1' : substituting v2 := b -----
    -- step2 has type:
    --   atomic (substEq v2 b (substEq 0 a e))
    --     imp atomic (substEq v2 b (substEq 0 (var v2) e))
    --     imp atomic (substEq v2 b (substEq 0 (ap2 Pair a (var v2)) e))

    step2 = O.ruleInst v2 b step1'

    -- substEq v2 b (substEq 0 a e) = substEq 0 a e
    -- (because  IsValue a  =>  subst v2 b a = a)
    eq4 : Eq (substEq v2 b (substEq zero a e)) (substEq zero a e)
    eq4 = eqTrans (substEq_compose_general v2 b a e ge2)
                   (eqCong (\ s -> substEq zero s e) (subst_value v2 b a va))

    -- substEq v2 b (substEq 0 (var v2) e) = substEq 0 b e
    eq5 : Eq (substEq v2 b (substEq zero (var v2) e)) (substEq zero b e)
    eq5 = substEq_compose_fresh v2 b e ge2

    -- substEq v2 b (substEq 0 (ap2 Pair a (var v2)) e) = substEq 0 (ap2 Pair a b) e
    -- subst v2 b (ap2 Pair a (var v2)) = ap2 Pair (subst v2 b a) (subst v2 b (var v2))
    --                                  = ap2 Pair a b   (by subst_value, subst_var_self)
    eq6 : Eq (substEq v2 b (substEq zero (ap2 Pair a (var v2)) e))
              (substEq zero (ap2 Pair a b) e)
    eq6 = eqTrans (substEq_compose_general v2 b (ap2 Pair a (var v2)) e ge2)
                   (eqCong (\ s -> substEq zero s e)
                           (eqCong2 (ap2 Pair) (subst_value v2 b a va) (subst_var_self v2 b)))

    step2' : O.DerivT0 ((atomic (substEq zero a e))
                         imp ((atomic (substEq zero b e))
                              imp (atomic (substEq zero (ap2 Pair a b) e))))
    step2' = eqSubstAtomic3 eq4 eq5 eq6 step2

    -- ----- mp twice with d_a and d_b -----
    mp1 : O.DerivT0 ((atomic (substEq zero b e))
                      imp (atomic (substEq zero (ap2 Pair a b) e)))
    mp1 = O.mp step2' d_a

    result : O.DerivT0 (atomic (substEq zero (ap2 Pair a b) e))
    result = O.mp mp1 d_b
