{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.StepU2Reach -- Term-fuel Reaches infrastructure for the Layer-1
-- CK machine (BRA4.StepU2).  Independent of Fun1/Fun2 correctness.
--
-- The key data:
--
--   record Reaches (c c' : Term) : Set where
--     fuel : Term         -- a Term-level fuel (NOT a meta-Nat)
--     runs : Deriv (iter step c fuel = c')
--
-- The key composition law:
--
--   iter_add_T : iter step c (sigma n m) = iter step (iter step c n) m
--
-- where sigma : Fun2 is BRA's standard addition (R u s2 v).  The
-- orientation matches reach_trans: a first run of  n  steps from  c  to
-- c'  composes with a second run of  m  steps from  c'  to  c''  into
-- a single run of  sigma n m  steps from  c  to  c''.
--
-- This file is per the "majorising fuel by recursion on f's definition"
-- architecture: the fuel for each Fun1 / Fun2 is itself a BRA function,
-- and composition along iter step proceeds at Term level via sigma.

module BRA4.StepU2Reach where

open import BRA4.Base
open import BRA4.StepU2 using ( step )

open import BRA3.CourseOfValues   using ( iter )
open import BRA3.RecBRA3AtPairUniv using ( iter_base_univ ; iter_step_univ )
open import BRA3.Church           using ( sigma ; T33 ; T34 ; cong1Imp )
open import BRA3.Logic            using ( impTrans ; prependEqLeft ; appendEqRight )
open import BRA3.RuleInst2        using ( ruleInst2 )
open import BRA3.RuleInst3        using ( ruleInst3 )

------------------------------------------------------------------------
-- Sigma facts at Term level.
--
-- sigma_zero  : sigma(x, O) = x          (Church T33)
-- sigma_succ  : sigma(x, s y) = s(sigma(x, y))   (Church T34 specialised)

sigma_zero : (x : Term) -> Deriv (eqF (ap2 sigma x O) x)
sigma_zero = T33

sigma_succ : (x y : Term) ->
  Deriv (eqF (ap2 sigma x (ap1 s y)) (ap1 s (ap2 sigma x y)))
sigma_succ x y = ruleInst2 zero x (suc zero) y refl T34

------------------------------------------------------------------------
-- iter_add_T : iter step c (sigma n m) = iter step (iter step c n) m
--
-- Universal in c, n, m (all Terms).  Proved by  ruleIndNat  on  var 2
-- (m) with motive Pform.

iter_add_T : (c n m : Term) ->
  Deriv (eqF (ap2 (iter step) c (ap2 sigma n m))
              (ap2 (iter step) (ap2 (iter step) c n) m))
iter_add_T c n m =
  let
      ----------------------------------------------------------------
      -- Motive.
      Pform : Formula
      Pform = eqF (ap2 (iter step) (var 0) (ap2 sigma (var 1) (var 2)))
                  (ap2 (iter step) (ap2 (iter step) (var 0) (var 1)) (var 2))

      ----------------------------------------------------------------
      -- Base case at  var 2 := O .
      --   LHS = iter step (var 0) (sigma (var 1) O)
      --       = iter step (var 0) (var 1)               [sigma_zero]
      --   RHS = iter step (iter step (var 0) (var 1)) O
      --       = iter step (var 0) (var 1)               [iter_base_univ]
      baseCase : Deriv (eqF (ap2 (iter step) (var 0) (ap2 sigma (var 1) O))
                            (ap2 (iter step) (ap2 (iter step) (var 0) (var 1)) O))
      baseCase =
        let lhs_eq : Deriv (eqF (ap2 (iter step) (var 0) (ap2 sigma (var 1) O))
                                 (ap2 (iter step) (var 0) (var 1)))
            lhs_eq = congR (iter step) (var 0) (sigma_zero (var 1))

            rhs_eq : Deriv (eqF (ap2 (iter step) (var 0) (var 1))
                                 (ap2 (iter step) (ap2 (iter step) (var 0) (var 1)) O))
            rhs_eq = ruleSym (iter_base_univ step (ap2 (iter step) (var 0) (var 1)))
        in ruleTrans lhs_eq rhs_eq

      ----------------------------------------------------------------
      -- Step case:  imp Pform (Pform[var 2 := s (var 2)]) .
      --   LHS_c = iter step (var 0) (sigma (var 1) (s (var 2)))
      --         = iter step (var 0) (s (sigma (var 1) (var 2)))  [sigma_succ]
      --         = step (iter step (var 0) (sigma (var 1) (var 2)))  [iter_step_univ]
      --                = step LHS_h
      --   RHS_c = iter step (iter step (var 0) (var 1)) (s (var 2))
      --         = step (iter step (iter step (var 0) (var 1)) (var 2))  [iter_step_univ]
      --                = step RHS_h
      -- imp Pform (LHS_c = RHS_c) :=
      --   cong1Imp step LHS_h RHS_h  : imp Pform (step LHS_h = step RHS_h)
      --   prependEqLeft LHS_c (step LHS_h) (step RHS_h) eL : ...
      --   appendEqRight LHS_c (step RHS_h) RHS_c (sym eR) : ...
      LHS_h : Term
      LHS_h = ap2 (iter step) (var 0) (ap2 sigma (var 1) (var 2))

      RHS_h : Term
      RHS_h = ap2 (iter step) (ap2 (iter step) (var 0) (var 1)) (var 2)

      LHS_c : Term
      LHS_c = ap2 (iter step) (var 0) (ap2 sigma (var 1) (ap1 s (var 2)))

      RHS_c : Term
      RHS_c = ap2 (iter step) (ap2 (iter step) (var 0) (var 1)) (ap1 s (var 2))

      stepLH : Term
      stepLH = ap1 step LHS_h

      stepRH : Term
      stepRH = ap1 step RHS_h

      eL : Deriv (eqF LHS_c stepLH)
      eL =
        let e1 : Deriv (eqF LHS_c (ap2 (iter step) (var 0) (ap1 s (ap2 sigma (var 1) (var 2)))))
            e1 = congR (iter step) (var 0) (sigma_succ (var 1) (var 2))

            e2 : Deriv (eqF (ap2 (iter step) (var 0) (ap1 s (ap2 sigma (var 1) (var 2))))
                             stepLH)
            e2 = iter_step_univ step (var 0) (ap2 sigma (var 1) (var 2))
        in ruleTrans e1 e2

      eR : Deriv (eqF RHS_c stepRH)
      eR = iter_step_univ step (ap2 (iter step) (var 0) (var 1)) (var 2)

      stepCase : Deriv (imp Pform (eqF LHS_c RHS_c))
      stepCase =
        let s1 : Deriv (imp Pform (eqF stepLH stepRH))
            s1 = cong1Imp step LHS_h RHS_h

            s2 : Deriv (imp (eqF stepLH stepRH) (eqF LHS_c stepRH))
            s2 = prependEqLeft LHS_c stepLH stepRH eL

            s3 : Deriv (imp Pform (eqF LHS_c stepRH))
            s3 = impTrans s1 s2

            s4 : Deriv (imp (eqF LHS_c stepRH) (eqF LHS_c RHS_c))
            s4 = appendEqRight LHS_c stepRH RHS_c (ruleSym eR)
        in impTrans s3 s4

      ----------------------------------------------------------------
      -- Conclude  ruleIndNat 2 .
      universal : Deriv Pform
      universal = ruleIndNat 2 {P = Pform} baseCase stepCase

      ----------------------------------------------------------------
      -- Specialise (var 0, var 1, var 2) := (c, n, m) simultaneously.
  in ruleInst3 zero c (suc zero) n (suc (suc zero)) m refl refl refl universal

------------------------------------------------------------------------
-- Reaches : the universal-fuel iter-relation.

record Reaches (c c' : Term) : Set where
  constructor mkReach
  field
    fuel : Term
    runs : Deriv (eqF (ap2 (iter step) c fuel) c')

open Reaches public

------------------------------------------------------------------------
-- Reaches combinators.

-- 0 steps:  iter step c O = c  (iter_base_univ).

reach_refl : (c : Term) -> Reaches c c
reach_refl c = mkReach O (iter_base_univ step c)

-- 1 step:  iter step c (s O) = step (iter step c O) = step c .
reach_step1 : (c c' : Term) -> Deriv (eqF (ap1 step c) c') -> Reaches c c'
reach_step1 c c' eStep =
  let unfold : Deriv (eqF (ap2 (iter step) c (ap1 s O))
                           (ap1 step (ap2 (iter step) c O)))
      unfold = iter_step_univ step c O

      rebase : Deriv (eqF (ap1 step (ap2 (iter step) c O))
                           (ap1 step c))
      rebase = cong1 step (iter_base_univ step c)

      chain : Deriv (eqF (ap2 (iter step) c (ap1 s O)) c')
      chain = ruleTrans unfold (ruleTrans rebase eStep)
  in mkReach (ap1 s O) chain

-- Composition:  c reaches c' (fuel n), c' reaches c'' (fuel m), then
--   c reaches c''  with fuel  sigma n m .
reach_trans : {c c' c'' : Term} -> Reaches c c' -> Reaches c' c'' -> Reaches c c''
reach_trans {c} {c'} {c''} r1 r2 =
  let n  : Term
      n  = fuel r1
      m  : Term
      m  = fuel r2
      e1 : Deriv (eqF (ap2 (iter step) c n) c')
      e1 = runs r1
      e2 : Deriv (eqF (ap2 (iter step) c' m) c'')
      e2 = runs r2

      -- iter step c (sigma n m) = iter step (iter step c n) m
      add : Deriv (eqF (ap2 (iter step) c (ap2 sigma n m))
                        (ap2 (iter step) (ap2 (iter step) c n) m))
      add = iter_add_T c n m

      -- iter step (iter step c n) m = iter step c' m  via e1.
      lhs2 : Deriv (eqF (ap2 (iter step) (ap2 (iter step) c n) m)
                         (ap2 (iter step) c' m))
      lhs2 = congL (iter step) m e1

      chain : Deriv (eqF (ap2 (iter step) c (ap2 sigma n m)) c'')
      chain = ruleTrans add (ruleTrans lhs2 e2)
  in mkReach (ap2 sigma n m) chain

-- Rewrite target by an equation.
reach_eq_target : {c c' c'' : Term} ->
  Reaches c c' -> Deriv (eqF c' c'') -> Reaches c c''
reach_eq_target (mkReach f r) e = mkReach f (ruleTrans r e)
