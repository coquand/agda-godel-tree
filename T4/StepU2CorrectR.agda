{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.StepU2CorrectR -- the Fun2 R-case of Layer-1 completeness for
-- the universal interpreter.
--
-- Architecture: T4/STEPU2-STACK-HANDOFF.md + the abstract framing in
-- ~/.claude/.../memory/feedback_peter_recursion_abstract_lemma.md .
--
-- This file is intended to host the full R-case story:
--
--   identityA               -- sub top y = s (sub top (s y))  under leq (s y) top
--   identityB               -- sub top (sub top y) = y         under leq y top
--   Stack-unfold-at-current -- one descent step of the backward iterate
--   StepU2CorrectR-universal -- the ruleIndNat 2 theorem (open in params, y)
--   correct2_R               -- the Correct2 (R g h1 h2) API wrapper
--
-- The abstract bounded backward-transform induction is JUST ruleIndNat 2
-- on the motive  Q := substF 2 _ (motive shape)  --  there is no
-- separate Peter-recursion principle to derive.  The "Peter content" is
-- entirely in how Stack-unfold-at-current discharges the step.
--
-- STATUS 2026-05-29 .  Sections 1-3 SHIPPED here -- typechecked under
-- --safe --without-K --exact-split , no holes, no postulates:
--
--   identityA           (~80  LoC)
--   identityB           (~250 LoC, ruleIndNat on top + T82-caseElim)
--   Stack-unfold-at-current (~130 LoC)
--   small helpers: transUnderOne, transUnderTwo, weakenUnder.
--
-- Sections 4-5 (Universal theorem + correct2_R wrapper) are NOT YET
-- IMPLEMENTED here.  Next-session handoff:
--
--   * Motive Pform = imp (leq (var 2) y_top)
--                        (eqF (iter step
--                               (cfgEV Rcode (pi x (var 2))
--                                       (Stack params (sub y_top (var 2))))
--                               (fuelR_combinator x (var 2)))
--                             (cfgRT (R x (var 2))
--                                    (Stack params (sub y_top (var 2)))))
--     with params = pi y_top (pi K_outer x), y_top/K_outer/x META-Term
--     parameters (NOT BRA vars).  Only var 2 = y_current is a BRA var.
--
--   * Base v2 := O : run = reach_step1 (stepU_at_evRbase) `reach_trans`
--     bG.runs1 ; fuel matched to fuelR_combinator x O via
--     axPost + Snd_paired_R_at_O + constN_eq.  Premise discharged by axK.
--
--     Worked fuel-bridge skeleton (the part most easy to mis-thread):
--
--       eqA : eqF (fuelR_combinator x O) (Snd (paired_R x O))
--           = axPost Snd paired_R x O
--       eqB : eqF (Snd (paired_R x O)) (sigma (constN 1 x) (fG x))
--           = Snd_paired_R_at_O x
--       eqC : eqF (constN 1 x) (s O)        = constN_eq 1 x
--       eqD : eqF (sigma (constN 1 x) (fG x)) (sigma (s O) (fG x))
--           = congL sigma (fG x) eqC
--       fuel_chain : eqF (fuelR_combinator x O) (sigma (s O) (fG x))
--                  = ruleTrans eqA (ruleTrans eqB eqD)
--
--     Then to thread `chained' : Reaches cInit cGoal` (whose fuel is the
--     sigma form) into a Deriv at the fuelR_combinator-form fuel:
--
--       cong_iter : eqF (iter step cInit (fuelR_combinator x O))
--                       (iter step cInit (sigma (s O) (fG x)))
--                = congR (iter step) cInit fuel_chain
--       result    : eqF (iter step cInit (fuelR_combinator x O)) cGoal
--                = ruleTrans cong_iter (runs chained')
--
--   * Step v2 -> s v2 : 7-segment run
--       reach_step1 (stepU_at_evRstep)  fuel = s O
--     . bH2.runs2 x (var 2) K_h2         fuel = fH2 x (var 2)
--     . reach_step1 (stepU_at_rtR1)      fuel = s O
--     . IH at v2 (Pform applied to T80_at HypBound)   fuel = fuelR_combinator x (var 2)
--     . reach_step1 (stepU_at_rtApp2)    fuel = s O
--     . bH1.runs2 (h2 x (var 2)) (R x (var 2)) K_sy     fuel = fH1 (h2 x (var 2)) (R x (var 2))
--     The IH-segment uses Stack-unfold-at-current TWICE: once forward
--     (to rewrite K_R = kons (frmApp2 h1c (h2 x (var 2))) K_sy --> K_y)
--     so the IH's cfgEV's K position matches, once backward at the
--     rtApp2 transition.  Final value matched via ax_R_step.
--     Total fuel = sigma (sigma (sigma (sigma (sigma 1 fH2_xy) 1) fuelR_combinator_xy) 1) fH1_h2_R
--     ; matched to fuelR_combinator x (s var 2) via axPost +
--     Snd_paired_R_at_s + Fan_eq + Lift1_eq + Lift2_eq + axFst + axSnd.
--
--   * Bundle wrapper correct2_R : at (x, y, K), specialise
--     StepU2CorrectR-universal at (y_top := y, K_outer := K, x := x) ,
--     then ruleInst (suc (suc zero)) y , then mp with (ruleInst zero y T73)
--     to discharge the leq y y premise.  Stack params (sub y y) = K
--     via congR Stack params (ruleInst zero y T73) `ruleTrans`
--     Stack-base-at-K0 y K x ; cfg-rewrite the run's K position via
--     cfgEV_kont_rw / cfgRT_kont_rw helpers (still to be added).
--
-- Estimated remaining ~500 LoC.  The skeleton in this session's commit
-- to /tmp shows the right shape but was incomplete (premature `identP`
-- placeholders, type-mismatched bComb chain) so was rolled back.
-- Sections 1-3 below are the load-bearing portion.

module T4.StepU2CorrectR where

open import T4.Base
open import T4.StepU2
  using ( step
        ; stepU_at_evRbase ; stepU_at_evRstep
        ; stepU_at_rtR1 ; stepU_at_rtApp2
        ; cfgEV ; cfgRT ; kons ; frmApp2 ; frmR1
        ; mcode1 ; mcode2
        ; tagApp2 ; tagRT ; tagEV )
open import T4.StepU2Reach
  using ( Reaches ; reach_refl ; reach_step1 ; reach_trans ; reach_eq_target
        ; mkReach ; fuel ; runs
        ; sigma_zero ; sigma_succ ; iter_add_T )
open import T4.StepU2CorrectAPI
  using ( Correct1 ; Correct2 ; mkC1 ; mkC2
        ; fuelF ; fuelG ; runs1 ; runs2 )
open import T4.StepU2RStack
  using ( module StackOf )
open import T4.StepU2PairFuelR using ()
open import T4.LoopReaches
  using ( ClosedAtVar ; mkCAV ; cavSubst
        ; cav_O ; cav_ap1 ; cav_ap2 ; cav_natCode )
open import T4.Tags
  using ( tag_s ; tag_o ; tag_u ; tag_C ; tag_v ; tag_R )

open import BRA3.CourseOfValues
  using ( iter )

------------------------------------------------------------------------
-- BRA3 imports.

open import BRA3.Church
  using ( pi ; sub ; sigma ; predecessor ; p_aux
        ; T_p_O ; T_p_S_v0 ; T_sub_S_v01
        ; cong1Imp ; T33 ; T34 ; T35 )
open import BRA3.ChurchT117 using ( Fst )
open import BRA3.ChurchT116 using ( Snd )
open import BRA3.ChurchLeq  using ( leq ; T76 )
open import BRA3.ChurchSubSucc using ( T_sub_O ; T57sub )
open import BRA3.ChurchT73  using ( T73 )
open import BRA3.ChurchT80  using ( T80 )
open import BRA3.ChurchT82  using ( T82 )
open import BRA3.ChurchPredLemmas using ( L_sp )
open import BRA3.Contrapositive
  using ( axContrapos ; identP ; liftP ; bComb ; bCombTwo
        ; compI ; Q_to_dNeg )
open import BRA3.Logic
  using ( impTrans ; prependEqLeft ; appendEqRight ; eqSymImp )
open import BRA3.Equational
  using ( axRefl ; ruleSym ; ruleTrans ; cong1 ; congL ; congR )
open import BRA3.RuleInst2  using ( ruleInst2 )
open import BRA3.RuleInst3  using ( ruleInst3 )
open import BRA3.RecBRA3AtPairUniv
  using ( sub_step_under_le_univ
        ; not_leq_succ_under_le_univ
        ; not_leq_succ_self_univ
        ; iter_base_univ ; iter_step_univ )
open import BRA3.ChurchDChurchAsSub using ( caseElimUnderOne )
open import BRA3.ChurchLemmaA       using ( caseElimUnderTwo )

open import BRA3.PairAlgebra
  using ( axFst ; axSnd ; compose1U ; compose1U_eq
        ; Post ; axPost )
open import BRA3.Fan
  using ( Lift1 ; Lift1_eq ; Lift2 ; Lift2_eq ; Fan ; Fan_eq )

------------------------------------------------------------------------
-- Section 1.  Identity A:
--
--   imp (leq (s var 1) (var 0))
--        (eqF (sub var 0 var 1) (s (sub var 0 (s var 1))))
--
-- "Under  s y <= top ,  top - y = (top - (s y)) + 1 ."
--
-- Strategy (Hilbert-chained, no deduction theorem):
--   1.  Let  H = leq (s var 1) (var 0)  and  X = sub var 0 var 1 .
--       From  not_leq_succ_under_le_univ  +  axContrapos +  Q_to_dNeg ,
--       derive  imp H (neg (eqF X O)) .
--   2.  L_sp at X (ruleInst 0 X L_sp): imp (neg (eqF X O)) (eqF (s (pred X)) X).
--   3.  impTrans (1) (2):  imp H (eqF (s (pred X)) X).
--   4.  T_sub_S_v01 specialised gives  sub var 0 (s var 1) = pred X .
--       cong1 s gives  s (sub var 0 (s var 1)) = s (pred X) .
--   5.  prependEqLeft + eqSymImp + impTrans to rotate (3)'s consequent.

identityA :
  Deriv (imp (leq (ap1 s (var 1)) (var 0))
              (eqF (ap2 sub (var 0) (var 1))
                    (ap1 s (ap2 sub (var 0) (ap1 s (var 1))))))
identityA =
  let
      H : Formula
      H = leq (ap1 s (var 1)) (var 0)

      Hleq : Formula
      Hleq = leq (var 0) (var 1)

      X : Term
      X = ap2 sub (var 0) (var 1)

      Y : Term         -- = sub var 0 (s var 1) .
      Y = ap2 sub (var 0) (ap1 s (var 1))

      -- Step 1a.  not_leq_succ_under_le_univ : imp (leq v0 v1) (neg (leq (s v1) v0)) .
      --   At (v0, v1) literal of identityA = (var 0, var 1) : same shape;
      --   gives  imp Hleq (neg H) .
      step1a : Deriv (imp Hleq (neg H))
      step1a = not_leq_succ_under_le_univ

      -- Step 1b.  axContrapos to swap:
      --   imp (imp Hleq (neg H)) (imp (neg (neg H)) (neg Hleq)) .
      --   mp with step1a:  imp (neg (neg H)) (neg Hleq) .
      step1b : Deriv (imp (neg (neg H)) (neg Hleq))
      step1b = mp (axContrapos Hleq (neg H)) step1a

      -- Step 1c.  Q_to_dNeg H : imp H (neg (neg H)).
      step1c : Deriv (imp H (neg (neg H)))
      step1c = Q_to_dNeg H

      -- Combined Step 1:  imp H (neg (eqF X O)) .
      -- ( Hleq = leq var 0 var 1 = eqF (sub var 0 var 1) O = eqF X O .)
      step1 : Deriv (imp H (neg (eqF X O)))
      step1 = impTrans step1c step1b

      -- Step 2.  L_sp at X.
      step2 : Deriv (imp (neg (eqF X O)) (eqF (ap1 s (ap1 predecessor X)) X))
      step2 = ruleInst zero X L_sp

      -- Step 3.  impTrans gives  imp H (eqF (s (pred X)) X) .
      step3 : Deriv (imp H (eqF (ap1 s (ap1 predecessor X)) X))
      step3 = impTrans step1 step2

      -- Step 4.  T_sub_S_v01 at literal (var 0, var 1):
      --   eqF (sub var 0 (s var 1)) (pred (sub var 0 var 1))
      --   = eqF Y (pred X) .
      step4_eq : Deriv (eqF Y (ap1 predecessor X))
      step4_eq = T_sub_S_v01

      -- cong1 s on step4_eq:  eqF (s Y) (s (pred X)) .
      step4_sY : Deriv (eqF (ap1 s Y) (ap1 s (ap1 predecessor X)))
      step4_sY = cong1 s step4_eq

      -- Step 5a.  prependEqLeft (s Y) (s (pred X)) X (step4_sY):
      --   imp (eqF (s (pred X)) X) (eqF (s Y) X) .
      step5a : Deriv (imp (eqF (ap1 s (ap1 predecessor X)) X)
                           (eqF (ap1 s Y) X))
      step5a = prependEqLeft (ap1 s Y) (ap1 s (ap1 predecessor X)) X step4_sY

      -- Step 5b.  impTrans step3 step5a:  imp H (eqF (s Y) X) .
      step5b : Deriv (imp H (eqF (ap1 s Y) X))
      step5b = impTrans step3 step5a

      -- Step 5c.  eqSymImp (s Y) X:  imp (eqF (s Y) X) (eqF X (s Y)) .
      step5c : Deriv (imp (eqF (ap1 s Y) X) (eqF X (ap1 s Y)))
      step5c = eqSymImp (ap1 s Y) X

  in impTrans step5b step5c

------------------------------------------------------------------------
-- Small helpers: equational transitivity under one / two hypothesis layers.

transUnderOne :
  {P : Formula} {a b c : Term} ->
  Deriv (imp P (eqF a b)) ->
  Deriv (imp P (eqF b c)) ->
  Deriv (imp P (eqF a c))
transUnderOne {P} {a} {b} {c} D1 D2 =
  let lift_trans : Deriv (imp P (imp (eqF b a) (imp (eqF b c) (eqF a c))))
      lift_trans = liftP P (ax_eqTrans b a c)

      lift_eqSym : Deriv (imp P (imp (eqF a b) (eqF b a)))
      lift_eqSym = liftP P (eqSymImp a b)

      symD1 : Deriv (imp P (eqF b a))
      symD1 = bComb lift_eqSym D1

      step1 : Deriv (imp P (imp (eqF b c) (eqF a c)))
      step1 = bComb lift_trans symD1
  in bComb step1 D2

transUnderTwo :
  {P1 P2 : Formula} {a b c : Term} ->
  Deriv (imp P1 (imp P2 (eqF a b))) ->
  Deriv (imp P1 (imp P2 (eqF b c))) ->
  Deriv (imp P1 (imp P2 (eqF a c)))
transUnderTwo {P1} {P2} {a} {b} {c} D1 D2 =
  let lift_trans : Deriv (imp P1 (imp P2
                            (imp (eqF b a) (imp (eqF b c) (eqF a c)))))
      lift_trans = liftP P1 (liftP P2 (ax_eqTrans b a c))

      lift_eqSym : Deriv (imp P1 (imp P2 (imp (eqF a b) (eqF b a))))
      lift_eqSym = liftP P1 (liftP P2 (eqSymImp a b))

      symD1 : Deriv (imp P1 (imp P2 (eqF b a)))
      symD1 = bCombTwo lift_eqSym D1

      step1 : Deriv (imp P1 (imp P2 (imp (eqF b c) (eqF a c))))
      step1 = bCombTwo lift_trans symD1
  in bCombTwo step1 D2

-- "Weaken under P":  imp P A  -->  imp P (imp Q A) .
weakenUnder :
  (Q : Formula) {P A : Formula} ->
  Deriv (imp P A) -> Deriv (imp P (imp Q A))
weakenUnder Q {P} {A} D =
  let kImp : Deriv (imp P (imp A (imp Q A)))
      kImp = liftP P (axK A Q)
  in bComb kImp D

------------------------------------------------------------------------
-- Section 2.  Identity B:
--
--   imp (leq (var 1) (var 0))
--        (eqF (sub (var 0) (sub (var 0) (var 1))) (var 1))
--
-- "Under  y <= top ,   top - (top - y) = y ."
--
-- ruleIndNat 0 on  var 0 (= top) ,  var 1 (= y)  free.
--
--   Base v0 := O: leq v1 O forces v1 = O ; both sides reduce to O.
--   Step v0 -> s v0: T82-style split  leq v1 (s v0)  ->  leq v1 v0  V  v1 = s v0,
--     each branch yields the conclusion ; combine via caseElimUnderTwo.

identityB :
  Deriv (imp (leq (var 1) (var 0))
              (eqF (ap2 sub (var 0) (ap2 sub (var 0) (var 1))) (var 1)))
identityB = ruleIndNat 0 {P = Pform} baseCase stepImp
  where
    Pform : Formula
    Pform = imp (leq (var 1) (var 0))
                 (eqF (ap2 sub (var 0) (ap2 sub (var 0) (var 1))) (var 1))

    ------------------------------------------------------------------
    -- Base case  v0 := O .

    baseCase :
      Deriv (imp (leq (var 1) O)
                  (eqF (ap2 sub O (ap2 sub O (var 1))) (var 1)))
    baseCase =
      let -- Hyp1: prependEqLeft v1 (sub v1 O) O (ruleSym T_sub_O v1).
          --   imp (leq v1 O = eqF (sub v1 O) O) (eqF v1 O).
          step_a : Deriv (imp (leq (var 1) O) (eqF (var 1) O))
          step_a = prependEqLeft (var 1) (ap2 sub (var 1) O) O
                                  (ruleSym (T_sub_O (var 1)))

          -- step_a_swap : imp (leq v1 O) (eqF O v1) .
          step_a_swap : Deriv (imp (leq (var 1) O) (eqF O (var 1)))
          step_a_swap = impTrans step_a (eqSymImp (var 1) O)

          -- T76 at var 0 := sub O v1 :  eqF (sub O (sub O v1)) O .
          T76_at_inner : Deriv (eqF (ap2 sub O (ap2 sub O (var 1))) O)
          T76_at_inner = ruleInst zero (ap2 sub O (var 1)) T76

          -- ax_eqTrans O (sub O (sub O v1)) v1 + ruleSym T76_at_inner
          --   gives  imp (eqF O v1) (eqF (sub O (sub O v1)) v1) .
          core_base :
            Deriv (imp (eqF O (var 1))
                        (eqF (ap2 sub O (ap2 sub O (var 1))) (var 1)))
          core_base = mp (ax_eqTrans O (ap2 sub O (ap2 sub O (var 1))) (var 1))
                          (ruleSym T76_at_inner)
      in impTrans step_a_swap core_base

    ------------------------------------------------------------------
    -- Step case.

    Hyp_next : Formula
    Hyp_next = leq (var 1) (ap1 s (var 0))

    Hyp_X1 : Formula
    Hyp_X1 = leq (var 1) (var 0)

    Hyp_Y : Formula
    Hyp_Y = eqF (var 1) (ap1 s (var 0))

    Q_step : Formula
    Q_step = eqF (ap2 sub (ap1 s (var 0))
                          (ap2 sub (ap1 s (var 0)) (var 1)))
                  (var 1)

    -- T82 at literal variables, then swap (var 0 <-> var 1) via ruleInst2.
    --   T82 : imp (leq v0 (s v1)) (imp (neg (leq v0 v1)) (eqF v0 (s v1))) .
    --   We want at (v0 := var 1, v1 := var 0): same shape, swap.

    T82_at :
      Deriv (imp Hyp_next (imp (neg Hyp_X1) Hyp_Y))
    T82_at = ruleInst2 zero (var 1) (suc zero) (var 0) refl T82

    -- T80 swap: at (var 0 := var 1, var 1 := var 0), giving
    --   imp (leq (s var 1) (var 0)) (leq (var 1) (var 0)) .
    -- We do NOT use this here ; we use T82_at directly.

    -- ------------------------------------------------------------
    -- negX_Y under (Pform, Hyp_next):
    --   imp Pform (imp Hyp_next (imp (neg Hyp_X1) Hyp_Y))
    negX_Y :
      Deriv (imp Pform (imp Hyp_next (imp (neg Hyp_X1) Hyp_Y)))
    negX_Y = liftP Pform T82_at

    -- ------------------------------------------------------------
    -- X_Rf : imp Pform (imp Hyp_next (imp Hyp_X1 Q_step))
    --
    -- Inside (Pform, Hyp_next, Hyp_X1):
    --   sub_step_at applied to Hyp_X1 (Pform/Hyp_next unused):
    --     eqF (sub (s v0) v1) (s (sub v0 v1)) .
    --   congR sub (s v0):
    --     eqF (sub (s v0) (sub (s v0) v1)) (sub (s v0) (s (sub v0 v1))) .
    --   T57_at:
    --     eqF (sub (s v0) (s (sub v0 v1))) (sub v0 (sub v0 v1)) .
    --   Combine -> eqF (sub (s v0) (sub (s v0) v1)) (sub v0 (sub v0 v1)) .
    --   Pform applied to Hyp_X1 (the IH) :
    --     eqF (sub v0 (sub v0 v1)) v1 .
    --   transUnderTwo gives Q_step.

    LHS_target : Term
    LHS_target = ap2 sub (ap1 s (var 0))
                          (ap2 sub (ap1 s (var 0)) (var 1))

    mid_target : Term
    mid_target = ap2 sub (var 0) (ap2 sub (var 0) (var 1))

    -- sub_step_at : imp (leq (var 1) (var 0))
    --                   (eqF (sub (s (var 0)) (var 1)) (s (sub (var 0) (var 1)))) .
    -- Obtained from sub_step_under_le_univ by simultaneous swap.
    sub_step_at :
      Deriv (imp Hyp_X1
              (eqF (ap2 sub (ap1 s (var 0)) (var 1))
                    (ap1 s (ap2 sub (var 0) (var 1)))))
    sub_step_at = ruleInst2 zero (var 1) (suc zero) (var 0)
                              refl sub_step_under_le_univ

    -- T57sub at (var 0 := var 0, var 1 := sub v0 v1):
    --   eqF (sub (s v0) (s (sub v0 v1))) (sub v0 (sub v0 v1)) .
    T57_at :
      Deriv (eqF (ap2 sub (ap1 s (var 0)) (ap1 s (ap2 sub (var 0) (var 1))))
                  (ap2 sub (var 0) (ap2 sub (var 0) (var 1))))
    T57_at = ruleInst2 zero (var 0) (suc zero)
                        (ap2 sub (var 0) (var 1)) refl T57sub

    -- Step 1: under Hyp_X1 alone,
    --   eqF (sub (s v0) (sub (s v0) v1)) (sub v0 (sub v0 v1)) .
    cong_under_X1 :
      Deriv (imp Hyp_X1 (eqF LHS_target mid_target))
    cong_under_X1 =
      let -- congR sub (s v0) on sub_step_at -- in imp form:
          axCongR_sub :
            Deriv (imp (eqF (ap2 sub (ap1 s (var 0)) (var 1))
                              (ap1 s (ap2 sub (var 0) (var 1))))
                        (eqF LHS_target
                              (ap2 sub (ap1 s (var 0))
                                        (ap1 s (ap2 sub (var 0) (var 1))))))
          axCongR_sub = ax_eqCongR sub
                          (ap2 sub (ap1 s (var 0)) (var 1))
                          (ap1 s (ap2 sub (var 0) (var 1)))
                          (ap1 s (var 0))

          step_a' :
            Deriv (imp Hyp_X1
                    (eqF LHS_target
                          (ap2 sub (ap1 s (var 0))
                                    (ap1 s (ap2 sub (var 0) (var 1))))))
          step_a' = impTrans sub_step_at axCongR_sub

          -- appendEqRight to apply T57_at.
          appR :
            Deriv (imp (eqF LHS_target
                              (ap2 sub (ap1 s (var 0))
                                        (ap1 s (ap2 sub (var 0) (var 1)))))
                        (eqF LHS_target mid_target))
          appR = appendEqRight LHS_target
                   (ap2 sub (ap1 s (var 0)) (ap1 s (ap2 sub (var 0) (var 1))))
                   mid_target T57_at
      in impTrans step_a' appR

    -- Step 2: combine with Pform (the IH) to get  imp Pform (imp Hyp_X1 Q_step) .
    --
    -- Pform =  imp Hyp_X1 (eqF mid_target v1) .
    -- identP Pform = imp Pform (imp Hyp_X1 (eqF mid_target v1)) .

    pform_to_IH : Deriv (imp Pform (imp Hyp_X1 (eqF mid_target (var 1))))
    pform_to_IH = identP Pform

    cong_under_Pform_X1 :
      Deriv (imp Pform (imp Hyp_X1 (eqF LHS_target mid_target)))
    cong_under_Pform_X1 = liftP Pform cong_under_X1

    Q_under_Pform_X1 :
      Deriv (imp Pform (imp Hyp_X1 (eqF LHS_target (var 1))))
    Q_under_Pform_X1 =
      transUnderTwo cong_under_Pform_X1 pform_to_IH

    X_Rf :
      Deriv (imp Pform (imp Hyp_next (imp Hyp_X1 Q_step)))
    X_Rf =
      let -- weakenUnder Hyp_next on Q_under_Pform_X1 -- under Pform.
          axK_lifted :
            Deriv (imp Pform (imp (imp Hyp_X1 (eqF LHS_target (var 1)))
                                   (imp Hyp_next (imp Hyp_X1 (eqF LHS_target (var 1))))))
          axK_lifted = liftP Pform (axK (imp Hyp_X1 (eqF LHS_target (var 1))) Hyp_next)
      in bComb axK_lifted Q_under_Pform_X1

    -- ------------------------------------------------------------
    -- Y_Rf : imp Pform (imp Hyp_next (imp Hyp_Y Q_step))
    --
    -- Under Hyp_Y = eqF v1 (s v0):
    --   eA : sub (s v0) v1 = sub (s v0) (s v0)              [ax_eqCongR sub _ _ (s v0)]
    --   eB : sub (s v0) (s v0) = O                          [T73 at (var 0 := s v0)]
    --   eC : sub (s v0) v1 = O                               [chain eA + eB via appendEqRight]
    --   eD : sub (s v0) (sub (s v0) v1) = sub (s v0) O      [ax_eqCongR sub (sub (s v0) v1) O (s v0)]
    --   eE : sub (s v0) O = s v0                             [T_sub_O (s v0)]
    --   eEC: sub (s v0) (sub (s v0) v1) = s v0               [chain eD + eE via appendEqRight]
    --   eF : s v0 = v1                                       [ruleSym Hyp_Y in imp form]
    --   Q_step : sub (s v0) (sub (s v0) v1) = v1            [transUnderOne eEC, eF -- using Hyp_Y].
    --
    -- Build entirely under Hyp_Y first, then lift Pform / Hyp_next.

    T73_at_sv0 :
      Deriv (eqF (ap2 sub (ap1 s (var 0)) (ap1 s (var 0))) O)
    T73_at_sv0 = ruleInst zero (ap1 s (var 0)) T73

    Y_to_Q_only_Y : Deriv (imp Hyp_Y Q_step)
    Y_to_Q_only_Y =
      let eA :
            Deriv (imp Hyp_Y
                    (eqF (ap2 sub (ap1 s (var 0)) (var 1))
                          (ap2 sub (ap1 s (var 0)) (ap1 s (var 0)))))
          eA = ax_eqCongR sub (var 1) (ap1 s (var 0)) (ap1 s (var 0))

          eB : Deriv (eqF (ap2 sub (ap1 s (var 0)) (ap1 s (var 0))) O)
          eB = T73_at_sv0

          -- appendEqRight (sub (s v0) v1) (sub (s v0) (s v0)) O eB :
          --   imp (eqF (sub (s v0) v1) (sub (s v0) (s v0))) (eqF (sub (s v0) v1) O).
          aR1 :
            Deriv (imp (eqF (ap2 sub (ap1 s (var 0)) (var 1))
                              (ap2 sub (ap1 s (var 0)) (ap1 s (var 0))))
                        (eqF (ap2 sub (ap1 s (var 0)) (var 1)) O))
          aR1 = appendEqRight (ap2 sub (ap1 s (var 0)) (var 1))
                                (ap2 sub (ap1 s (var 0)) (ap1 s (var 0)))
                                O eB

          eC : Deriv (imp Hyp_Y (eqF (ap2 sub (ap1 s (var 0)) (var 1)) O))
          eC = impTrans eA aR1

          -- ax_eqCongR sub (sub (s v0) v1) O (s v0) :
          --   imp (eqF (sub (s v0) v1) O)
          --       (eqF (sub (s v0) (sub (s v0) v1)) (sub (s v0) O)).
          axCongR_D :
            Deriv (imp (eqF (ap2 sub (ap1 s (var 0)) (var 1)) O)
                        (eqF LHS_target
                              (ap2 sub (ap1 s (var 0)) O)))
          axCongR_D = ax_eqCongR sub (ap2 sub (ap1 s (var 0)) (var 1)) O
                                  (ap1 s (var 0))

          eD : Deriv (imp Hyp_Y (eqF LHS_target (ap2 sub (ap1 s (var 0)) O)))
          eD = impTrans eC axCongR_D

          -- T_sub_O (s v0) : eqF (sub (s v0) O) (s v0).
          eE : Deriv (eqF (ap2 sub (ap1 s (var 0)) O) (ap1 s (var 0)))
          eE = T_sub_O (ap1 s (var 0))

          aR2 :
            Deriv (imp (eqF LHS_target (ap2 sub (ap1 s (var 0)) O))
                        (eqF LHS_target (ap1 s (var 0))))
          aR2 = appendEqRight LHS_target (ap2 sub (ap1 s (var 0)) O) (ap1 s (var 0)) eE

          eEC : Deriv (imp Hyp_Y (eqF LHS_target (ap1 s (var 0))))
          eEC = impTrans eD aR2

          -- eF : imp Hyp_Y (eqF (s v0) v1) -- ruleSym of Hyp_Y, in imp form.
          eF : Deriv (imp Hyp_Y (eqF (ap1 s (var 0)) (var 1)))
          eF = eqSymImp (var 1) (ap1 s (var 0))
      in transUnderOne eEC eF

    Y_Rf :
      Deriv (imp Pform (imp Hyp_next (imp Hyp_Y Q_step)))
    Y_Rf = liftP Pform (liftP Hyp_next Y_to_Q_only_Y)

    -- ------------------------------------------------------------
    -- caseElimUnderTwo combines negX_Y, X_Rf, Y_Rf.

    step_combined :
      Deriv (imp Pform (imp Hyp_next Q_step))
    step_combined = caseElimUnderTwo {P1 = Pform} {P2 = Hyp_next}
                      {X = Hyp_X1} {Y = Hyp_Y} {Rf = Q_step}
                      negX_Y X_Rf Y_Rf

    stepImp : Deriv (imp Pform (substF 0 (ap1 s (var 0)) Pform))
    stepImp = step_combined

------------------------------------------------------------------------
-- Section 3.  Stack-unfold-at-current -- the descent recurrence:
--
--   under  leq (s y) y_top :
--     Stack params (sub y_top y) = kons (frmApp2 h1c (h2 x y))
--                                       (Stack params (sub y_top (s y)))
--
-- where  params = pi y_top (pi K_outer x) .
--
-- Combines Stack-step-at-params from T4.StepU2RStack with Identity A
-- (used twice -- once forward to rewrite the Stack-step argument,
-- once via cong+chain to clean the frame's h2 argument) and Identity B
-- (also for the frame's h2 argument cleanup).

module Unfold (h1 h2 : Fun2) where

  open StackOf h1 h2
    using ( h1c ; Stack ; Stack-step-at-params )

  Stack-unfold-at-current :
    (y_top K_outer x y : Term) ->
    Deriv (leq (ap1 s y) y_top) ->
    Deriv (eqF (ap2 Stack (ap2 pi y_top (ap2 pi K_outer x))
                  (ap2 sub y_top y))
                (kons (frmApp2 h1c (ap2 h2 x y))
                      (ap2 Stack (ap2 pi y_top (ap2 pi K_outer x))
                        (ap2 sub y_top (ap1 s y)))))
  Stack-unfold-at-current y_top K_outer x y H =
    let params : Term
        params = ap2 pi y_top (ap2 pi K_outer x)

        -- Identity A specialised at (var 0 := y_top, var 1 := y).
        --   imp (leq (s y) y_top) (eqF (sub y_top y) (s (sub y_top (s y))))
        idA_at : Deriv (imp (leq (ap1 s y) y_top)
                              (eqF (ap2 sub y_top y)
                                    (ap1 s (ap2 sub y_top (ap1 s y)))))
        idA_at = ruleInst2 zero y_top (suc zero) y refl identityA

        -- IDA : eqF (sub y_top y) (s (sub y_top (s y)))   (from H).
        IDA : Deriv (eqF (ap2 sub y_top y) (ap1 s (ap2 sub y_top (ap1 s y))))
        IDA = mp idA_at H

        -- congR Stack params on IDA.
        cong_Stack :
          Deriv (eqF (ap2 Stack params (ap2 sub y_top y))
                      (ap2 Stack params (ap1 s (ap2 sub y_top (ap1 s y)))))
        cong_Stack = congR Stack params IDA

        -- Stack-step-at-params at d := sub y_top (s y) :
        --   Stack params (s (sub y_top (s y)))
        --     = kons (frmApp2 h1c (h2 x (sub y_top (s (sub y_top (s y))))))
        --             (Stack params (sub y_top (s y))) .
        stack_step :
          Deriv (eqF (ap2 Stack params (ap1 s (ap2 sub y_top (ap1 s y))))
                      (kons (frmApp2 h1c
                              (ap2 h2 x
                                (ap2 sub y_top (ap1 s (ap2 sub y_top (ap1 s y))))))
                             (ap2 Stack params (ap2 sub y_top (ap1 s y)))))
        stack_step = Stack-step-at-params y_top K_outer x (ap2 sub y_top (ap1 s y))

        chain1 :
          Deriv (eqF (ap2 Stack params (ap2 sub y_top y))
                      (kons (frmApp2 h1c
                              (ap2 h2 x
                                (ap2 sub y_top (ap1 s (ap2 sub y_top (ap1 s y))))))
                             (ap2 Stack params (ap2 sub y_top (ap1 s y)))))
        chain1 = ruleTrans cong_Stack stack_step

        -- Clean the frame's h2 arg: sub y_top (s (sub y_top (s y))) -> y .
        --
        --   By IDA: sub y_top y = s (sub y_top (s y))  ; ruleSym gives
        --     s (sub y_top (s y)) = sub y_top y .
        --   Then congR sub y_top:
        --     sub y_top (s (sub y_top (s y))) = sub y_top (sub y_top y) .
        --   Identity B at (var 0 := y_top, var 1 := y) under leq y y_top:
        --     sub y_top (sub y_top y) = y .
        --   Need leq y y_top -- from H via T80 at (var 0 := y, var 1 := y_top).

        IDA_sym : Deriv (eqF (ap1 s (ap2 sub y_top (ap1 s y))) (ap2 sub y_top y))
        IDA_sym = ruleSym IDA

        cong_subA :
          Deriv (eqF (ap2 sub y_top (ap1 s (ap2 sub y_top (ap1 s y))))
                      (ap2 sub y_top (ap2 sub y_top y)))
        cong_subA = congR sub y_top IDA_sym

        -- T80 at (var 0 := y, var 1 := y_top) via ruleInst2.
        --   imp (leq (s y) y_top) (leq y y_top) .
        T80_at :
          Deriv (imp (leq (ap1 s y) y_top) (leq y y_top))
        T80_at = ruleInst2 zero y (suc zero) y_top refl T80

        H_leq_y : Deriv (leq y y_top)
        H_leq_y = mp T80_at H

        -- Identity B at (var 0 := y_top, var 1 := y) via ruleInst2.
        --   imp (leq y y_top) (eqF (sub y_top (sub y_top y)) y) .
        idB_at :
          Deriv (imp (leq y y_top)
                      (eqF (ap2 sub y_top (ap2 sub y_top y)) y))
        idB_at = ruleInst2 zero y_top (suc zero) y refl identityB

        IDB : Deriv (eqF (ap2 sub y_top (ap2 sub y_top y)) y)
        IDB = mp idB_at H_leq_y

        clean_arg :
          Deriv (eqF (ap2 sub y_top (ap1 s (ap2 sub y_top (ap1 s y)))) y)
        clean_arg = ruleTrans cong_subA IDB

        -- Build the kons-frame congruence chain.
        cong_h2 :
          Deriv (eqF (ap2 h2 x (ap2 sub y_top (ap1 s (ap2 sub y_top (ap1 s y)))))
                      (ap2 h2 x y))
        cong_h2 = congR h2 x clean_arg

        cong_pi_h1c :
          Deriv (eqF (ap2 pi h1c
                       (ap2 h2 x (ap2 sub y_top (ap1 s (ap2 sub y_top (ap1 s y))))))
                      (ap2 pi h1c (ap2 h2 x y)))
        cong_pi_h1c = congR pi h1c cong_h2

        cong_frmApp2 :
          Deriv (eqF (frmApp2 h1c
                       (ap2 h2 x (ap2 sub y_top (ap1 s (ap2 sub y_top (ap1 s y))))))
                      (frmApp2 h1c (ap2 h2 x y)))
        cong_frmApp2 = congR pi (natCode tagApp2) cong_pi_h1c

        cong_pi_kons_inner :
          Deriv (eqF (ap2 pi (frmApp2 h1c
                                (ap2 h2 x (ap2 sub y_top
                                  (ap1 s (ap2 sub y_top (ap1 s y))))))
                              (ap2 Stack params (ap2 sub y_top (ap1 s y))))
                      (ap2 pi (frmApp2 h1c (ap2 h2 x y))
                              (ap2 Stack params (ap2 sub y_top (ap1 s y)))))
        cong_pi_kons_inner = congL pi
          (ap2 Stack params (ap2 sub y_top (ap1 s y))) cong_frmApp2

        cong_kons :
          Deriv (eqF (kons (frmApp2 h1c
                              (ap2 h2 x (ap2 sub y_top
                                (ap1 s (ap2 sub y_top (ap1 s y))))))
                             (ap2 Stack params (ap2 sub y_top (ap1 s y))))
                      (kons (frmApp2 h1c (ap2 h2 x y))
                             (ap2 Stack params (ap2 sub y_top (ap1 s y)))))
        cong_kons = congR pi (ap1 s O) cong_pi_kons_inner

    in ruleTrans chain1 cong_kons

-- Sections 4-5 to be appended to T4/StepU2CorrectR.agda

------------------------------------------------------------------------
-- Section 4.  StepU2CorrectR-universal -- the ruleIndNat 2 theorem
-- on the backward-iterate motive.
--
-- Motive Pform (with var 2 = y_current, var 0 = y_top, var 1 = K_outer,
-- var 3 = x as free Term vars; ruleIndNat 2 substitutes only var 2):
--
--   Pform = imp (leq (var 2) (var 0))
--                (eqF (iter step
--                       (cfgEV Rc (pi (var 3) (var 2))
--                              (Stack paramsExpr (sub (var 0) (var 2))))
--                       (fuelR_combinator (var 3) (var 2)))
--                     (cfgRT ((R g h1 h2) (var 3) (var 2))
--                            (Stack paramsExpr (sub (var 0) (var 2)))))
--
-- where paramsExpr = pi (var 0) (pi (var 1) (var 3))  and
-- Rc = mcode2 (R g h1 h2).

module Construct
  (g : Fun1) (h1 h2 : Fun2)
  (bG : Correct1 g) (bH1 : Correct2 h1) (bH2 : Correct2 h2)
  where

  open StackOf h1 h2
    using ( h1c ; Stack
          ; Stack-base-at-K0 ; Stack-step-at-params )

  open Unfold h1 h2 using ( Stack-unfold-at-current )

  open T4.StepU2PairFuelR.Construct g h1 h2 bG bH1 bH2
    using ( paired_R ; fuelR_combinator ; fG ; fH1 ; fH2
          ; F3 ; fuel_next_Fun2
          ; Snd_paired_R_eq ; Fst_paired_R_eq
          ; Snd_paired_R_at_O ; Snd_paired_R_at_s )

  ------------------------------------------------------------------------
  -- Section 4a.  Local helpers.

  cfgRT-val-rw : (val val' K : Term) ->
                  Deriv (eqF val val') ->
                  Deriv (eqF (cfgRT val K) (cfgRT val' K))
  cfgRT-val-rw val val' K e = congR pi (natCode tagRT) (congL pi K e)

  cfgRT-kont-rw : (val K K' : Term) ->
                   Deriv (eqF K K') ->
                   Deriv (eqF (cfgRT val K) (cfgRT val K'))
  cfgRT-kont-rw val K K' e = congR pi (natCode tagRT) (congR pi val e)

  cfgEV-kont-rw : (fc a K K' : Term) ->
                   Deriv (eqF K K') ->
                   Deriv (eqF (cfgEV fc a K) (cfgEV fc a K'))
  cfgEV-kont-rw fc a K K' e =
    congR pi (natCode tagEV) (congR pi (ap2 pi fc a) e)

  -- One step of iter: from "step c = c'" derive "iter step c (s O) = c'".
  iter-step1 : (c c' : Term) ->
                Deriv (eqF (ap1 step c) c') ->
                Deriv (eqF (ap2 (iter step) c (ap1 s O)) c')
  iter-step1 c c' e =
    let e1 = iter_step_univ step c O
        e2 = cong1 step (iter_base_univ step c)
    in ruleTrans e1 (ruleTrans e2 e)

  -- ClosedAtVar witnesses for mcode1 / mcode2 (any Fun1 / Fun2).
  -- Needed for bridging the substT-stuck positions in baseCase / stepCase.
  -- (Same pattern as T4.MuSimulation but inlined to avoid that dependency.)

  cav-mcode1 : (k : Nat) (f : Fun1) -> ClosedAtVar k (mcode1 f)
  cav-mcode2 : (k : Nat) (g : Fun2) -> ClosedAtVar k (mcode2 g)

  cav-mcode1 k s =
    cav_ap2 k pi (natCode tag_s) O (cav_natCode k tag_s) (cav_O k)
  cav-mcode1 k o =
    cav_ap2 k pi (natCode tag_o) O (cav_natCode k tag_o) (cav_O k)
  cav-mcode1 k u =
    cav_ap2 k pi (natCode tag_u) O (cav_natCode k tag_u) (cav_O k)
  cav-mcode1 k (C g h1' h2') =
    cav_ap2 k pi (natCode tag_C)
      (ap2 pi (mcode2 g) (ap2 pi (mcode1 h1') (mcode1 h2')))
      (cav_natCode k tag_C)
      (cav_ap2 k pi (mcode2 g) (ap2 pi (mcode1 h1') (mcode1 h2'))
        (cav-mcode2 k g)
        (cav_ap2 k pi (mcode1 h1') (mcode1 h2')
          (cav-mcode1 k h1') (cav-mcode1 k h2')))

  cav-mcode2 k v =
    cav_ap2 k pi (natCode tag_v) O (cav_natCode k tag_v) (cav_O k)
  cav-mcode2 k (R g' h1' h2') =
    cav_ap2 k pi (natCode tag_R)
      (ap2 pi (mcode1 g') (ap2 pi (mcode2 h1') (mcode2 h2')))
      (cav_natCode k tag_R)
      (cav_ap2 k pi (mcode1 g') (ap2 pi (mcode2 h1') (mcode2 h2'))
        (cav-mcode1 k g')
        (cav_ap2 k pi (mcode2 h1') (mcode2 h2')
          (cav-mcode2 k h1') (cav-mcode2 k h2')))

  ------------------------------------------------------------------------
  -- Section 4b.  Stack-unfold-at-current in IMP form.
  -- Needed because the IH-application in the step case is under HypNew.

  Stack-unfold-at-current-imp :
    (y_top K_outer x y : Term) ->
    Deriv (imp (leq (ap1 s y) y_top)
                (eqF (ap2 Stack (ap2 pi y_top (ap2 pi K_outer x))
                          (ap2 sub y_top y))
                     (kons (frmApp2 h1c (ap2 h2 x y))
                           (ap2 Stack (ap2 pi y_top (ap2 pi K_outer x))
                                (ap2 sub y_top (ap1 s y))))))
  Stack-unfold-at-current-imp y_top K_outer x y =
    let H : Formula
        H = leq (ap1 s y) y_top

        params : Term
        params = ap2 pi y_top (ap2 pi K_outer x)

        sub_y : Term
        sub_y = ap2 sub y_top y

        sub_sy : Term
        sub_sy = ap2 sub y_top (ap1 s y)

        s_sub_sy : Term
        s_sub_sy = ap1 s sub_sy

        sub_sssy : Term
        sub_sssy = ap2 sub y_top s_sub_sy

        ------------------------------------------------------------
        -- Identity A in imp form.
        IDA_imp : Deriv (imp H (eqF sub_y s_sub_sy))
        IDA_imp = ruleInst2 zero y_top (suc zero) y refl identityA

        -- congR Stack params on IDA_imp.
        cong_Stack :
          Deriv (imp H (eqF (ap2 Stack params sub_y)
                              (ap2 Stack params s_sub_sy)))
        cong_Stack =
          bComb (liftP H (ax_eqCongR Stack sub_y s_sub_sy params))
                IDA_imp

        -- Stack-step (unconditional).
        stack_step :
          Deriv (eqF (ap2 Stack params s_sub_sy)
                      (kons (frmApp2 h1c (ap2 h2 x sub_sssy))
                            (ap2 Stack params sub_sy)))
        stack_step = Stack-step-at-params y_top K_outer x sub_sy

        stack_step_imp :
          Deriv (imp H (eqF (ap2 Stack params s_sub_sy)
                              (kons (frmApp2 h1c (ap2 h2 x sub_sssy))
                                    (ap2 Stack params sub_sy))))
        stack_step_imp = liftP H stack_step

        -- chain1: imp H (eqF (Stack params sub_y) (kons ... (Stack params sub_sy)))
        chain1_imp :
          Deriv (imp H (eqF (ap2 Stack params sub_y)
                              (kons (frmApp2 h1c (ap2 h2 x sub_sssy))
                                    (ap2 Stack params sub_sy))))
        chain1_imp = transUnderOne cong_Stack stack_step_imp

        ------------------------------------------------------------
        -- Clean the frame's h2 argument: sub y_top s_sub_sy -> y.

        -- IDA reversed: imp H (eqF s_sub_sy sub_y).
        IDA_sym_imp : Deriv (imp H (eqF s_sub_sy sub_y))
        IDA_sym_imp =
          bComb (liftP H (eqSymImp sub_y s_sub_sy)) IDA_imp

        -- cong_subA: imp H (eqF sub_sssy (sub y_top sub_y)).
        cong_subA :
          Deriv (imp H (eqF sub_sssy (ap2 sub y_top sub_y)))
        cong_subA =
          bComb (liftP H (ax_eqCongR sub s_sub_sy sub_y y_top))
                IDA_sym_imp

        -- T80 at (var 0 := y, var 1 := y_top).
        T80_at : Deriv (imp H (leq y y_top))
        T80_at = ruleInst2 zero y (suc zero) y_top refl T80

        -- Identity B at (var 0 := y_top, var 1 := y).
        idB_at : Deriv (imp (leq y y_top) (eqF (ap2 sub y_top sub_y) y))
        idB_at = ruleInst2 zero y_top (suc zero) y refl identityB

        IDB_imp : Deriv (imp H (eqF (ap2 sub y_top sub_y) y))
        IDB_imp = impTrans T80_at idB_at

        -- clean_arg: imp H (eqF sub_sssy y).
        clean_arg : Deriv (imp H (eqF sub_sssy y))
        clean_arg = transUnderOne cong_subA IDB_imp

        ------------------------------------------------------------
        -- Lift through cong_h2, cong_pi, cong_frmApp2, cong_pi_kons, cong_kons.

        cong_h2_imp :
          Deriv (imp H (eqF (ap2 h2 x sub_sssy) (ap2 h2 x y)))
        cong_h2_imp =
          bComb (liftP H (ax_eqCongR h2 sub_sssy y x)) clean_arg

        cong_pi_h1c_imp :
          Deriv (imp H (eqF (ap2 pi h1c (ap2 h2 x sub_sssy))
                              (ap2 pi h1c (ap2 h2 x y))))
        cong_pi_h1c_imp =
          bComb (liftP H (ax_eqCongR pi (ap2 h2 x sub_sssy)
                                          (ap2 h2 x y) h1c))
                cong_h2_imp

        cong_frmApp2_imp :
          Deriv (imp H (eqF (frmApp2 h1c (ap2 h2 x sub_sssy))
                              (frmApp2 h1c (ap2 h2 x y))))
        cong_frmApp2_imp =
          bComb (liftP H (ax_eqCongR pi (ap2 pi h1c (ap2 h2 x sub_sssy))
                                          (ap2 pi h1c (ap2 h2 x y))
                                          (natCode tagApp2)))
                cong_pi_h1c_imp

        cong_pi_kons_inner_imp :
          Deriv (imp H (eqF (ap2 pi (frmApp2 h1c (ap2 h2 x sub_sssy))
                                      (ap2 Stack params sub_sy))
                              (ap2 pi (frmApp2 h1c (ap2 h2 x y))
                                      (ap2 Stack params sub_sy))))
        cong_pi_kons_inner_imp =
          bComb (liftP H (ax_eqCongL pi (frmApp2 h1c (ap2 h2 x sub_sssy))
                                           (frmApp2 h1c (ap2 h2 x y))
                                           (ap2 Stack params sub_sy)))
                cong_frmApp2_imp

        cong_kons_imp :
          Deriv (imp H (eqF (kons (frmApp2 h1c (ap2 h2 x sub_sssy))
                                     (ap2 Stack params sub_sy))
                              (kons (frmApp2 h1c (ap2 h2 x y))
                                     (ap2 Stack params sub_sy))))
        cong_kons_imp =
          bComb (liftP H (ax_eqCongR pi
                          (ap2 pi (frmApp2 h1c (ap2 h2 x sub_sssy))
                                   (ap2 Stack params sub_sy))
                          (ap2 pi (frmApp2 h1c (ap2 h2 x y))
                                   (ap2 Stack params sub_sy))
                          (ap1 s O)))
                cong_pi_kons_inner_imp

    in transUnderOne chain1_imp cong_kons_imp

  ------------------------------------------------------------------------
  -- Section 4c.  fuel_next_Fun2 unfolding.
  --
  -- ap2 fuel_next_Fun2 (F3 x y) (paired_R x y)
  --   = sigma (sigma (sigma (sigma (sigma (s O) (fH2 x y)) (s O))
  --                          (fuelR_combinator x y)) (s O))
  --           (fH1 (h2 x y) (R g h1 h2 x y))

  fuel-next-unfold : (x y : Term) ->
    Deriv (eqF (ap2 fuel_next_Fun2 (ap2 F3 x y) (ap2 paired_R x y))
                (ap2 sigma
                    (ap2 sigma
                      (ap2 sigma
                        (ap2 sigma
                          (ap2 sigma (ap1 s O) (ap2 fH2 x y))
                          (ap1 s O))
                        (ap2 fuelR_combinator x y))
                      (ap1 s O))
                    (ap2 fH1 (ap2 h2 x y) (ap2 (R g h1 h2) x y))))
  fuel-next-unfold x y =
    let A : Term
        A = ap2 F3 x y
        B : Term
        B = ap2 paired_R x y
        oneT : Term
        oneT = ap1 s O
        fh2v : Term
        fh2v = ap2 fH2 x y
        fuelR_xy : Term
        fuelR_xy = ap2 fuelR_combinator x y
        h2v : Term
        h2v = ap2 h2 x y
        Rxy : Term
        Rxy = ap2 (R g h1 h2) x y
        fh1v : Term
        fh1v = ap2 fH1 h2v Rxy

        ------------------------------------------------------------
        -- A_pi : F3 x y = pi (h2 x y) (fH2 x y).
        A_pi : Deriv (eqF A (ap2 pi h2v fh2v))
        A_pi = Fan_eq h2 fH2 pi x y

        SndA : Deriv (eqF (ap1 Snd A) fh2v)
        SndA = ruleTrans (cong1 Snd A_pi) (axSnd h2v fh2v)

        FstA : Deriv (eqF (ap1 Fst A) h2v)
        FstA = ruleTrans (cong1 Fst A_pi) (axFst h2v fh2v)

        SndB : Deriv (eqF (ap1 Snd B) fuelR_xy)
        SndB = Snd_paired_R_eq x y

        FstB : Deriv (eqF (ap1 Fst B) Rxy)
        FstB = Fst_paired_R_eq x y

        ------------------------------------------------------------
        -- Ingredients evaluated at (A, B):

        eOne : Deriv (eqF (ap2 (Lift2 (constN 1)) A B) oneT)
        eOne =
          ruleTrans (Lift2_eq (constN 1) A B)
                     (constN_eq 1 B)

        eFH2 : Deriv (eqF (ap2 (Lift1 Snd) A B) fh2v)
        eFH2 = ruleTrans (Lift1_eq Snd A B) SndA

        eFP : Deriv (eqF (ap2 (Lift2 Snd) A B) fuelR_xy)
        eFP = ruleTrans (Lift2_eq Snd A B) SndB

        eFH1 : Deriv (eqF (ap2 (Fan (Lift1 Fst) (Lift2 Fst) fH1) A B) fh1v)
        eFH1 =
          let e1 : Deriv (eqF (ap2 (Fan (Lift1 Fst) (Lift2 Fst) fH1) A B)
                                (ap2 fH1 (ap2 (Lift1 Fst) A B) (ap2 (Lift2 Fst) A B)))
              e1 = Fan_eq (Lift1 Fst) (Lift2 Fst) fH1 A B
              eL1 : Deriv (eqF (ap2 (Lift1 Fst) A B) h2v)
              eL1 = ruleTrans (Lift1_eq Fst A B) FstA
              eL2 : Deriv (eqF (ap2 (Lift2 Fst) A B) Rxy)
              eL2 = ruleTrans (Lift2_eq Fst A B) FstB
              e2 : Deriv (eqF (ap2 fH1 (ap2 (Lift1 Fst) A B) (ap2 (Lift2 Fst) A B))
                                fh1v)
              e2 = ruleTrans (congL fH1 (ap2 (Lift2 Fst) A B) eL1)
                              (congR fH1 h2v eL2)
          in ruleTrans e1 e2

        ------------------------------------------------------------
        -- Layer 1: addSigma oneFun2 fuelH2_proj.

        L1_target : Term
        L1_target = ap2 sigma oneT fh2v

        eL1 :
          Deriv (eqF (ap2 (Fan (Lift2 (constN 1)) (Lift1 Snd) sigma) A B)
                      L1_target)
        eL1 =
          let e1 = Fan_eq (Lift2 (constN 1)) (Lift1 Snd) sigma A B
              e2 = ruleTrans (congL sigma (ap2 (Lift1 Snd) A B) eOne)
                              (congR sigma oneT eFH2)
          in ruleTrans e1 e2

        ------------------------------------------------------------
        -- Layer 2: addSigma L1 oneFun2.

        L2_target : Term
        L2_target = ap2 sigma L1_target oneT

        eL2 :
          Deriv (eqF (ap2 (Fan (Fan (Lift2 (constN 1)) (Lift1 Snd) sigma)
                                 (Lift2 (constN 1)) sigma) A B)
                      L2_target)
        eL2 =
          let e1 = Fan_eq (Fan (Lift2 (constN 1)) (Lift1 Snd) sigma)
                            (Lift2 (constN 1)) sigma A B
              e2 = ruleTrans (congL sigma (ap2 (Lift2 (constN 1)) A B) eL1)
                              (congR sigma L1_target eOne)
          in ruleTrans e1 e2

        ------------------------------------------------------------
        -- Layer 3: addSigma L2 fuelPrev_proj.

        L3_target : Term
        L3_target = ap2 sigma L2_target fuelR_xy

        eL3 :
          Deriv (eqF (ap2 (Fan (Fan (Fan (Lift2 (constN 1)) (Lift1 Snd) sigma)
                                       (Lift2 (constN 1)) sigma)
                                 (Lift2 Snd) sigma) A B)
                      L3_target)
        eL3 =
          let e1 = Fan_eq (Fan (Fan (Lift2 (constN 1)) (Lift1 Snd) sigma)
                                 (Lift2 (constN 1)) sigma)
                            (Lift2 Snd) sigma A B
              e2 = ruleTrans (congL sigma (ap2 (Lift2 Snd) A B) eL2)
                              (congR sigma L2_target eFP)
          in ruleTrans e1 e2

        ------------------------------------------------------------
        -- Layer 4: addSigma L3 oneFun2.

        L4_target : Term
        L4_target = ap2 sigma L3_target oneT

        eL4 :
          Deriv (eqF (ap2 (Fan
                              (Fan (Fan (Fan (Lift2 (constN 1)) (Lift1 Snd) sigma)
                                        (Lift2 (constN 1)) sigma)
                                   (Lift2 Snd) sigma)
                              (Lift2 (constN 1)) sigma) A B)
                      L4_target)
        eL4 =
          let e1 = Fan_eq (Fan (Fan (Fan (Lift2 (constN 1)) (Lift1 Snd) sigma)
                                        (Lift2 (constN 1)) sigma)
                                 (Lift2 Snd) sigma)
                            (Lift2 (constN 1)) sigma A B
              e2 = ruleTrans (congL sigma (ap2 (Lift2 (constN 1)) A B) eL3)
                              (congR sigma L3_target eOne)
          in ruleTrans e1 e2

        ------------------------------------------------------------
        -- Layer 5: addSigma L4 fuelH1_at_Fun2.

        L5_target : Term
        L5_target = ap2 sigma L4_target fh1v

        eL5 :
          Deriv (eqF (ap2 fuel_next_Fun2 A B) L5_target)
        eL5 =
          let e1 = Fan_eq (Fan
                              (Fan (Fan (Fan (Lift2 (constN 1)) (Lift1 Snd) sigma)
                                        (Lift2 (constN 1)) sigma)
                                   (Lift2 Snd) sigma)
                              (Lift2 (constN 1)) sigma)
                            (Fan (Lift1 Fst) (Lift2 Fst) fH1)
                            sigma A B
              e2 = ruleTrans (congL sigma (ap2 (Fan (Lift1 Fst) (Lift2 Fst) fH1) A B)
                                       eL4)
                              (congR sigma L4_target eFH1)
          in ruleTrans e1 e2

    in eL5

  ------------------------------------------------------------------------
  -- Section 4d.  The motive Pform and the ruleIndNat 2 universal theorem.

  -- The R-code (closed).
  Rc : Term
  Rc = mcode2 (R g h1 h2)

  -- The params expression as a Term-form.
  paramsExpr : Term
  paramsExpr = ap2 pi (var 0) (ap2 pi (var 1) (var 3))

  -- K-at-y_cur:  Stack paramsExpr (sub var0 var2).
  -- Spell out var2 (the induction position) for clarity.

  -- The motive.
  Pform : Formula
  Pform =
    imp (leq (var 2) (var 0))
         (eqF (ap2 (iter step)
                    (cfgEV Rc (ap2 pi (var 3) (var 2))
                              (ap2 Stack paramsExpr (ap2 sub (var 0) (var 2))))
                    (ap2 fuelR_combinator (var 3) (var 2)))
              (cfgRT (ap2 (R g h1 h2) (var 3) (var 2))
                      (ap2 Stack paramsExpr (ap2 sub (var 0) (var 2)))))

  ------------------------------------------------------------------------
  -- Section 4d.1.  Base case.

  baseCase : Deriv (substF (suc (suc zero)) O Pform)
  baseCase =
    let -- After substF, var 2 := O.  var 0, var 1, var 3 unchanged.
        --
        -- Conclusion form:
        --   imp (leq O (var 0))
        --        (eqF (iter step (cfgEV Rc (pi (var 3) O) (Stack paramsExpr (sub (var 0) O)))
        --                         (fuelR x O))
        --             (cfgRT (R x O) (Stack paramsExpr (sub (var 0) O))))

        y_top : Term
        y_top = var 0

        x : Term
        x = var 3

        K_base : Term
        K_base = ap2 Stack paramsExpr (ap2 sub y_top O)

        cInit : Term
        cInit = cfgEV Rc (ap2 pi x O) K_base

        cMid : Term
        cMid = cfgEV (mcode1 g) x K_base

        cAfterG : Term
        cAfterG = cfgRT (ap1 g x) K_base

        cFinal : Term
        cFinal = cfgRT (ap2 (R g h1 h2) x O) K_base

        ------------------------------------------------------------
        -- Run segment 1: stepU_at_evRbase.

        step1 : Deriv (eqF (ap1 step cInit) cMid)
        step1 = stepU_at_evRbase g h1 h2 x K_base

        run1 : Deriv (eqF (ap2 (iter step) cInit (ap1 s O)) cMid)
        run1 = iter-step1 cInit cMid step1

        -- Run segment 2: bG.runs1 x K_base.
        runG : Deriv (eqF (ap2 (iter step) cMid (ap1 fG x)) cAfterG)
        runG = runs1 bG x K_base

        ------------------------------------------------------------
        -- Combine via iter_add_T.

        fuel12 : Term
        fuel12 = ap2 sigma (ap1 s O) (ap1 fG x)

        run12 : Deriv (eqF (ap2 (iter step) cInit fuel12) cAfterG)
        run12 =
          ruleTrans (iter_add_T cInit (ap1 s O) (ap1 fG x))
            (ruleTrans (congL (iter step) (ap1 fG x) run1) runG)

        ------------------------------------------------------------
        -- Rewrite value cAfterG -> cFinal.

        eVal : Deriv (eqF (ap1 g x) (ap2 (R g h1 h2) x O))
        eVal = ruleSym (ax_R_base g h1 h2 x)

        eRT : Deriv (eqF cAfterG cFinal)
        eRT = cfgRT-val-rw (ap1 g x) (ap2 (R g h1 h2) x O) K_base eVal

        run12_val : Deriv (eqF (ap2 (iter step) cInit fuel12) cFinal)
        run12_val = ruleTrans run12 eRT

        ------------------------------------------------------------
        -- Rewrite fuel fuel12 -> ap2 fuelR_combinator x O.

        eFuel1 : Deriv (eqF (ap1 (constN 1) x) (ap1 s O))
        eFuel1 = constN_eq 1 x

        eFuel2 : Deriv (eqF fuel12 (ap2 sigma (ap1 (constN 1) x) (ap1 fG x)))
        eFuel2 = congL sigma (ap1 fG x) (ruleSym eFuel1)

        eFuel3 : Deriv (eqF (ap2 sigma (ap1 (constN 1) x) (ap1 fG x))
                             (ap1 Snd (ap2 paired_R x O)))
        eFuel3 = ruleSym (Snd_paired_R_at_O x)

        eFuel4 : Deriv (eqF (ap1 Snd (ap2 paired_R x O))
                             (ap2 fuelR_combinator x O))
        eFuel4 = Snd_paired_R_eq x O

        eFuel : Deriv (eqF fuel12 (ap2 fuelR_combinator x O))
        eFuel = ruleTrans eFuel2 (ruleTrans eFuel3 eFuel4)

        eFuel_iter :
          Deriv (eqF (ap2 (iter step) cInit fuel12)
                      (ap2 (iter step) cInit (ap2 fuelR_combinator x O)))
        eFuel_iter = congR (iter step) cInit eFuel

        conclusion :
          Deriv (eqF (ap2 (iter step) cInit (ap2 fuelR_combinator x O)) cFinal)
        conclusion = ruleTrans (ruleSym eFuel_iter) run12_val

        ------------------------------------------------------------
        -- Wrap in imp (leq O y_top).

        premise : Formula
        premise = leq O y_top

        wrapped :
          Deriv (imp premise
                      (eqF (ap2 (iter step) cInit (ap2 fuelR_combinator x O))
                           cFinal))
        wrapped = mp (axK _ premise) conclusion

        ------------------------------------------------------------
        -- Bridge:  the expected type is  Deriv (substF 2 O Pform) ,  whose
        -- Rc position contains  substT 2 O Rc  rather than  Rc .  Since
        -- Rc = mcode2 (R g h1 h2) is closed (ClosedAtVar 2 Rc), the two
        -- forms are propositionally equal.  Use eqSubst to align.

        cav-Rc : ClosedAtVar (suc (suc zero)) Rc
        cav-Rc = cav-mcode2 (suc (suc zero)) (R g h1 h2)

        eq-Rc : Eq (substT (suc (suc zero)) O Rc) Rc
        eq-Rc = cavSubst cav-Rc O

        Pred : Term -> Set
        Pred rc =
          Deriv (imp premise
                      (eqF (ap2 (iter step)
                                  (cfgEV rc (ap2 pi x O) K_base)
                                  (ap2 fuelR_combinator x O))
                           cFinal))

    in eqSubst Pred (eqSym eq-Rc) wrapped

  ------------------------------------------------------------------------
  -- Section 4d.2.  Step case.

  stepCase :
    Deriv (imp Pform (substF (suc (suc zero)) (ap1 s (var 2)) Pform))
  stepCase =
    let y_top : Term
        y_top = var 0

        x : Term
        x = var 3

        yC : Term
        yC = var 2

        yN : Term
        yN = ap1 s yC

        -- Hypotheses.
        HypIH : Formula
        HypIH = Pform

        HypNew : Formula
        HypNew = leq yN y_top

        ------------------------------------------------------------
        -- K-shorthand.

        Knext : Term
        Knext = ap2 Stack paramsExpr (ap2 sub y_top yN)

        Kcur : Term
        Kcur = ap2 Stack paramsExpr (ap2 sub y_top yC)

        K_konsForm : Term
        K_konsForm = kons (frmApp2 h1c (ap2 h2 x yC)) Knext

        -- Configs.
        cInitN : Term
        cInitN = cfgEV Rc (ap2 pi x yN) Knext

        cAfter1 : Term
        cAfter1 =
          cfgEV (mcode2 h2) (ap2 pi x yC)
                (kons (frmR1 Rc h1c x yC) Knext)

        cAfter2 : Term
        cAfter2 =
          cfgRT (ap2 h2 x yC) (kons (frmR1 Rc h1c x yC) Knext)

        cAfter3 : Term
        cAfter3 = cfgEV Rc (ap2 pi x yC) K_konsForm

        cAfter3_Kcur : Term
        cAfter3_Kcur = cfgEV Rc (ap2 pi x yC) Kcur

        cAfter4 : Term
        cAfter4 = cfgRT (ap2 (R g h1 h2) x yC) Kcur

        cAfter4_konsForm : Term
        cAfter4_konsForm = cfgRT (ap2 (R g h1 h2) x yC) K_konsForm

        cAfter5 : Term
        cAfter5 =
          cfgEV h1c (ap2 pi (ap2 h2 x yC) (ap2 (R g h1 h2) x yC)) Knext

        cAfter6 : Term
        cAfter6 =
          cfgRT (ap2 h1 (ap2 h2 x yC) (ap2 (R g h1 h2) x yC)) Knext

        cFinalN : Term
        cFinalN = cfgRT (ap2 (R g h1 h2) x yN) Knext

        oneT : Term
        oneT = ap1 s O

        fH2v : Term
        fH2v = ap2 fH2 x yC

        fuelR_yC : Term
        fuelR_yC = ap2 fuelR_combinator x yC

        h2val : Term
        h2val = ap2 h2 x yC

        Rval_yC : Term
        Rval_yC = ap2 (R g h1 h2) x yC

        fH1v : Term
        fH1v = ap2 fH1 h2val Rval_yC

        ------------------------------------------------------------
        -- Segment 1: evRstep transition (unconditional).
        --   step cInitN = cAfter1.
        step_seg1 : Deriv (eqF (ap1 step cInitN) cAfter1)
        step_seg1 = stepU_at_evRstep g h1 h2 x yC Knext

        run_seg1 : Deriv (eqF (ap2 (iter step) cInitN oneT) cAfter1)
        run_seg1 = iter-step1 cInitN cAfter1 step_seg1

        ------------------------------------------------------------
        -- Segment 2: bH2.runs2 x yC K_for_h2.
        run_seg2 : Deriv (eqF (ap2 (iter step) cAfter1 fH2v) cAfter2)
        run_seg2 = runs2 bH2 x yC (kons (frmR1 Rc h1c x yC) Knext)

        ------------------------------------------------------------
        -- Segment 3: rtR1 transition (unconditional).
        step_seg3 : Deriv (eqF (ap1 step cAfter2) cAfter3)
        step_seg3 = stepU_at_rtR1 (ap2 h2 x yC) Rc h1c x yC Knext

        run_seg3 : Deriv (eqF (ap2 (iter step) cAfter2 oneT) cAfter3)
        run_seg3 = iter-step1 cAfter2 cAfter3 step_seg3

        ------------------------------------------------------------
        -- Combine segments 1-3 unconditionally.

        fuel123 : Term
        fuel123 = ap2 sigma (ap2 sigma oneT fH2v) oneT

        run_seg12 :
          Deriv (eqF (ap2 (iter step) cInitN (ap2 sigma oneT fH2v)) cAfter2)
        run_seg12 =
          ruleTrans (iter_add_T cInitN oneT fH2v)
            (ruleTrans (congL (iter step) fH2v run_seg1) run_seg2)

        run_seg123 :
          Deriv (eqF (ap2 (iter step) cInitN fuel123) cAfter3)
        run_seg123 =
          ruleTrans (iter_add_T cInitN (ap2 sigma oneT fH2v) oneT)
            (ruleTrans (congL (iter step) oneT run_seg12) run_seg3)

        ------------------------------------------------------------
        -- Segment 4: IH at yC under HypNew.
        --
        -- IH = Pform = imp (leq yC y_top) (eqF (iter step cInit_at_Kcur fuelR_yC) (cfgRT (R x yC) Kcur))
        --
        -- Under HypNew, T80 gives leq yC y_top, so we can mp the IH.

        T80_at_imp : Deriv (imp HypNew (leq yC y_top))
        T80_at_imp = ruleInst2 zero yC (suc zero) y_top refl T80

        -- Lift T80_at_imp to under HypIH.
        T80_at_under :
          Deriv (imp HypIH (imp HypNew (leq yC y_top)))
        T80_at_under = liftP HypIH T80_at_imp

        -- identP HypIH gives imp HypIH HypIH = imp HypIH (imp (leq yC y_top) (eqF ...))
        idP_IH :
          Deriv (imp HypIH (imp (leq yC y_top)
                                  (eqF (ap2 (iter step) cAfter3_Kcur fuelR_yC) cAfter4)))
        idP_IH = identP HypIH

        -- Weaken HypNew into the middle of idP_IH.
        idP_IH_weakened :
          Deriv (imp HypIH (imp HypNew
                                  (imp (leq yC y_top)
                                        (eqF (ap2 (iter step) cAfter3_Kcur fuelR_yC) cAfter4))))
        idP_IH_weakened = weakenUnder HypNew idP_IH

        -- Apply T80_at_under to discharge (leq yC y_top) inside.
        IH_applied :
          Deriv (imp HypIH (imp HypNew
                                  (eqF (ap2 (iter step) cAfter3_Kcur fuelR_yC) cAfter4)))
        IH_applied = bCombTwo idP_IH_weakened T80_at_under

        ------------------------------------------------------------
        -- Use Stack-unfold-at-current-imp at (y_top, var 1 = K_outer, x, yC).

        stack_unfold_imp :
          Deriv (imp HypNew (eqF Kcur K_konsForm))
        stack_unfold_imp = Stack-unfold-at-current-imp y_top (var 1) x yC

        -- Reversed form: imp HypNew (eqF K_konsForm Kcur).
        stack_unfold_imp_sym :
          Deriv (imp HypNew (eqF K_konsForm Kcur))
        stack_unfold_imp_sym =
          bComb (liftP HypNew (eqSymImp Kcur K_konsForm)) stack_unfold_imp

        ------------------------------------------------------------
        -- Lift stack_unfold to under both HypIH and HypNew.

        stack_unfold_two :
          Deriv (imp HypIH (imp HypNew (eqF Kcur K_konsForm)))
        stack_unfold_two = liftP HypIH stack_unfold_imp

        stack_unfold_two_sym :
          Deriv (imp HypIH (imp HypNew (eqF K_konsForm Kcur)))
        stack_unfold_two_sym = liftP HypIH stack_unfold_imp_sym

        ------------------------------------------------------------
        -- Rewrite the cfgEV's K position via stack_unfold.
        --
        -- We have: eqF Kcur K_konsForm under (HypIH, HypNew).
        -- cfgEV_kont rewrite gives: eqF (cfgEV Rc (pi x yC) Kcur) (cfgEV Rc (pi x yC) K_konsForm).
        -- = eqF cAfter3_Kcur cAfter3.

        cfgEV_K_eq :
          Deriv (imp HypIH (imp HypNew (eqF cAfter3_Kcur cAfter3)))
        cfgEV_K_eq =
          let cong_pi_inner :
                Deriv (imp HypIH (imp HypNew
                                        (eqF (ap2 pi (ap2 pi Rc (ap2 pi x yC)) Kcur)
                                             (ap2 pi (ap2 pi Rc (ap2 pi x yC)) K_konsForm))))
              cong_pi_inner =
                bCombTwo
                  (liftP HypIH
                    (liftP HypNew
                      (ax_eqCongR pi Kcur K_konsForm (ap2 pi Rc (ap2 pi x yC)))))
                  stack_unfold_two
              cong_pi_outer :
                Deriv (imp HypIH (imp HypNew
                                        (eqF cAfter3_Kcur cAfter3)))
              cong_pi_outer =
                bCombTwo
                  (liftP HypIH
                    (liftP HypNew
                      (ax_eqCongR pi (ap2 pi (ap2 pi Rc (ap2 pi x yC)) Kcur)
                                        (ap2 pi (ap2 pi Rc (ap2 pi x yC)) K_konsForm)
                                        (natCode tagEV))))
                  cong_pi_inner
          in cong_pi_outer

        -- cfgRT K-rewrite: eqF cAfter4 cAfter4_konsForm under (HypIH, HypNew).
        cfgRT_K_eq :
          Deriv (imp HypIH (imp HypNew (eqF cAfter4 cAfter4_konsForm)))
        cfgRT_K_eq =
          let cong_pi_inner :
                Deriv (imp HypIH (imp HypNew
                                        (eqF (ap2 pi Rval_yC Kcur)
                                             (ap2 pi Rval_yC K_konsForm))))
              cong_pi_inner =
                bCombTwo
                  (liftP HypIH
                    (liftP HypNew
                      (ax_eqCongR pi Kcur K_konsForm Rval_yC)))
                  stack_unfold_two
              cong_pi_outer :
                Deriv (imp HypIH (imp HypNew
                                        (eqF cAfter4 cAfter4_konsForm)))
              cong_pi_outer =
                bCombTwo
                  (liftP HypIH
                    (liftP HypNew
                      (ax_eqCongR pi (ap2 pi Rval_yC Kcur)
                                        (ap2 pi Rval_yC K_konsForm)
                                        (natCode tagRT))))
                  cong_pi_inner
          in cong_pi_outer

        ------------------------------------------------------------
        -- IH applied at K_konsForm = under HypIH, HypNew, gives
        --   eqF (iter step cAfter3 fuelR_yC) cAfter4_konsForm.
        --
        -- We have:
        --   IH_applied : eqF (iter step cAfter3_Kcur fuelR_yC) cAfter4
        --   cfgEV_K_eq : eqF cAfter3_Kcur cAfter3
        --   cfgRT_K_eq : eqF cAfter4 cAfter4_konsForm
        --
        -- Strategy: rewrite iter step's first arg via cfgEV_K_eq (reversed),
        -- then chain with IH_applied, then chain with cfgRT_K_eq.

        cfgEV_K_eq_sym :
          Deriv (imp HypIH (imp HypNew (eqF cAfter3 cAfter3_Kcur)))
        cfgEV_K_eq_sym =
          bCombTwo
            (liftP HypIH (liftP HypNew (eqSymImp cAfter3_Kcur cAfter3)))
            cfgEV_K_eq

        cong_iter_step_K_sym :
          Deriv (imp HypIH (imp HypNew
                                  (eqF (ap2 (iter step) cAfter3 fuelR_yC)
                                       (ap2 (iter step) cAfter3_Kcur fuelR_yC))))
        cong_iter_step_K_sym =
          bCombTwo
            (liftP HypIH
              (liftP HypNew
                (ax_eqCongL (iter step) cAfter3 cAfter3_Kcur fuelR_yC)))
            cfgEV_K_eq_sym

        IH_at_konsForm :
          Deriv (imp HypIH (imp HypNew
                                  (eqF (ap2 (iter step) cAfter3 fuelR_yC) cAfter4_konsForm)))
        IH_at_konsForm =
          transUnderTwo cong_iter_step_K_sym
            (transUnderTwo IH_applied cfgRT_K_eq)

        ------------------------------------------------------------
        -- Lift run_seg123 to under HypIH, HypNew.
        run_seg123_two :
          Deriv (imp HypIH (imp HypNew
                                  (eqF (ap2 (iter step) cInitN fuel123) cAfter3)))
        run_seg123_two = liftP HypIH (liftP HypNew run_seg123)

        ------------------------------------------------------------
        -- Compose segments 1-3 with IH.

        -- iter_add_T cInitN fuel123 fuelR_yC :
        --   iter step cInitN (sigma fuel123 fuelR_yC) = iter step (iter step cInitN fuel123) fuelR_yC.

        iter_add_seg_IH :
          Deriv (eqF (ap2 (iter step) cInitN (ap2 sigma fuel123 fuelR_yC))
                      (ap2 (iter step) (ap2 (iter step) cInitN fuel123) fuelR_yC))
        iter_add_seg_IH = iter_add_T cInitN fuel123 fuelR_yC

        -- congL on run_seg123_two: under (IH, HypNew),
        --   eqF (iter step (iter step cInitN fuel123) fuelR_yC) (iter step cAfter3 fuelR_yC).
        cong_after_segs :
          Deriv (imp HypIH (imp HypNew
                                  (eqF (ap2 (iter step) (ap2 (iter step) cInitN fuel123) fuelR_yC)
                                       (ap2 (iter step) cAfter3 fuelR_yC))))
        cong_after_segs =
          bCombTwo
            (liftP HypIH
              (liftP HypNew
                (ax_eqCongL (iter step) (ap2 (iter step) cInitN fuel123) cAfter3 fuelR_yC)))
            run_seg123_two

        -- Combine: under (IH, HypNew),
        --   eqF (iter step cInitN (sigma fuel123 fuelR_yC)) cAfter4_konsForm.
        run_after_IH :
          Deriv (imp HypIH (imp HypNew
                                  (eqF (ap2 (iter step) cInitN (ap2 sigma fuel123 fuelR_yC))
                                       cAfter4_konsForm)))
        run_after_IH =
          transUnderTwo (liftP HypIH (liftP HypNew iter_add_seg_IH))
            (transUnderTwo cong_after_segs IH_at_konsForm)

        ------------------------------------------------------------
        -- Segment 5: rtApp2 transition (unconditional).
        step_seg5 :
          Deriv (eqF (ap1 step cAfter4_konsForm) cAfter5)
        step_seg5 = stepU_at_rtApp2 Rval_yC h1c h2val Knext

        run_seg5 :
          Deriv (eqF (ap2 (iter step) cAfter4_konsForm oneT) cAfter5)
        run_seg5 = iter-step1 cAfter4_konsForm cAfter5 step_seg5

        ------------------------------------------------------------
        -- Segment 6: bH1.runs2 (h2 x yC) (R x yC) Knext.
        run_seg6 : Deriv (eqF (ap2 (iter step) cAfter5 fH1v) cAfter6)
        run_seg6 = runs2 bH1 h2val Rval_yC Knext

        ------------------------------------------------------------
        -- Combine seg 5 and 6.

        fuel56 : Term
        fuel56 = ap2 sigma oneT fH1v

        run_seg56 :
          Deriv (eqF (ap2 (iter step) cAfter4_konsForm fuel56) cAfter6)
        run_seg56 =
          ruleTrans (iter_add_T cAfter4_konsForm oneT fH1v)
            (ruleTrans (congL (iter step) fH1v run_seg5) run_seg6)

        ------------------------------------------------------------
        -- Lift run_seg56 to under (IH, HypNew).
        run_seg56_two :
          Deriv (imp HypIH (imp HypNew
                                  (eqF (ap2 (iter step) cAfter4_konsForm fuel56) cAfter6)))
        run_seg56_two = liftP HypIH (liftP HypNew run_seg56)

        ------------------------------------------------------------
        -- Compose: iter_add_T after IH-result with seg 56.

        fuel_full : Term
        fuel_full = ap2 sigma (ap2 sigma fuel123 fuelR_yC) fuel56

        iter_add_after_IH :
          Deriv (eqF (ap2 (iter step) cInitN
                            (ap2 sigma (ap2 sigma fuel123 fuelR_yC) fuel56))
                      (ap2 (iter step)
                            (ap2 (iter step) cInitN (ap2 sigma fuel123 fuelR_yC))
                            fuel56))
        iter_add_after_IH =
          iter_add_T cInitN (ap2 sigma fuel123 fuelR_yC) fuel56

        cong_after_IH :
          Deriv (imp HypIH (imp HypNew
                                  (eqF
                                    (ap2 (iter step)
                                          (ap2 (iter step) cInitN (ap2 sigma fuel123 fuelR_yC))
                                          fuel56)
                                    (ap2 (iter step) cAfter4_konsForm fuel56))))
        cong_after_IH =
          bCombTwo
            (liftP HypIH
              (liftP HypNew
                (ax_eqCongL (iter step)
                            (ap2 (iter step) cInitN (ap2 sigma fuel123 fuelR_yC))
                            cAfter4_konsForm
                            fuel56)))
            run_after_IH

        run_full :
          Deriv (imp HypIH (imp HypNew
                                  (eqF (ap2 (iter step) cInitN fuel_full) cAfter6)))
        run_full =
          transUnderTwo (liftP HypIH (liftP HypNew iter_add_after_IH))
            (transUnderTwo cong_after_IH run_seg56_two)

        ------------------------------------------------------------
        -- Rewrite final value: h1 (h2 x yC) (R x yC) = R x yN.
        -- ax_R_step g h1 h2 x yC : R x (s yC) = h1 (h2 x yC) (R x yC).
        -- ruleSym + cfgRT_val_rw.

        eVal :
          Deriv (eqF (ap2 h1 h2val Rval_yC) (ap2 (R g h1 h2) x yN))
        eVal = ruleSym (ax_R_step g h1 h2 x yC)

        eRT_final :
          Deriv (eqF cAfter6 cFinalN)
        eRT_final = cfgRT-val-rw
                      (ap2 h1 h2val Rval_yC)
                      (ap2 (R g h1 h2) x yN)
                      Knext eVal

        run_to_finalN :
          Deriv (imp HypIH (imp HypNew
                                  (eqF (ap2 (iter step) cInitN fuel_full) cFinalN)))
        run_to_finalN =
          transUnderTwo run_full
            (liftP HypIH (liftP HypNew eRT_final))

        ------------------------------------------------------------
        -- Rewrite fuel: fuel_full -> ap2 fuelR_combinator x yN.
        --
        -- fuel_full = sigma (sigma fuel123 fuelR_yC) fuel56
        --           = sigma (sigma (sigma (sigma oneT fH2v) oneT) fuelR_yC) (sigma oneT fH1v)
        --
        -- The motive's fuel at yN is fuelR_xy_N = ap2 fuelR_combinator x yN.
        --
        -- By axPost: fuelR x yN = Snd (paired_R x yN).
        -- By Snd_paired_R_at_s x yC: Snd (paired_R x yN) = ap2 fuel_next_Fun2 (F3 x yC) (paired_R x yC).
        -- By fuel-next-unfold x yC: ap2 fuel_next_Fun2 (F3 x yC) (paired_R x yC) =
        --   sigma (sigma (sigma (sigma (sigma oneT fH2v) oneT) fuelR_yC) oneT) fH1v.
        --
        -- Compare to our fuel_full:
        --   fuel_full = sigma (sigma (sigma (sigma oneT fH2v) oneT) fuelR_yC) (sigma oneT fH1v)
        --
        -- These DIFFER in nesting:
        --   target = sigma (sigma (sigma (sigma (sigma oneT fH2v) oneT) fuelR_yC) oneT) fH1v
        --   ours   = sigma (sigma (sigma (sigma oneT fH2v) oneT) fuelR_yC) (sigma oneT fH1v)
        --
        -- Associativity of sigma is NOT (in general) a definitional equality.
        -- BUT: iter step c (sigma f1 (sigma f2 f3)) = iter step c (sigma (sigma f1 f2) f3)
        -- IS provable via iter_add_T.  Both sides equal
        -- iter step (iter step (iter step c f1) f2) f3.
        --
        -- So we'll bridge via the iter level, not the fuel level.

        ------------------------------------------------------------
        -- Define the target nested form (matching fuel-next-unfold).

        target_fuel : Term
        target_fuel =
          ap2 sigma
              (ap2 sigma
                  (ap2 sigma
                    (ap2 sigma
                      (ap2 sigma oneT fH2v) oneT)
                    fuelR_yC) oneT) fH1v

        -- Bridge fuel: target_fuel via:
        --   target_fuel = ap2 fuel_next_Fun2 (F3 x yC) (paired_R x yC)  [ruleSym fuel-next-unfold]
        --              = ap1 Snd (paired_R x yN)                         [ruleSym Snd_paired_R_at_s]
        --              = ap2 fuelR_combinator x yN                       [Snd_paired_R_eq]
        eTarget_fuelR :
          Deriv (eqF target_fuel (ap2 fuelR_combinator x yN))
        eTarget_fuelR =
          let e1 : Deriv (eqF target_fuel (ap2 fuel_next_Fun2 (ap2 F3 x yC) (ap2 paired_R x yC)))
              e1 = ruleSym (fuel-next-unfold x yC)
              e2 : Deriv (eqF (ap2 fuel_next_Fun2 (ap2 F3 x yC) (ap2 paired_R x yC))
                                (ap1 Snd (ap2 paired_R x yN)))
              e2 = ruleSym (Snd_paired_R_at_s x yC)
              e3 : Deriv (eqF (ap1 Snd (ap2 paired_R x yN))
                                (ap2 fuelR_combinator x yN))
              e3 = Snd_paired_R_eq x yN
          in ruleTrans e1 (ruleTrans e2 e3)

        ------------------------------------------------------------
        -- Equate iter step cInitN fuel_full with iter step cInitN target_fuel via
        -- iter_add_T re-association.
        --
        -- iter step cInitN fuel_full
        --   = iter step cInitN (sigma (sigma fuel123 fuelR_yC) (sigma oneT fH1v))
        --   = iter step (iter step cInitN (sigma fuel123 fuelR_yC)) (sigma oneT fH1v)    [iter_add_T]
        --   = iter step (iter step (iter step cInitN (sigma fuel123 fuelR_yC)) oneT) fH1v    [iter_add_T]
        --
        -- iter step cInitN target_fuel
        --   = iter step cInitN (sigma (sigma (sigma (sigma (sigma oneT fH2v) oneT) fuelR_yC) oneT) fH1v)
        --   = iter step (iter step cInitN (sigma (sigma (sigma (sigma oneT fH2v) oneT) fuelR_yC) oneT)) fH1v   [iter_add_T]
        --   = iter step (iter step (iter step cInitN (sigma (sigma (sigma oneT fH2v) oneT) fuelR_yC)) oneT) fH1v   [iter_add_T]
        --   ...
        --
        -- This bridging is tedious.  We'll instead show:
        --
        --   iter step cInitN fuel_full = iter step cInitN target_fuel
        --
        -- via repeated iter_add_T application from BOTH sides until they
        -- meet at the fully-unfolded form.
        --
        -- Actually, a cleaner approach: we already have
        --   run_to_finalN : iter step cInitN fuel_full = cFinalN  (under H1, H2)
        -- and we want
        --   iter step cInitN (ap2 fuelR_combinator x yN) = cFinalN
        --
        -- Approach: prove the EQUALITY at iter level:
        --   iter step cInitN fuel_full = iter step cInitN target_fuel
        -- via association at iter level, then chain with eTarget_fuelR.

        -- Fully unfolded form: iter through each segment one at a time.
        --
        -- Let c0 = cInitN.
        -- c1 = iter step c0 oneT       (after seg 1 -- partial)
        -- c2 = iter step c1 fH2v       (after seg 2)
        -- c3 = iter step c2 oneT       (after seg 3)
        -- c4 = iter step c3 fuelR_yC   (after seg 4 -- IH)
        -- c5 = iter step c4 oneT       (after seg 5)
        -- c6 = iter step c5 fH1v       (after seg 6)
        --
        -- Both fuel_full and target_fuel iterate from c0 to c6 (modulo nesting).
        --
        -- iter step c0 fuel_full = iter step (iter step c0 (sigma fuel123 fuelR_yC)) fuel56
        --   = iter step (iter step (iter step c0 fuel123) fuelR_yC) fuel56
        --   = iter step (iter step (iter step (iter step c0 (sigma oneT fH2v)) oneT) fuelR_yC) fuel56
        --   = iter step (iter step (iter step (iter step (iter step c0 oneT) fH2v) oneT) fuelR_yC) fuel56
        --   = iter step c6 (post-segment-iter form)
        --
        -- iter step c0 target_fuel = iter step (iter step c0 (sigma .. oneT)) fH1v
        --   = ...
        --   = iter step c5 fH1v   = c6.

        ------------------------------------------------------------
        -- Strategy:  define c_seg_1 through c_seg_6 explicitly, and
        -- relate both fuel forms to them via iter_add_T.

        c0 : Term
        c0 = cInitN

        c1 : Term
        c1 = ap2 (iter step) c0 oneT

        c2 : Term
        c2 = ap2 (iter step) c1 fH2v

        c3 : Term
        c3 = ap2 (iter step) c2 oneT

        c4 : Term
        c4 = ap2 (iter step) c3 fuelR_yC

        c5 : Term
        c5 = ap2 (iter step) c4 oneT

        c6 : Term
        c6 = ap2 (iter step) c5 fH1v

        -- iter step c0 fuel_full = c6.

        -- Step (a): iter step c0 fuel_full = iter step (iter step c0 (sigma fuel123 fuelR_yC)) fuel56.
        ea : Deriv (eqF (ap2 (iter step) c0 fuel_full)
                          (ap2 (iter step) (ap2 (iter step) c0 (ap2 sigma fuel123 fuelR_yC)) fuel56))
        ea = iter_add_T c0 (ap2 sigma fuel123 fuelR_yC) fuel56

        -- Step (b): iter step c0 (sigma fuel123 fuelR_yC) = iter step (iter step c0 fuel123) fuelR_yC = c4.
        eb1 : Deriv (eqF (ap2 (iter step) c0 (ap2 sigma fuel123 fuelR_yC))
                           (ap2 (iter step) (ap2 (iter step) c0 fuel123) fuelR_yC))
        eb1 = iter_add_T c0 fuel123 fuelR_yC

        -- iter step c0 fuel123 = iter step (iter step c0 (sigma oneT fH2v)) oneT = c3.
        eb2 : Deriv (eqF (ap2 (iter step) c0 fuel123)
                          (ap2 (iter step) (ap2 (iter step) c0 (ap2 sigma oneT fH2v)) oneT))
        eb2 = iter_add_T c0 (ap2 sigma oneT fH2v) oneT

        -- iter step c0 (sigma oneT fH2v) = iter step (iter step c0 oneT) fH2v = c2.
        eb3 : Deriv (eqF (ap2 (iter step) c0 (ap2 sigma oneT fH2v))
                          (ap2 (iter step) (ap2 (iter step) c0 oneT) fH2v))
        eb3 = iter_add_T c0 oneT fH2v

        -- iter step c0 (sigma oneT fH2v) = c2.
        eb3_to_c2 : Deriv (eqF (ap2 (iter step) c0 (ap2 sigma oneT fH2v)) c2)
        eb3_to_c2 = eb3   -- c2 = iter step c1 fH2v = iter step (iter step c0 oneT) fH2v.

        -- iter step c0 fuel123 = c3.
        eb2_to_c3 : Deriv (eqF (ap2 (iter step) c0 fuel123) c3)
        eb2_to_c3 = ruleTrans eb2
                      (congL (iter step) oneT eb3_to_c2)

        -- iter step c0 (sigma fuel123 fuelR_yC) = c4.
        eb1_to_c4 : Deriv (eqF (ap2 (iter step) c0 (ap2 sigma fuel123 fuelR_yC)) c4)
        eb1_to_c4 = ruleTrans eb1
                      (congL (iter step) fuelR_yC eb2_to_c3)

        -- iter step c0 fuel_full = iter step c4 fuel56.
        ea_to_c4 :
          Deriv (eqF (ap2 (iter step) c0 fuel_full)
                      (ap2 (iter step) c4 fuel56))
        ea_to_c4 = ruleTrans ea
                      (congL (iter step) fuel56 eb1_to_c4)

        -- iter step c4 fuel56 = iter step (iter step c4 oneT) fH1v = c6.
        ec1 : Deriv (eqF (ap2 (iter step) c4 fuel56)
                           (ap2 (iter step) c5 fH1v))
        ec1 = iter_add_T c4 oneT fH1v

        ea_to_c6 :
          Deriv (eqF (ap2 (iter step) c0 fuel_full) c6)
        ea_to_c6 = ruleTrans ea_to_c4 ec1

        ------------------------------------------------------------
        -- Now: iter step c0 target_fuel = c6.

        -- target_fuel = sigma (sigma (sigma (sigma (sigma oneT fH2v) oneT) fuelR_yC) oneT) fH1v.

        -- Step (d): iter step c0 target_fuel = iter step (iter step c0 (sigma (sigma (sigma (sigma oneT fH2v) oneT) fuelR_yC) oneT)) fH1v.
        ed : Deriv (eqF (ap2 (iter step) c0 target_fuel)
                         (ap2 (iter step)
                                (ap2 (iter step) c0 (ap2 sigma (ap2 sigma (ap2 sigma (ap2 sigma oneT fH2v) oneT) fuelR_yC) oneT))
                                fH1v))
        ed = iter_add_T c0 (ap2 sigma (ap2 sigma (ap2 sigma (ap2 sigma oneT fH2v) oneT) fuelR_yC) oneT) fH1v

        -- iter step c0 (sigma (... fuelR_yC) oneT) = iter step (iter step c0 (... fuelR_yC)) oneT.
        ed1 : Deriv (eqF (ap2 (iter step) c0 (ap2 sigma (ap2 sigma (ap2 sigma (ap2 sigma oneT fH2v) oneT) fuelR_yC) oneT))
                          (ap2 (iter step) (ap2 (iter step) c0 (ap2 sigma (ap2 sigma (ap2 sigma oneT fH2v) oneT) fuelR_yC)) oneT))
        ed1 = iter_add_T c0 (ap2 sigma (ap2 sigma (ap2 sigma oneT fH2v) oneT) fuelR_yC) oneT

        -- iter step c0 (sigma (... oneT) fuelR_yC) = iter step (iter step c0 (... oneT)) fuelR_yC.
        ed2 : Deriv (eqF (ap2 (iter step) c0 (ap2 sigma (ap2 sigma (ap2 sigma oneT fH2v) oneT) fuelR_yC))
                          (ap2 (iter step) (ap2 (iter step) c0 (ap2 sigma (ap2 sigma oneT fH2v) oneT)) fuelR_yC))
        ed2 = iter_add_T c0 (ap2 sigma (ap2 sigma oneT fH2v) oneT) fuelR_yC

        -- iter step c0 (sigma (sigma oneT fH2v) oneT) = iter step (iter step c0 (sigma oneT fH2v)) oneT = c3.
        ed3 : Deriv (eqF (ap2 (iter step) c0 (ap2 sigma (ap2 sigma oneT fH2v) oneT))
                          (ap2 (iter step) (ap2 (iter step) c0 (ap2 sigma oneT fH2v)) oneT))
        ed3 = iter_add_T c0 (ap2 sigma oneT fH2v) oneT

        -- iter step c0 (sigma (sigma oneT fH2v) oneT) = c3.
        ed3_to_c3 : Deriv (eqF (ap2 (iter step) c0 (ap2 sigma (ap2 sigma oneT fH2v) oneT)) c3)
        ed3_to_c3 = ruleTrans ed3 (congL (iter step) oneT eb3_to_c2)

        -- iter step c0 (sigma (sigma (sigma oneT fH2v) oneT) fuelR_yC) = c4.
        ed2_to_c4 : Deriv (eqF (ap2 (iter step) c0 (ap2 sigma (ap2 sigma (ap2 sigma oneT fH2v) oneT) fuelR_yC)) c4)
        ed2_to_c4 = ruleTrans ed2 (congL (iter step) fuelR_yC ed3_to_c3)

        -- iter step c0 (... oneT) = c5.
        ed1_to_c5 : Deriv (eqF (ap2 (iter step) c0 (ap2 sigma (ap2 sigma (ap2 sigma (ap2 sigma oneT fH2v) oneT) fuelR_yC) oneT)) c5)
        ed1_to_c5 = ruleTrans ed1 (congL (iter step) oneT ed2_to_c4)

        -- iter step c0 target_fuel = c6.
        ed_to_c6 : Deriv (eqF (ap2 (iter step) c0 target_fuel) c6)
        ed_to_c6 = ruleTrans ed (congL (iter step) fH1v ed1_to_c5)

        ------------------------------------------------------------
        -- Equate the two fuel forms via c6.

        e_fuel_eq :
          Deriv (eqF (ap2 (iter step) c0 fuel_full) (ap2 (iter step) c0 target_fuel))
        e_fuel_eq = ruleTrans ea_to_c6 (ruleSym ed_to_c6)

        e_target_eq :
          Deriv (eqF (ap2 (iter step) c0 target_fuel)
                       (ap2 (iter step) c0 (ap2 fuelR_combinator x yN)))
        e_target_eq = congR (iter step) c0 eTarget_fuelR

        e_fuel_to_fuelR :
          Deriv (eqF (ap2 (iter step) c0 fuel_full)
                       (ap2 (iter step) c0 (ap2 fuelR_combinator x yN)))
        e_fuel_to_fuelR = ruleTrans e_fuel_eq e_target_eq

        ------------------------------------------------------------
        -- Combine with run_to_finalN:
        --   under (HypIH, HypNew), iter step c0 fuel_full = cFinalN.
        -- Result:
        --   iter step c0 (fuelR_combinator x yN) = cFinalN under (HypIH, HypNew).

        e_fuel_to_fuelR_sym :
          Deriv (eqF (ap2 (iter step) c0 (ap2 fuelR_combinator x yN))
                       (ap2 (iter step) c0 fuel_full))
        e_fuel_to_fuelR_sym = ruleSym e_fuel_to_fuelR

        conclusion :
          Deriv (imp HypIH (imp HypNew
                                  (eqF (ap2 (iter step) cInitN (ap2 fuelR_combinator x yN))
                                       cFinalN)))
        conclusion =
          transUnderTwo
            (liftP HypIH (liftP HypNew e_fuel_to_fuelR_sym))
            run_to_finalN

        ------------------------------------------------------------
        -- Bridge: same as in baseCase, but at substT 2 (s var 2) Rc.
        --
        -- The expected step-case conclusion is
        --   Deriv (imp Pform (substF 2 (s var 2) Pform)) .
        -- The substF-substituted RHS has  substT 2 (s var 2) Rc  in the
        -- cInit position.  Bridge via eqSubst + cav-Rc .

        cav-Rc : ClosedAtVar (suc (suc zero)) Rc
        cav-Rc = cav-mcode2 (suc (suc zero)) (R g h1 h2)

        eq-Rc-sy : Eq (substT (suc (suc zero)) (ap1 s (var 2)) Rc) Rc
        eq-Rc-sy = cavSubst cav-Rc (ap1 s (var 2))

        PredStep : Term -> Set
        PredStep rc =
          Deriv (imp HypIH (imp HypNew
                                  (eqF (ap2 (iter step)
                                              (cfgEV rc (ap2 pi x yN) Knext)
                                              (ap2 fuelR_combinator x yN))
                                       cFinalN)))

    in eqSubst PredStep (eqSym eq-Rc-sy) conclusion

  ------------------------------------------------------------------------
  -- Section 4d.3.  The universal theorem.

  universal : Deriv Pform
  universal = ruleIndNat (suc (suc zero)) {P = Pform} baseCase stepCase

  ------------------------------------------------------------------------
  -- Section 5.  correct2-R bundle wrapper -- DEFERRED.
  --
  -- The natural plan (specialise universal via 4 ruleInsts: var 3 := x,
  -- var 1 := K, var 0 := y, var 2 := y; mp with leq y y from T73; rewrite
  -- K-form = Stack params (sub y y) to K via Stack-base-at-K0) is BLOCKED
  -- by a meta-level substT issue:
  --
  --   After ruleInst-stack, the resulting Deriv's type has
  --     substT 2 y (substT 0 y (substT 1 K (substT 3 x ...)))
  --   walking THROUGH the formula, including INTO the user-supplied
  --   x, y, K placed at the var positions.  At each opaque user-input
  --   position, substT gets stuck (Agda can't reduce substT k _ y when
  --   y is an opaque Term param).
  --
  --   Concretely: substT 2 y (var 0) reduces to substT 2 y y (the inner
  --   y placed by substT 0 y).  Stuck.  Similar issues at every
  --   user-Term-substituted position.
  --
  -- The PRINCIPLED FIX (deferred to a follow-up refactor) is:
  --
  --   1. Extend T4.StepU2CorrectAPI: add ClosedAtVar 2 (or Closed)
  --      witnesses to Correct1.runs1 (for x, K) and Correct2.runs2 (for
  --      x, y, K) signatures.
  --
  --   2. Update T4.StepU2Correct1New: propagate Closed witnesses
  --      through correct1 / correct2 mutual definitions.  Each kons /
  --      frame-builder K-construction needs structural Closed-witness
  --      construction via closed_ap2 / closed_natCode / closed_mcode1 /
  --      closed_mcode2 (the latter two analogous to the cav-mcode1 /
  --      cav-mcode2 lemmas already in this file).  ~100 LoC of
  --      mechanical propagation.
  --
  --   3. At runs2-R in this file: use ruleInst3 (3-way simultaneous,
  --      vars 0, 1, 3) + ruleInst (var 2), then bridge the substT 2 y
  --      walks via cavSubst at level 2 (constructed from the supplied
  --      Closed witnesses) and the Rc-internal positions via cav-mcode2
  --      at the relevant levels.  ~100-150 LoC of bridging via eqSubst.
  --
  -- Alternative (lower-API-impact but higher new-infrastructure cost):
  -- derive ruleInst4 + simSubstF4 (~500 LoC) to do 4-way simultaneous
  -- substitution in one pass, avoiding the substT-into-opaque issue.
  --
  -- The universal theorem itself (Section 4) is COMPLETE; the bundle
  -- wrapper is the only remaining piece.  Patching T4.StepU2Correct1New
  -- with `open Inner correct2-R-bundle` is also deferred to the same
  -- follow-up.

  -- correct2-R : Correct2 (R g h1 h2)
  -- correct2-R = mkC2 fuelR_combinator runs2-R    -- requires closure refactor.
