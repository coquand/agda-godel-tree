{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.SubLeqIdentities -- the two arithmetic identities about
--  sub (= truncated subtraction)  under  leq , factored out of
-- BRA4/StepU2CorrectR.agda so that BRA4/PeterRec.agda can reuse them
-- without depending on the entire CK-machine completeness proof.
--
-- The two identities:
--
--   identityA :  imp (leq (s var 1) (var 0))
--                 (eqF (sub var 0 var 1)
--                       (s (sub var 0 (s var 1))))
--   -- "Under  s y <= top ,  top - y = 1 + (top - (s y))."
--
--   identityB :  imp (leq (var 1) (var 0))
--                 (eqF (sub var 0 (sub var 0 var 1)) (var 1))
--   -- "Under  y <= top ,  top - (top - y) = y."
--
-- Both are derivable in BRA from the standard Church/Guard arithmetic
-- via the Carneiro-style  _univ  building blocks in
-- BRA3.RecBRA3AtPairUniv  + L_sp + T_sub_S_v01 + T57sub + T_sub_O +
-- T73 + T82 + caseElimUnderTwo .
--
-- This file is a verbatim copy of  StepU2CorrectR.agda  Sections 1-2
-- with the local helpers  transUnderOne / transUnderTwo / weakenUnder
-- (also factored here for reuse).

module BRA4.SubLeqIdentities where

open import BRA4.Base

open import BRA3.Church
  using ( sub ; predecessor ; T_sub_S_v01 )
open import BRA3.ChurchLeq  using ( leq ; T76 )
open import BRA3.ChurchSubSucc using ( T_sub_O ; T57sub )
open import BRA3.ChurchT73  using ( T73 )
open import BRA3.ChurchT82  using ( T82 )
open import BRA3.ChurchPredLemmas using ( L_sp )
open import BRA3.Contrapositive
  using ( axContrapos ; identP ; liftP ; bComb ; bCombTwo ; Q_to_dNeg )
open import BRA3.Logic
  using ( impTrans ; prependEqLeft ; appendEqRight ; eqSymImp )
open import BRA3.RuleInst2  using ( ruleInst2 )
open import BRA3.RecBRA3AtPairUniv
  using ( sub_step_under_le_univ ; not_leq_succ_under_le_univ )
open import BRA3.ChurchLemmaA using ( caseElimUnderTwo )

------------------------------------------------------------------------
-- Section 1.  Identity A.
--
--   imp (leq (s var 1) (var 0))
--        (eqF (sub var 0 var 1) (s (sub var 0 (s var 1))))

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

      step1a : Deriv (imp Hleq (neg H))
      step1a = not_leq_succ_under_le_univ

      step1b : Deriv (imp (neg (neg H)) (neg Hleq))
      step1b = mp (axContrapos Hleq (neg H)) step1a

      step1c : Deriv (imp H (neg (neg H)))
      step1c = Q_to_dNeg H

      step1 : Deriv (imp H (neg (eqF X O)))
      step1 = impTrans step1c step1b

      step2 : Deriv (imp (neg (eqF X O)) (eqF (ap1 s (ap1 predecessor X)) X))
      step2 = ruleInst zero X L_sp

      step3 : Deriv (imp H (eqF (ap1 s (ap1 predecessor X)) X))
      step3 = impTrans step1 step2

      step4_eq : Deriv (eqF Y (ap1 predecessor X))
      step4_eq = T_sub_S_v01

      step4_sY : Deriv (eqF (ap1 s Y) (ap1 s (ap1 predecessor X)))
      step4_sY = cong1 s step4_eq

      step5a : Deriv (imp (eqF (ap1 s (ap1 predecessor X)) X)
                           (eqF (ap1 s Y) X))
      step5a = prependEqLeft (ap1 s Y) (ap1 s (ap1 predecessor X)) X step4_sY

      step5b : Deriv (imp H (eqF (ap1 s Y) X))
      step5b = impTrans step3 step5a

      step5c : Deriv (imp (eqF (ap1 s Y) X) (eqF X (ap1 s Y)))
      step5c = eqSymImp (ap1 s Y) X

  in impTrans step5b step5c

------------------------------------------------------------------------
-- Section 2.  Small reusable helpers : equational transitivity under
-- one / two implication layers, and a simple weakening.

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

weakenUnder :
  (Q : Formula) {P A : Formula} ->
  Deriv (imp P A) -> Deriv (imp P (imp Q A))
weakenUnder Q {P} {A} D =
  let kImp : Deriv (imp P (imp A (imp Q A)))
      kImp = liftP P (axK A Q)
  in bComb kImp D

------------------------------------------------------------------------
-- Section 3.  Identity B.
--
--   imp (leq (var 1) (var 0))
--        (eqF (sub (var 0) (sub (var 0) (var 1))) (var 1))

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
      let step_a : Deriv (imp (leq (var 1) O) (eqF (var 1) O))
          step_a = prependEqLeft (var 1) (ap2 sub (var 1) O) O
                                  (ruleSym (T_sub_O (var 1)))

          step_a_swap : Deriv (imp (leq (var 1) O) (eqF O (var 1)))
          step_a_swap = impTrans step_a (eqSymImp (var 1) O)

          T76_at_inner : Deriv (eqF (ap2 sub O (ap2 sub O (var 1))) O)
          T76_at_inner = ruleInst zero (ap2 sub O (var 1)) T76

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

    T82_at :
      Deriv (imp Hyp_next (imp (neg Hyp_X1) Hyp_Y))
    T82_at = ruleInst2 zero (var 1) (suc zero) (var 0) refl T82

    negX_Y :
      Deriv (imp Pform (imp Hyp_next (imp (neg Hyp_X1) Hyp_Y)))
    negX_Y = liftP Pform T82_at

    LHS_target : Term
    LHS_target = ap2 sub (ap1 s (var 0))
                          (ap2 sub (ap1 s (var 0)) (var 1))

    mid_target : Term
    mid_target = ap2 sub (var 0) (ap2 sub (var 0) (var 1))

    sub_step_at :
      Deriv (imp Hyp_X1
              (eqF (ap2 sub (ap1 s (var 0)) (var 1))
                    (ap1 s (ap2 sub (var 0) (var 1)))))
    sub_step_at = ruleInst2 zero (var 1) (suc zero) (var 0)
                              refl sub_step_under_le_univ

    T57_at :
      Deriv (eqF (ap2 sub (ap1 s (var 0)) (ap1 s (ap2 sub (var 0) (var 1))))
                  (ap2 sub (var 0) (ap2 sub (var 0) (var 1))))
    T57_at = ruleInst2 zero (var 0) (suc zero)
                        (ap2 sub (var 0) (var 1)) refl T57sub

    cong_under_X1 :
      Deriv (imp Hyp_X1 (eqF LHS_target mid_target))
    cong_under_X1 =
      let axCongR_sub :
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

          appR :
            Deriv (imp (eqF LHS_target
                              (ap2 sub (ap1 s (var 0))
                                        (ap1 s (ap2 sub (var 0) (var 1)))))
                        (eqF LHS_target mid_target))
          appR = appendEqRight LHS_target
                   (ap2 sub (ap1 s (var 0)) (ap1 s (ap2 sub (var 0) (var 1))))
                   mid_target T57_at
      in impTrans step_a' appR

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
      let axK_lifted :
            Deriv (imp Pform (imp (imp Hyp_X1 (eqF LHS_target (var 1)))
                                   (imp Hyp_next (imp Hyp_X1 (eqF LHS_target (var 1))))))
          axK_lifted = liftP Pform (axK (imp Hyp_X1 (eqF LHS_target (var 1))) Hyp_next)
      in bComb axK_lifted Q_under_Pform_X1

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

          aR1 :
            Deriv (imp (eqF (ap2 sub (ap1 s (var 0)) (var 1))
                              (ap2 sub (ap1 s (var 0)) (ap1 s (var 0))))
                        (eqF (ap2 sub (ap1 s (var 0)) (var 1)) O))
          aR1 = appendEqRight (ap2 sub (ap1 s (var 0)) (var 1))
                                (ap2 sub (ap1 s (var 0)) (ap1 s (var 0)))
                                O eB

          eC : Deriv (imp Hyp_Y (eqF (ap2 sub (ap1 s (var 0)) (var 1)) O))
          eC = impTrans eA aR1

          axCongR_D :
            Deriv (imp (eqF (ap2 sub (ap1 s (var 0)) (var 1)) O)
                        (eqF LHS_target
                              (ap2 sub (ap1 s (var 0)) O)))
          axCongR_D = ax_eqCongR sub (ap2 sub (ap1 s (var 0)) (var 1)) O
                                  (ap1 s (var 0))

          eD : Deriv (imp Hyp_Y (eqF LHS_target (ap2 sub (ap1 s (var 0)) O)))
          eD = impTrans eC axCongR_D

          eE : Deriv (eqF (ap2 sub (ap1 s (var 0)) O) (ap1 s (var 0)))
          eE = T_sub_O (ap1 s (var 0))

          aR2 :
            Deriv (imp (eqF LHS_target (ap2 sub (ap1 s (var 0)) O))
                        (eqF LHS_target (ap1 s (var 0))))
          aR2 = appendEqRight LHS_target (ap2 sub (ap1 s (var 0)) O) (ap1 s (var 0)) eE

          eEC : Deriv (imp Hyp_Y (eqF LHS_target (ap1 s (var 0))))
          eEC = impTrans eD aR2

          eF : Deriv (imp Hyp_Y (eqF (ap1 s (var 0)) (var 1)))
          eF = eqSymImp (var 1) (ap1 s (var 0))
      in transUnderOne eEC eF

    Y_Rf :
      Deriv (imp Pform (imp Hyp_next (imp Hyp_Y Q_step)))
    Y_Rf = liftP Pform (liftP Hyp_next Y_to_Q_only_Y)

    step_combined :
      Deriv (imp Pform (imp Hyp_next Q_step))
    step_combined = caseElimUnderTwo {P1 = Pform} {P2 = Hyp_next}
                      {X = Hyp_X1} {Y = Hyp_Y} {Rf = Q_step}
                      negX_Y X_Rf Y_Rf

    stepImp : Deriv (imp Pform (substF 0 (ap1 s (var 0)) Pform))
    stepImp = step_combined
