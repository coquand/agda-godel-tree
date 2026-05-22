{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.CoVSpecUniv -- the Closed-free, universal-in-Term versions of
-- the cov_spec step / history-table lemmas.  S4 prerequisites.
--
-- The lemmas in BRA4.CoVSpec take  Closed n  as a premise on the fuel
-- argument.  For S4's  sbt_at_ap1 / sbt_at_ap2  the input  ct  is an
-- arbitrary Term (possibly non-Closed), so we need the Closed-free
-- versions.  These follow BRA3.SubT.Closures.covSubT_step_univ /
-- BRA3.SubT.Closures.HistP_subT_succ_extend pattern.
--
-- Shipped:
--
--   1.  cov_spec_step_univ : universal cov_spec_step (no Closed).
--   2.  HistP_sbt : the table accessor =Snd Snd of cov_spec state.
--   3.  HistP_sbt_succ_extend : table grows under one step (universal).

module BRA4.CoVSpecUniv where

open import BRA4.Base
open import BRA4.CoVSpec

open import BRA3.Church          using ( pi )
open import BRA3.ChurchT117      using ( Fst )
open import BRA3.ChurchT116      using ( Snd )
open import BRA3.PairAlgebra     using
  ( axFst ; axSnd ; compose1U ; compose1U_eq )
open import BRA3.CourseOfValues  using
  ( iter_step_fun ; iter_step_fun_eq_univ )
open import BRA3.RuleInst2       using ( ruleInst2 )

------------------------------------------------------------------------
-- cov_spec_step_univ :  universal-in-Term cov_spec step.
--
--   ap2 (cov_spec base step) spec (ap1 s n)
--     =Deriv= ap1 (state_step_spec step) (ap2 (cov_spec base step) spec n)
--
-- Universal in spec, n : Term.  No Closed premise.  Direct analog of
-- BRA3.SubT.Closures.covSubT_step_univ (lines 59-89 of that file).

cov_spec_step_univ :
  (baseFun : Fun1) (stepFun : Fun2) (spec n : Term) ->
  Deriv (eqF (ap2 (cov_spec baseFun stepFun) spec (ap1 s n))
              (ap1 (state_step_spec stepFun)
                    (ap2 (cov_spec baseFun stepFun) spec n)))
cov_spec_step_univ baseFun stepFun spec n =
  let prev : Term
      prev = ap2 (cov_spec baseFun stepFun) spec n

      e1 : Deriv (eqF (ap2 (cov_spec baseFun stepFun) spec (ap1 s n))
                       (ap2 (iter_step_fun (state_step_spec stepFun))
                            (ap2 v spec n) prev))
      e1 = ax_R_step (initialState_spec baseFun)
                      (iter_step_fun (state_step_spec stepFun))
                      v spec n

      vK : Deriv (eqF (ap2 v spec n) n)
      vK = ax_v spec n

      e1b : Deriv (eqF (ap2 (iter_step_fun (state_step_spec stepFun))
                              (ap2 v spec n) prev)
                        (ap2 (iter_step_fun (state_step_spec stepFun))
                              n prev))
      e1b = congL (iter_step_fun (state_step_spec stepFun)) prev vK

      e2 : Deriv (eqF (ap2 (iter_step_fun (state_step_spec stepFun))
                              n prev)
                       (ap1 (state_step_spec stepFun) prev))
      e2 = ruleInst2 zero n (suc zero) prev refl
                      (iter_step_fun_eq_univ (state_step_spec stepFun))
  in ruleTrans e1 (ruleTrans e1b e2)

------------------------------------------------------------------------
-- HistP_sbt :  the table accessor =  Snd (Snd (cov_spec base step spec K)) .
--
-- The "history table" stored inside the spec-carrying cov state.

HistP_sbt : (baseFun : Fun1) (stepFun : Fun2) (spec K : Term) -> Term
HistP_sbt baseFun stepFun spec K =
  ap1 Snd (ap1 Snd (ap2 (cov_spec baseFun stepFun) spec K))

------------------------------------------------------------------------
-- newVal_at :  the new value to be prepended on the table at the next step.
--
-- = stepFun (Fst (cov_spec base step spec K)) (Snd (cov_spec base step spec K)).

newVal_at : (baseFun : Fun1) (stepFun : Fun2) (spec K : Term) -> Term
newVal_at baseFun stepFun spec K =
  let prev = ap2 (cov_spec baseFun stepFun) spec K
  in ap2 stepFun (ap1 Fst prev) (ap1 Snd prev)

------------------------------------------------------------------------
-- HistP_sbt_succ_extend :
--
--   HistP_sbt base step spec (s K)
--     = pi (newVal_at base step spec K) (HistP_sbt base step spec K)
--
-- Universal in spec, K : Term .  No Closed premise.

HistP_sbt_succ_extend :
  (baseFun : Fun1) (stepFun : Fun2) (spec K : Term) ->
  Deriv (eqF (HistP_sbt baseFun stepFun spec (ap1 s K))
              (ap2 pi (newVal_at baseFun stepFun spec K)
                       (HistP_sbt baseFun stepFun spec K)))
HistP_sbt_succ_extend baseFun stepFun spec K =
  let prev : Term
      prev = ap2 (cov_spec baseFun stepFun) spec K

      -- Step 1: cov_spec spec (s K) = state_step_spec step prev.
      cov_step :
        Deriv (eqF (ap2 (cov_spec baseFun stepFun) spec (ap1 s K))
                    (ap1 (state_step_spec stepFun) prev))
      cov_step = cov_spec_step_univ baseFun stepFun spec K

      -- Step 2: state_step_spec step prev = pi (s (Fst prev)) (pi (Fst (Snd prev)) (pi (step (Fst prev) (Snd prev)) (Snd (Snd prev)))).
      shape :
        Deriv (eqF (ap1 (state_step_spec stepFun) prev)
                    (ap2 pi (ap1 s (ap1 Fst prev))
                            (ap2 pi (ap1 Fst (ap1 Snd prev))
                                    (ap2 pi (ap2 stepFun (ap1 Fst prev) (ap1 Snd prev))
                                            (ap1 Snd (ap1 Snd prev))))))
      shape = state_step_spec_eq stepFun prev

      cov_full :
        Deriv (eqF (ap2 (cov_spec baseFun stepFun) spec (ap1 s K))
                    (ap2 pi (ap1 s (ap1 Fst prev))
                            (ap2 pi (ap1 Fst (ap1 Snd prev))
                                    (ap2 pi (ap2 stepFun (ap1 Fst prev) (ap1 Snd prev))
                                            (ap1 Snd (ap1 Snd prev))))))
      cov_full = ruleTrans cov_step shape

      -- Step 3: Snd (cov_spec ... (s K)) = pi (Fst (Snd prev)) (pi (step ...) (Snd (Snd prev))).
      snd_cov :
        Deriv (eqF (ap1 Snd (ap2 (cov_spec baseFun stepFun) spec (ap1 s K)))
                    (ap1 Snd (ap2 pi (ap1 s (ap1 Fst prev))
                              (ap2 pi (ap1 Fst (ap1 Snd prev))
                                (ap2 pi (ap2 stepFun (ap1 Fst prev) (ap1 Snd prev))
                                        (ap1 Snd (ap1 Snd prev)))))))
      snd_cov = cong1 Snd cov_full

      snd_pi :
        Deriv (eqF (ap1 Snd (ap2 pi (ap1 s (ap1 Fst prev))
                              (ap2 pi (ap1 Fst (ap1 Snd prev))
                                (ap2 pi (ap2 stepFun (ap1 Fst prev) (ap1 Snd prev))
                                        (ap1 Snd (ap1 Snd prev))))))
                    (ap2 pi (ap1 Fst (ap1 Snd prev))
                            (ap2 pi (ap2 stepFun (ap1 Fst prev) (ap1 Snd prev))
                                    (ap1 Snd (ap1 Snd prev)))))
      snd_pi = axSnd (ap1 s (ap1 Fst prev))
                      (ap2 pi (ap1 Fst (ap1 Snd prev))
                          (ap2 pi (ap2 stepFun (ap1 Fst prev) (ap1 Snd prev))
                                  (ap1 Snd (ap1 Snd prev))))

      snd_full :
        Deriv (eqF (ap1 Snd (ap2 (cov_spec baseFun stepFun) spec (ap1 s K)))
                    (ap2 pi (ap1 Fst (ap1 Snd prev))
                            (ap2 pi (ap2 stepFun (ap1 Fst prev) (ap1 Snd prev))
                                    (ap1 Snd (ap1 Snd prev)))))
      snd_full = ruleTrans snd_cov snd_pi

      -- Step 4: Snd (Snd (cov_spec ... (s K))) = pi (step (Fst prev) (Snd prev)) (Snd (Snd prev)).
      -- (Used downstream; kept here to chain.)
      snd_snd_cov :
        Deriv (eqF (ap1 Snd (ap1 Snd (ap2 (cov_spec baseFun stepFun) spec (ap1 s K))))
                    (ap1 Snd (ap2 pi (ap1 Fst (ap1 Snd prev))
                              (ap2 pi (ap2 stepFun (ap1 Fst prev) (ap1 Snd prev))
                                      (ap1 Snd (ap1 Snd prev))))))
      snd_snd_cov = cong1 Snd snd_full

      snd_pi2 :
        Deriv (eqF (ap1 Snd (ap2 pi (ap1 Fst (ap1 Snd prev))
                              (ap2 pi (ap2 stepFun (ap1 Fst prev) (ap1 Snd prev))
                                      (ap1 Snd (ap1 Snd prev)))))
                    (ap2 pi (ap2 stepFun (ap1 Fst prev) (ap1 Snd prev))
                            (ap1 Snd (ap1 Snd prev))))
      snd_pi2 = axSnd (ap1 Fst (ap1 Snd prev))
                       (ap2 pi (ap2 stepFun (ap1 Fst prev) (ap1 Snd prev))
                               (ap1 Snd (ap1 Snd prev)))
  in ruleTrans snd_snd_cov snd_pi2

------------------------------------------------------------------------
-- readOff_state_step_univ :  universal-in-Term form of the readOff at
-- state_step_spec step state.
--
--   readOff_spec (state_step_spec step state)
--     =Deriv= stepFun (Fst state) (Snd state) .
--
-- Direct unfolding via state_step_spec_eq + axSnd/axFst + readOff_spec_eq.

readOff_state_step_univ :
  (stepFun : Fun2) (state : Term) ->
  Deriv (eqF (ap1 readOff_spec (ap1 (state_step_spec stepFun) state))
              (ap2 stepFun (ap1 Fst state) (ap1 Snd state)))
readOff_state_step_univ stepFun state =
  let -- readOff_spec X = Fst (Snd (Snd X)).
      e1 :
        Deriv (eqF (ap1 readOff_spec (ap1 (state_step_spec stepFun) state))
                    (ap1 Fst (ap1 Snd (ap1 Snd (ap1 (state_step_spec stepFun) state)))))
      e1 = readOff_spec_eq (ap1 (state_step_spec stepFun) state)

      -- state_step_spec step state = pi (s (Fst state)) (pi (Fst (Snd state)) (pi (step (Fst state) (Snd state)) (Snd (Snd state)))).
      shape :
        Deriv (eqF (ap1 (state_step_spec stepFun) state)
                    (ap2 pi (ap1 s (ap1 Fst state))
                            (ap2 pi (ap1 Fst (ap1 Snd state))
                                    (ap2 pi (ap2 stepFun (ap1 Fst state) (ap1 Snd state))
                                            (ap1 Snd (ap1 Snd state))))))
      shape = state_step_spec_eq stepFun state

      -- Lift through Snd (Snd (Fst _)).
      snd_step :
        Deriv (eqF (ap1 Snd (ap1 (state_step_spec stepFun) state))
                    (ap2 pi (ap1 Fst (ap1 Snd state))
                            (ap2 pi (ap2 stepFun (ap1 Fst state) (ap1 Snd state))
                                    (ap1 Snd (ap1 Snd state)))))
      snd_step =
        ruleTrans (cong1 Snd shape)
          (axSnd (ap1 s (ap1 Fst state))
                  (ap2 pi (ap1 Fst (ap1 Snd state))
                      (ap2 pi (ap2 stepFun (ap1 Fst state) (ap1 Snd state))
                              (ap1 Snd (ap1 Snd state)))))

      snd_snd_step :
        Deriv (eqF (ap1 Snd (ap1 Snd (ap1 (state_step_spec stepFun) state)))
                    (ap2 pi (ap2 stepFun (ap1 Fst state) (ap1 Snd state))
                            (ap1 Snd (ap1 Snd state))))
      snd_snd_step =
        ruleTrans (cong1 Snd snd_step)
          (axSnd (ap1 Fst (ap1 Snd state))
                  (ap2 pi (ap2 stepFun (ap1 Fst state) (ap1 Snd state))
                          (ap1 Snd (ap1 Snd state))))

      fst_snd_snd :
        Deriv (eqF (ap1 Fst (ap1 Snd (ap1 Snd (ap1 (state_step_spec stepFun) state))))
                    (ap2 stepFun (ap1 Fst state) (ap1 Snd state)))
      fst_snd_snd =
        ruleTrans (cong1 Fst snd_snd_step)
          (axFst (ap2 stepFun (ap1 Fst state) (ap1 Snd state))
                  (ap1 Snd (ap1 Snd state)))
  in ruleTrans e1 fst_snd_snd
