{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.ChaitinG1ChainKdefAlph -- the  checkAlphN -guard analog of
-- T4.ChaitinG1ChainKdef .   Re-pointed from  Kcode Lstar / outKdef Lstar /
-- gLcodeDef Lstar  to  KcodeAlph / outKdefAlph / gLcodeDefAlph .  Body generic.

open import T4.Base

module T4.ChaitinG1ChainKdefAlph (Lstar_meta : Nat) where

open import T4.ThmT            using ( thmT )
open import T4.KdefAlph Lstar_meta using ( KcodeAlph )
open import T4.KdefRecogAlph Lstar_meta using ( outKdefAlph )
open import T4.KdefDiagAlph Lstar_meta using ( gLcodeDefAlph ; gCodeOfDefAlph ; dRT_gLDefAlph )
open import T4.EvalU           using ( mcodeMu ; mcode1 ; mcode2
                                       ; cfgEV ; cfgRT ; cfgHALT
                                       ; kons ; konEmpty
                                       ; frmC1 ; frmApp2 ; tagRT )
open import T4.EvalUEval       using ( evalU ; readout ; readout_halt
                                       ; initF ; initF_eq ; evalU_unfold )
open import T4.EvalUStep       using ( stepU_at_evC_code ; stepU_at_rtC1
                                       ; stepU_at_evU ; stepU_at_rtApp2
                                       ; stepU_at_rtEmpty )
open import T4.StepU2          using ( step )
open import T4.StepU2Reach     using ( iter_add_T )
open import T4.StepU2Correct1New using ( correct2 )
open import T4.StepU2CorrectAPI  using ( Correct2 ; fuelG ; runs2 )
open import T4.ProgEnc         using ( enc )
open import T4.ProgParse       using ( parse )
open import T4.Tags            using ( tag_C )

import T4.ChaitinG1DischargeKdefAlph

open import BRA3.Church          using ( pi ; sigma )
open import BRA3.Fan             using ( Lift1 ; Lift1_eq )
open import BRA3.RuleInst2       using ( simSubstT )
open import BRA3.CourseOfValues  using ( iter )
open import BRA3.RecBRA3AtPairUniv using ( iter_base_univ ; iter_step_univ )

------------------------------------------------------------------------
-- The Chain module.

module ChainKdefAlph
  (w        : Term)
  (x        : Term)
  (h        : Deriv (eqF (ap1 thmT w) (ap1 KcodeAlph x)))
  (sub0_w   : (a : Term) -> Eq (substT zero a w) w)
  (sub1_w   : (a : Term) -> Eq (substT (suc zero) a w) w)
  (sim_w    : (a b : Term) ->
              Eq (simSubstT zero a (suc zero) b w) w)
  where

  open T4.ChaitinG1DischargeKdefAlph.DischargeKdefAlph Lstar_meta w x h sub0_w sub1_w sim_w
    using ( k_max ; fuelMu_fun ; runs_mu ; x' ; dNeg_at_kmax )

  ----------------------------------------------------------------------
  -- Configurations.

  outL : Fun1
  outL = outKdefAlph

  g_outer_code : Term
  g_outer_code = gCodeOfDefAlph      -- = mcode2 (Lift1 outL)

  h1c : Term
  h1c = mcodeMu (mcode1 (T4.ChaitinG1DischargeKdefAlph.DischargeKdefAlph.gFun
                          Lstar_meta w x h sub0_w sub1_w sim_w))

  K1 : Term
  K1 = kons (frmC1 g_outer_code (mcode1 u) O) konEmpty

  K2 : Term
  K2 = kons (frmApp2 g_outer_code k_max) konEmpty

  c0 c1 c2 c3 c4 c5 c6 c6' cH : Term
  c0  = cfgEV gLcodeDefAlph O konEmpty
  c1  = cfgEV h1c O K1
  c2  = cfgRT k_max K1
  c3  = cfgEV (mcode1 u) O K2
  c4  = cfgRT O K2
  c5  = cfgEV g_outer_code (ap2 pi k_max O) konEmpty
  c6  = cfgRT (ap2 (Lift1 outL) k_max O) konEmpty
  c6' = cfgRT (ap1 outL k_max) konEmpty
  cH  = cfgHALT (ap1 outL k_max)

  ----------------------------------------------------------------------
  -- Per-segment derivations.

  bG : Correct2 (Lift1 outL)
  bG = correct2 (Lift1 outL)

  fGouter : Term
  fGouter = ap2 (fuelG bG) k_max O

  seg1_evC : Deriv (eqF (ap1 step c0) c1)
  seg1_evC =
    stepU_at_evC_code g_outer_code h1c (mcode1 u) O konEmpty

  seg2_mu_fuel : Term
  seg2_mu_fuel = ap2 sigma (ap1 s O) (ap2 fuelMu_fun k_max k_max)

  seg2_mu : Deriv (eqF (ap2 (iter step) c1 seg2_mu_fuel) c2)
  seg2_mu = runs_mu O K1

  seg3_rtC1 : Deriv (eqF (ap1 step c2) c3)
  seg3_rtC1 = stepU_at_rtC1 k_max g_outer_code (mcode1 u) O konEmpty

  seg4_evU : Deriv (eqF (ap1 step c3) c4)
  seg4_evU = stepU_at_evU O K2

  seg5_rtApp2 : Deriv (eqF (ap1 step c4) c5)
  seg5_rtApp2 = stepU_at_rtApp2 O g_outer_code k_max konEmpty

  seg6_runs2 : Deriv (eqF (ap2 (iter step) c5 fGouter) c6)
  seg6_runs2 = runs2 bG k_max O konEmpty

  liftBridge : Deriv (eqF (ap2 (Lift1 outL) k_max O) (ap1 outL k_max))
  liftBridge = Lift1_eq outL k_max O

  seg7_bridge : Deriv (eqF c6 c6')
  seg7_bridge =
    congR pi (natCode tagRT) (congL pi konEmpty liftBridge)

  seg8_rtEmpty : Deriv (eqF (ap1 step c6') cH)
  seg8_rtEmpty = stepU_at_rtEmpty (ap1 outL k_max)

  ----------------------------------------------------------------------
  -- Fuel composition helpers.

  iter_step1 : (c c' : Term) ->
                Deriv (eqF (ap1 step c) c') ->
                Deriv (eqF (ap2 (iter step) c (ap1 s O)) c')
  iter_step1 c c' e =
    let e1 = iter_step_univ step c O
        e2 = cong1 step (iter_base_univ step c)
    in ruleTrans e1 (ruleTrans e2 e)

  compStep :
    (cInit cMid cNext prevFuel delta : Term) ->
    Deriv (eqF (ap2 (iter step) cInit prevFuel) cMid) ->
    Deriv (eqF (ap2 (iter step) cMid delta) cNext) ->
    Deriv (eqF (ap2 (iter step) cInit (ap2 sigma prevFuel delta)) cNext)
  compStep cInit cMid cNext prevFuel delta e1 e2 =
    let addF = iter_add_T cInit prevFuel delta
        rwL  = congL (iter step) delta e1
    in ruleTrans addF (ruleTrans rwL e2)

  ----------------------------------------------------------------------
  -- Build the fuel (sigma-pile) and the run chain.

  fuelA : Term
  fuelA = ap1 s O
  fuelAB : Term
  fuelAB = ap2 sigma fuelA seg2_mu_fuel
  fuelABC : Term
  fuelABC = ap2 sigma fuelAB (ap1 s O)
  fuelD : Term
  fuelD = ap2 sigma fuelABC (ap1 s O)
  fuelE : Term
  fuelE = ap2 sigma fuelD (ap1 s O)
  fuelM : Term
  fuelM = ap2 sigma fuelE fGouter
  fuelN : Term
  fuelN = ap2 sigma fuelM (ap1 s O)

  run1 : Deriv (eqF (ap2 (iter step) c0 fuelA) c1)
  run1 = iter_step1 c0 c1 seg1_evC

  run12 : Deriv (eqF (ap2 (iter step) c0 fuelAB) c2)
  run12 = compStep c0 c1 c2 fuelA seg2_mu_fuel run1 seg2_mu

  run123 : Deriv (eqF (ap2 (iter step) c0 fuelABC) c3)
  run123 = compStep c0 c2 c3 fuelAB (ap1 s O) run12
             (iter_step1 c2 c3 seg3_rtC1)

  run4 : Deriv (eqF (ap2 (iter step) c0 fuelD) c4)
  run4 = compStep c0 c3 c4 fuelABC (ap1 s O) run123
           (iter_step1 c3 c4 seg4_evU)

  run5 : Deriv (eqF (ap2 (iter step) c0 fuelE) c5)
  run5 = compStep c0 c4 c5 fuelD (ap1 s O) run4
           (iter_step1 c4 c5 seg5_rtApp2)

  run6 : Deriv (eqF (ap2 (iter step) c0 fuelM) c6)
  run6 = compStep c0 c5 c6 fuelE fGouter run5 seg6_runs2

  run6' : Deriv (eqF (ap2 (iter step) c0 fuelM) c6')
  run6' = ruleTrans run6 seg7_bridge

  run7 : Deriv (eqF (ap2 (iter step) c0 fuelN) cH)
  run7 = compStep c0 c6' cH fuelM (ap1 s O) run6'
           (iter_step1 c6' cH seg8_rtEmpty)

  ----------------------------------------------------------------------
  -- Wrap with readout, initF, and parse round-trip.

  readout_chain :
    Deriv (eqF (ap1 readout (ap2 (iter step) c0 fuelN))
                (ap1 s (ap1 outL k_max)))
  readout_chain =
    ruleTrans (cong1 readout run7) (readout_halt (ap1 outL k_max))

  initF_bridge : Deriv (eqF (ap1 initF gLcodeDefAlph) c0)
  initF_bridge = initF_eq gLcodeDefAlph

  evalU_at_gL :
    Deriv (eqF (ap2 evalU gLcodeDefAlph fuelN) (ap1 s (ap1 outL k_max)))
  evalU_at_gL =
    let unfold = evalU_unfold gLcodeDefAlph fuelN
        iterRw = congL (iter step) fuelN initF_bridge
        readRw = cong1 readout iterRw
    in ruleTrans unfold (ruleTrans readRw readout_chain)

  evalU_at_parse :
    Deriv (eqF (ap2 evalU (ap1 parse (enc gLcodeDefAlph)) fuelN)
                (ap1 s (ap1 outL k_max)))
  evalU_at_parse =
    let parseEq = dRT_gLDefAlph
        evalRw = congL evalU fuelN parseEq
    in ruleTrans evalRw evalU_at_gL

  ----------------------------------------------------------------------
  -- EXPORTS.

  nTerm : Term
  nTerm = fuelN

  dEval_witness :
    Deriv (eqF (ap2 evalU (ap1 parse (enc gLcodeDefAlph)) nTerm)
                (ap1 s (ap1 outKdefAlph k_max)))
  dEval_witness = evalU_at_parse
