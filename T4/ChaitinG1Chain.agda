{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.ChaitinG1Chain -- the C-wrapper unwinding of the gLcode Lstar run.
--
-- Compose the discharged  runs_mu  with the 7 enclosing steps:
--   * stepU_at_evC  (the outer C-head enters the mu code).
--   * runs_mu       (the mu loop runs to k_max).
--   * stepU_at_rtC1 (frmC1 pops, evaluate h2 = u).
--   * stepU_at_evU  (u(O) = O).
--   * stepU_at_rtApp2 (frmApp2 pops, evaluate g = Lift1 (out_L Lstar) at pi k_max O).
--   * correct2.runs2 (Lift1 (out_L Lstar)) k_max O konEmpty  -- yields outL k_max.
--   * stepU_at_rtEmpty (konEmpty pops, halt).
--
-- and bridges to  evalU (parse (enc (gLcode Lstar))) nTerm  via initF_eq,
-- evalU_unfold, and dRT_gL.

module T4.ChaitinG1Chain where

open import T4.Base
open import T4.IsNat           using ( isNat )
open import T4.KFormula        using ( Kgt )
open import T4.KOut            using ( out_L )
open import T4.KDiag           using ( gLcode ; gCodeOf ; dRT_gL )
open import T4.KGodel1Bridge   using ( Lstar )
open import T4.Encode          using ( encode )
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

import T4.ChaitinG1Discharge

open import BRA3.Church          using ( pi ; sigma )
open import BRA3.Fan             using ( Lift1 ; Lift1_eq )
open import BRA3.Dispatch        using ( Closed ; closed_O ; closed_ap1
                                        ; closed_ap2 )
open import BRA3.RuleInst2       using ( simSubstT )
open import BRA3.CourseOfValues  using ( iter )
open import BRA3.RecBRA3AtPairUniv using ( iter_base_univ ; iter_step_univ )

------------------------------------------------------------------------
-- The Chain module -- parametric in the same setup as Discharge.

module Chain
  (x        : Term)
  (nx       : isNat x)
  (d        : Deriv (Kgt Lstar x))
  (cl_encD  : Closed (encode d))
  (sim_encD : (a b : Term) ->
              Eq (simSubstT zero a (suc zero) b (encode d)) (encode d))
  where

  open T4.ChaitinG1Discharge.Discharge x nx d cl_encD sim_encD
    using ( k_max ; cl_kmax ; fuelMu_fun ; runs_mu )

  ----------------------------------------------------------------------
  -- Configurations.

  outL : Fun1
  outL = out_L Lstar

  g_outer_code : Term
  g_outer_code = gCodeOf Lstar      -- = mcode2 (Lift1 outL)

  h1c : Term
  h1c = mcodeMu (mcode1 (T4.ChaitinG1Discharge.Discharge.gFun
                          x nx d cl_encD sim_encD))

  K1 : Term
  K1 = kons (frmC1 g_outer_code (mcode1 u) O) konEmpty

  K2 : Term
  K2 = kons (frmApp2 g_outer_code k_max) konEmpty

  c0 c1 c2 c3 c4 c5 c6 c6' cH : Term
  c0  = cfgEV (gLcode Lstar) O konEmpty
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

  initF_bridge : Deriv (eqF (ap1 initF (gLcode Lstar)) c0)
  initF_bridge = initF_eq (gLcode Lstar)

  evalU_at_gL :
    Deriv (eqF (ap2 evalU (gLcode Lstar) fuelN) (ap1 s (ap1 outL k_max)))
  evalU_at_gL =
    let unfold = evalU_unfold (gLcode Lstar) fuelN
        iterRw = congL (iter step) fuelN initF_bridge
        readRw = cong1 readout iterRw
    in ruleTrans unfold (ruleTrans readRw readout_chain)

  evalU_at_parse :
    Deriv (eqF (ap2 evalU (ap1 parse (enc (gLcode Lstar))) fuelN)
                (ap1 s (ap1 outL k_max)))
  evalU_at_parse =
    let parseEq = dRT_gL Lstar
        evalRw = congL evalU fuelN parseEq
    in ruleTrans evalRw evalU_at_gL

  ----------------------------------------------------------------------
  -- Closedness of fuelN  (built from closed pieces).

  cl_sO : Closed (ap1 s O)
  cl_sO = closed_ap1 s O closed_O

  cl_seg2_mu_fuel : Closed seg2_mu_fuel
  cl_seg2_mu_fuel =
    closed_ap2 sigma (ap1 s O) (ap2 fuelMu_fun k_max k_max)
      cl_sO
      (closed_ap2 fuelMu_fun k_max k_max cl_kmax cl_kmax)

  cl_fGouter : Closed fGouter
  cl_fGouter = closed_ap2 (fuelG bG) k_max O cl_kmax closed_O

  cl_fuelA   : Closed fuelA
  cl_fuelA   = cl_sO
  cl_fuelAB  : Closed fuelAB
  cl_fuelAB  = closed_ap2 sigma fuelA seg2_mu_fuel cl_fuelA cl_seg2_mu_fuel
  cl_fuelABC : Closed fuelABC
  cl_fuelABC = closed_ap2 sigma fuelAB (ap1 s O) cl_fuelAB cl_sO
  cl_fuelD   : Closed fuelD
  cl_fuelD   = closed_ap2 sigma fuelABC (ap1 s O) cl_fuelABC cl_sO
  cl_fuelE   : Closed fuelE
  cl_fuelE   = closed_ap2 sigma fuelD (ap1 s O) cl_fuelD cl_sO
  cl_fuelM   : Closed fuelM
  cl_fuelM   = closed_ap2 sigma fuelE fGouter cl_fuelE cl_fGouter
  cl_fuelN   : Closed fuelN
  cl_fuelN   = closed_ap2 sigma fuelM (ap1 s O) cl_fuelM cl_sO

  ----------------------------------------------------------------------
  -- EXPORTS.

  nTerm : Term
  nTerm = fuelN

  clN : Closed nTerm
  clN = cl_fuelN

  dEval_witness :
    Deriv (eqF (ap2 evalU (ap1 parse (enc (gLcode Lstar))) nTerm)
                (ap1 s (ap1 (out_L Lstar) k_max)))
  dEval_witness = evalU_at_parse
