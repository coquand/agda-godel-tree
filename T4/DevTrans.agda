{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.DevTrans -- STAGE I3 of attempt3 §11, layer 2b: the per-transition
-- reduction lemmas of the complete-development CK machine, the EV rows of the
-- transition table in T4.DevMachine's header.  Each lemma fires the mode test
-- (isEV), the head-tag cascade (testHd 0/1) and -- in the ad case -- the
-- first-child cascade (testFirstHd 0/1), then applies the matching EV
-- branch-value lemma (T4.DevStep) and cleans the result with the TrsCodeObj
-- projection equations (ar_su / ad1 / ad2) into constructor-specific form:
--
--   devStepU_ze   :  cfgEV ze#         K  ->  cfgRT ze# K
--   devStepU_su   :  cfgEV (su# t1)    K  ->  cfgEV t1 (kons frmSu K)
--   devStepU_adZe :  cfgEV (ad# ze# y) K  ->  cfgEV y  K
--   devStepU_adSu :  cfgEV (ad# (su# x) y)    K  ->  cfgEV x (kons (frmAdSu1 y) K)
--   devStepU_adAd :  cfgEV (ad# (ad# p q) y)  K  ->  cfgEV (ad# p q) (kons (frmAd1 y) K)
--
-- These are the descent transitions; the RT (return) transitions and the
-- run-to-HALT assembly  devF  + the five  dev  closure equations build on top.
-- Pure object reasoning (fireT / fireF + the DevStep fire/skip helpers); no
-- induction, no postulates, no holes.

module T4.DevTrans where

open import T4.Base
open import T4.DevMachine
open import T4.DevStep
open import T4.TrsCodeObj using
  ( ze# ; su# ; ad# ; tagSu ; tagAd
  ; hd_ze ; hd_su ; hd_ad ; ar_su ; ad1 ; ad2 )

open import T4.EvalUStep        using ( fork ; fireT ; fireF )
open import BRA3.SubT.V2NatNeq  using ( decideNatNeq )

------------------------------------------------------------------------
-- ze :  cfgEV ze# K  ->  cfgRT ze# K .

devStepU_ze : (K : Term) ->
  Deriv (eqF (ap1 devStepU (cfgEV ze# K)) (cfgRT ze# K))
devStepU_ze K =
  let c : Term
      c = cfgEV ze# K
      e0 : Deriv (eqF (ap1 devStepU c) (ap1 evBranch c))
      e0 = fireT evBranch modeRT isEV c (isEV_cfgEV ze# K)
      e1 : Deriv (eqF (ap1 evBranch c) (ap1 evZe c))
      e1 = fireT evZe (fork evSu evAd (testHd 1)) (testHd 0) c
             (hdFire 0 ze# K hd_ze)
  in ruleTrans e0 (ruleTrans e1 (evZe_value ze# K))

------------------------------------------------------------------------
-- su :  cfgEV (su# t1) K  ->  cfgEV t1 (kons frmSu K) .

devStepU_su : (t1 K : Term) ->
  Deriv (eqF (ap1 devStepU (cfgEV (su# t1) K)) (cfgEV t1 (kons frmSu K)))
devStepU_su t1 K =
  let c : Term
      c = cfgEV (su# t1) K
      e0 : Deriv (eqF (ap1 devStepU c) (ap1 evBranch c))
      e0 = fireT evBranch modeRT isEV c (isEV_cfgEV (su# t1) K)
      e1 : Deriv (eqF (ap1 evBranch c) (ap1 (fork evSu evAd (testHd 1)) c))
      e1 = fireF evZe (fork evSu evAd (testHd 1)) (testHd 0) c
             (hdSkip 0 1 (su# t1) K (hd_su t1) (decideNatNeq 1 0 (\ ())))
      e2 : Deriv (eqF (ap1 (fork evSu evAd (testHd 1)) c) (ap1 evSu c))
      e2 = fireT evSu evAd (testHd 1) c (hdFire 1 (su# t1) K (hd_su t1))
      e3 : Deriv (eqF (ap1 evSu c) (cfgEV (ap1 Snd (su# t1)) (kons frmSu K)))
      e3 = evSu_value (su# t1) K
      e4 : Deriv (eqF (cfgEV (ap1 Snd (su# t1)) (kons frmSu K))
                      (cfgEV t1 (kons frmSu K)))
      e4 = congR Pair (natCode mEV) (congL Pair (kons frmSu K) (ar_su t1))
  in ruleTrans e0 (ruleTrans e1 (ruleTrans e2 (ruleTrans e3 e4)))

------------------------------------------------------------------------
-- ad / first = ze :  cfgEV (ad# ze# y) K  ->  cfgEV y K .

devStepU_adZe : (y K : Term) ->
  Deriv (eqF (ap1 devStepU (cfgEV (ad# ze# y) K)) (cfgEV y K))
devStepU_adZe y K =
  let t : Term
      t = ad# ze# y
      c : Term
      c = cfgEV t K
      e0 : Deriv (eqF (ap1 devStepU c) (ap1 evBranch c))
      e0 = fireT evBranch modeRT isEV c (isEV_cfgEV t K)
      e1 : Deriv (eqF (ap1 evBranch c) (ap1 (fork evSu evAd (testHd 1)) c))
      e1 = fireF evZe (fork evSu evAd (testHd 1)) (testHd 0) c
             (hdSkip 0 2 t K (hd_ad ze# y) (decideNatNeq 2 0 (\ ())))
      e2 : Deriv (eqF (ap1 (fork evSu evAd (testHd 1)) c) (ap1 evAd c))
      e2 = fireF evSu evAd (testHd 1) c
             (hdSkip 1 2 t K (hd_ad ze# y) (decideNatNeq 2 1 (\ ())))
      e3 : Deriv (eqF (ap1 evAd c) (ap1 evAdZe c))
      e3 = fireT evAdZe (fork evAdSu evAdAd (testFirstHd 1)) (testFirstHd 0) c
             (fhFire 0 t K (ruleTrans (cong1 Fst (ad1 ze# y)) hd_ze))
      e4 : Deriv (eqF (ap1 evAdZe c) (cfgEV (ap1 Snd (ap1 Snd t)) K))
      e4 = evAdZe_value t K
      e5 : Deriv (eqF (cfgEV (ap1 Snd (ap1 Snd t)) K) (cfgEV y K))
      e5 = congR Pair (natCode mEV) (congL Pair K (ad2 ze# y))
  in ruleTrans e0 (ruleTrans e1 (ruleTrans e2 (ruleTrans e3 (ruleTrans e4 e5))))

------------------------------------------------------------------------
-- ad / first = su :  cfgEV (ad# (su# x) y) K
--                  ->  cfgEV x (kons (frmAdSu1 y) K) .

devStepU_adSu : (x y K : Term) ->
  Deriv (eqF (ap1 devStepU (cfgEV (ad# (su# x) y) K))
             (cfgEV x (kons (frmAdSu1 y) K)))
devStepU_adSu x y K =
  let t : Term
      t = ad# (su# x) y
      c : Term
      c = cfgEV t K
      hf : Deriv (eqF (ap1 Fst (ap1 Fst (ap1 Snd t))) (natCode 1))
      hf = ruleTrans (cong1 Fst (ad1 (su# x) y)) (hd_su x)
      e0 : Deriv (eqF (ap1 devStepU c) (ap1 evBranch c))
      e0 = fireT evBranch modeRT isEV c (isEV_cfgEV t K)
      e1 : Deriv (eqF (ap1 evBranch c) (ap1 (fork evSu evAd (testHd 1)) c))
      e1 = fireF evZe (fork evSu evAd (testHd 1)) (testHd 0) c
             (hdSkip 0 2 t K (hd_ad (su# x) y) (decideNatNeq 2 0 (\ ())))
      e2 : Deriv (eqF (ap1 (fork evSu evAd (testHd 1)) c) (ap1 evAd c))
      e2 = fireF evSu evAd (testHd 1) c
             (hdSkip 1 2 t K (hd_ad (su# x) y) (decideNatNeq 2 1 (\ ())))
      e3 : Deriv (eqF (ap1 evAd c) (ap1 (fork evAdSu evAdAd (testFirstHd 1)) c))
      e3 = fireF evAdZe (fork evAdSu evAdAd (testFirstHd 1)) (testFirstHd 0) c
             (fhSkip 0 1 t K hf (decideNatNeq 1 0 (\ ())))
      e4 : Deriv (eqF (ap1 (fork evAdSu evAdAd (testFirstHd 1)) c) (ap1 evAdSu c))
      e4 = fireT evAdSu evAdAd (testFirstHd 1) c (fhFire 1 t K hf)
      e5 : Deriv (eqF (ap1 evAdSu c)
                      (cfgEV (ap1 Snd (ap1 Fst (ap1 Snd t)))
                             (kons (frmAdSu1 (ap1 Snd (ap1 Snd t))) K)))
      e5 = evAdSu_value t K
      eVal : Deriv (eqF (ap1 Snd (ap1 Fst (ap1 Snd t))) x)
      eVal = ruleTrans (cong1 Snd (ad1 (su# x) y)) (ar_su x)
      eFrm : Deriv (eqF (ap1 Snd (ap1 Snd t)) y)
      eFrm = ad2 (su# x) y
      e6 : Deriv (eqF (cfgEV (ap1 Snd (ap1 Fst (ap1 Snd t)))
                             (kons (frmAdSu1 (ap1 Snd (ap1 Snd t))) K))
                      (cfgEV x (kons (frmAdSu1 y) K)))
      e6 = congR Pair (natCode mEV)
             (ruleTrans (congL Pair (kons (frmAdSu1 (ap1 Snd (ap1 Snd t))) K) eVal)
                        (congR Pair x
                           (congR Pair (ap1 s O)
                              (congL Pair K (congR Pair (natCode fAdSu1) eFrm)))))
  in ruleTrans e0 (ruleTrans e1 (ruleTrans e2
       (ruleTrans e3 (ruleTrans e4 (ruleTrans e5 e6)))))

------------------------------------------------------------------------
-- ad / first = ad :  cfgEV (ad# (ad# p q) y) K
--                  ->  cfgEV (ad# p q) (kons (frmAd1 y) K) .

devStepU_adAd : (p q y K : Term) ->
  Deriv (eqF (ap1 devStepU (cfgEV (ad# (ad# p q) y) K))
             (cfgEV (ad# p q) (kons (frmAd1 y) K)))
devStepU_adAd p q y K =
  let a : Term
      a = ad# p q
      t : Term
      t = ad# a y
      c : Term
      c = cfgEV t K
      hf : Deriv (eqF (ap1 Fst (ap1 Fst (ap1 Snd t))) (natCode 2))
      hf = ruleTrans (cong1 Fst (ad1 a y)) (hd_ad p q)
      e0 : Deriv (eqF (ap1 devStepU c) (ap1 evBranch c))
      e0 = fireT evBranch modeRT isEV c (isEV_cfgEV t K)
      e1 : Deriv (eqF (ap1 evBranch c) (ap1 (fork evSu evAd (testHd 1)) c))
      e1 = fireF evZe (fork evSu evAd (testHd 1)) (testHd 0) c
             (hdSkip 0 2 t K (hd_ad a y) (decideNatNeq 2 0 (\ ())))
      e2 : Deriv (eqF (ap1 (fork evSu evAd (testHd 1)) c) (ap1 evAd c))
      e2 = fireF evSu evAd (testHd 1) c
             (hdSkip 1 2 t K (hd_ad a y) (decideNatNeq 2 1 (\ ())))
      e3 : Deriv (eqF (ap1 evAd c) (ap1 (fork evAdSu evAdAd (testFirstHd 1)) c))
      e3 = fireF evAdZe (fork evAdSu evAdAd (testFirstHd 1)) (testFirstHd 0) c
             (fhSkip 0 2 t K hf (decideNatNeq 2 0 (\ ())))
      e4 : Deriv (eqF (ap1 (fork evAdSu evAdAd (testFirstHd 1)) c) (ap1 evAdAd c))
      e4 = fireF evAdSu evAdAd (testFirstHd 1) c
             (fhSkip 1 2 t K hf (decideNatNeq 2 1 (\ ())))
      e5 : Deriv (eqF (ap1 evAdAd c)
                      (cfgEV (ap1 Fst (ap1 Snd t))
                             (kons (frmAd1 (ap1 Snd (ap1 Snd t))) K)))
      e5 = evAdAd_value t K
      eVal : Deriv (eqF (ap1 Fst (ap1 Snd t)) a)
      eVal = ad1 a y
      eFrm : Deriv (eqF (ap1 Snd (ap1 Snd t)) y)
      eFrm = ad2 a y
      e6 : Deriv (eqF (cfgEV (ap1 Fst (ap1 Snd t))
                             (kons (frmAd1 (ap1 Snd (ap1 Snd t))) K))
                      (cfgEV a (kons (frmAd1 y) K)))
      e6 = congR Pair (natCode mEV)
             (ruleTrans (congL Pair (kons (frmAd1 (ap1 Snd (ap1 Snd t))) K) eVal)
                        (congR Pair a
                           (congR Pair (ap1 s O)
                              (congL Pair K (congR Pair (natCode fAd1) eFrm)))))
  in ruleTrans e0 (ruleTrans e1 (ruleTrans e2
       (ruleTrans e3 (ruleTrans e4 (ruleTrans e5 e6)))))

------------------------------------------------------------------------
-- RT (return) transitions.  config = cfgRT val K.
--
-- Common projection helpers for a cons kont  K = kons frame rest :
--   frameProj :  Fst (Snd K)        = frame
--   restProj  :  Snd (Snd K)        = rest
-- and the RT cascade sub-forks (matching  rtCons  in T4.DevStep):
--   rtCons = fork rtFrmSu rtC2 (testFtag fSu)
--   rtC2   = fork rtFrmAdSu1 rtC3 (testFtag fAdSu1)
--   rtC3   = fork rtFrmAdSu2 rtC4 (testFtag fAdSu2)
--   rtC4   = fork rtFrmAd1 rtFrmAd2 (testFtag fAd1)

frameProj : (frame rest : Term) ->
  Deriv (eqF (ap1 Fst (ap1 Snd (kons frame rest))) frame)
frameProj frame rest = ruleTrans (cong1 Fst (konsBody frame rest)) (konsHd frame rest)

restProj : (frame rest : Term) ->
  Deriv (eqF (ap1 Snd (ap1 Snd (kons frame rest))) rest)
restProj frame rest = ruleTrans (cong1 Snd (konsBody frame rest)) (konsTl frame rest)

rtC4 : Fun1
rtC4 = fork rtFrmAd1 rtFrmAd2 (testFtag fAd1)

rtC3 : Fun1
rtC3 = fork rtFrmAdSu2 rtC4 (testFtag fAdSu2)

rtC2 : Fun1
rtC2 = fork rtFrmAdSu1 rtC3 (testFtag fAdSu1)

------------------------------------------------------------------------
-- HALT :  cfgRT val konEmpty  ->  cfgHALT val .

devStepU_halt : (val : Term) ->
  Deriv (eqF (ap1 devStepU (cfgRT val konEmpty)) (cfgHALT val))
devStepU_halt val =
  let c : Term
      c = cfgRT val konEmpty
      e0 : Deriv (eqF (ap1 devStepU c) (ap1 modeRT c))
      e0 = fireF evBranch modeRT isEV c (isEV_cfgRT val konEmpty)
      e1 : Deriv (eqF (ap1 modeRT c) (ap1 rtBranch c))
      e1 = fireT rtBranch u isRT c (isRT_cfgRT val konEmpty)
      e2 : Deriv (eqF (ap1 rtBranch c) (ap1 rtEmpty c))
      e2 = fireF rtCons rtEmpty rHasFrame c
             (ruleTrans (rHasFrame_rt val konEmpty) konsFlag_empty)
  in ruleTrans e0 (ruleTrans e1 (ruleTrans e2 (rtEmpty_value val konEmpty)))

------------------------------------------------------------------------
-- frmSu :  cfgRT val (kons frmSu rest)  ->  cfgRT (su# val) rest .

devStepU_frmSu : (val rest : Term) ->
  Deriv (eqF (ap1 devStepU (cfgRT val (kons frmSu rest))) (cfgRT (su# val) rest))
devStepU_frmSu val rest =
  let K : Term
      K = kons frmSu rest
      c : Term
      c = cfgRT val K
      e0 : Deriv (eqF (ap1 devStepU c) (ap1 modeRT c))
      e0 = fireF evBranch modeRT isEV c (isEV_cfgRT val K)
      e1 : Deriv (eqF (ap1 modeRT c) (ap1 rtBranch c))
      e1 = fireT rtBranch u isRT c (isRT_cfgRT val K)
      e2 : Deriv (eqF (ap1 rtBranch c) (ap1 rtCons c))
      e2 = fireT rtCons rtEmpty rHasFrame c
             (ruleTrans (rHasFrame_rt val K) (konsFlag_cons frmSu rest))
      e3 : Deriv (eqF (ap1 rtCons c) (ap1 rtFrmSu c))
      e3 = fireT rtFrmSu rtC2 (testFtag fSu) c
             (ftFire fSu val K (ruleTrans (cong1 Fst (frameProj frmSu rest)) frmSu_tag))
      e4 : Deriv (eqF (ap1 rtFrmSu c) (cfgRT (su# (ap1 rVal c)) (ap1 rRest c)))
      e4 = rtFrmSu_value val K
      eRest : Deriv (eqF (ap1 rRest c) rest)
      eRest = ruleTrans (rRest_rt val K) (restProj frmSu rest)
      e5 : Deriv (eqF (cfgRT (su# (ap1 rVal c)) (ap1 rRest c)) (cfgRT (su# val) rest))
      e5 = congR Pair (natCode mRT)
             (ruleTrans (congL Pair (ap1 rRest c) (congR Pair tagSu (rVal_rt val K)))
                        (congR Pair (su# val) eRest))
  in ruleTrans e0 (ruleTrans e1 (ruleTrans e2 (ruleTrans e3 (ruleTrans e4 e5))))

------------------------------------------------------------------------
-- frmAdSu1 :  cfgRT val (kons (frmAdSu1 y) rest)
--          ->  cfgEV y (kons (frmAdSu2 val) rest) .

devStepU_frmAdSu1 : (val y rest : Term) ->
  Deriv (eqF (ap1 devStepU (cfgRT val (kons (frmAdSu1 y) rest)))
             (cfgEV y (kons (frmAdSu2 val) rest)))
devStepU_frmAdSu1 val y rest =
  let K : Term
      K = kons (frmAdSu1 y) rest
      c : Term
      c = cfgRT val K
      ftEq : Deriv (eqF (ap1 Fst (ap1 Fst (ap1 Snd K))) (natCode fAdSu1))
      ftEq = ruleTrans (cong1 Fst (frameProj (frmAdSu1 y) rest)) (frmAdSu1_tag y)
      e0 : Deriv (eqF (ap1 devStepU c) (ap1 modeRT c))
      e0 = fireF evBranch modeRT isEV c (isEV_cfgRT val K)
      e1 : Deriv (eqF (ap1 modeRT c) (ap1 rtBranch c))
      e1 = fireT rtBranch u isRT c (isRT_cfgRT val K)
      e2 : Deriv (eqF (ap1 rtBranch c) (ap1 rtCons c))
      e2 = fireT rtCons rtEmpty rHasFrame c
             (ruleTrans (rHasFrame_rt val K) (konsFlag_cons (frmAdSu1 y) rest))
      e3 : Deriv (eqF (ap1 rtCons c) (ap1 rtC2 c))
      e3 = fireF rtFrmSu rtC2 (testFtag fSu) c
             (ftSkip fSu fAdSu1 val K ftEq (decideNatNeq fAdSu1 fSu (\ ())))
      e4 : Deriv (eqF (ap1 rtC2 c) (ap1 rtFrmAdSu1 c))
      e4 = fireT rtFrmAdSu1 rtC3 (testFtag fAdSu1) c (ftFire fAdSu1 val K ftEq)
      e5 : Deriv (eqF (ap1 rtFrmAdSu1 c)
                      (cfgEV (ap1 rFdata c)
                             (kons (frmAdSu2 (ap1 rVal c)) (ap1 rRest c))))
      e5 = rtFrmAdSu1_value val K
      eFdata : Deriv (eqF (ap1 rFdata c) y)
      eFdata = ruleTrans (rFdata_rt val K)
                 (ruleTrans (cong1 Snd (frameProj (frmAdSu1 y) rest)) (frmAdSu1_body y))
      eRest : Deriv (eqF (ap1 rRest c) rest)
      eRest = ruleTrans (rRest_rt val K) (restProj (frmAdSu1 y) rest)
      e6 : Deriv (eqF (cfgEV (ap1 rFdata c)
                             (kons (frmAdSu2 (ap1 rVal c)) (ap1 rRest c)))
                      (cfgEV y (kons (frmAdSu2 val) rest)))
      e6 = congR Pair (natCode mEV)
             (ruleTrans (congL Pair (kons (frmAdSu2 (ap1 rVal c)) (ap1 rRest c)) eFdata)
                        (congR Pair y
                           (congR Pair (ap1 s O)
                              (ruleTrans
                                (congL Pair (ap1 rRest c)
                                   (congR Pair (natCode fAdSu2) (rVal_rt val K)))
                                (congR Pair (frmAdSu2 val) eRest)))))
  in ruleTrans e0 (ruleTrans e1 (ruleTrans e2
       (ruleTrans e3 (ruleTrans e4 (ruleTrans e5 e6)))))

------------------------------------------------------------------------
-- frmAdSu2 :  cfgRT val (kons (frmAdSu2 v1) rest)
--          ->  cfgRT (su# (ad# v1 val)) rest .

devStepU_frmAdSu2 : (val v1 rest : Term) ->
  Deriv (eqF (ap1 devStepU (cfgRT val (kons (frmAdSu2 v1) rest)))
             (cfgRT (su# (ad# v1 val)) rest))
devStepU_frmAdSu2 val v1 rest =
  let K : Term
      K = kons (frmAdSu2 v1) rest
      c : Term
      c = cfgRT val K
      ftEq : Deriv (eqF (ap1 Fst (ap1 Fst (ap1 Snd K))) (natCode fAdSu2))
      ftEq = ruleTrans (cong1 Fst (frameProj (frmAdSu2 v1) rest)) (frmAdSu2_tag v1)
      e0 : Deriv (eqF (ap1 devStepU c) (ap1 modeRT c))
      e0 = fireF evBranch modeRT isEV c (isEV_cfgRT val K)
      e1 : Deriv (eqF (ap1 modeRT c) (ap1 rtBranch c))
      e1 = fireT rtBranch u isRT c (isRT_cfgRT val K)
      e2 : Deriv (eqF (ap1 rtBranch c) (ap1 rtCons c))
      e2 = fireT rtCons rtEmpty rHasFrame c
             (ruleTrans (rHasFrame_rt val K) (konsFlag_cons (frmAdSu2 v1) rest))
      e3 : Deriv (eqF (ap1 rtCons c) (ap1 rtC2 c))
      e3 = fireF rtFrmSu rtC2 (testFtag fSu) c
             (ftSkip fSu fAdSu2 val K ftEq (decideNatNeq fAdSu2 fSu (\ ())))
      e4 : Deriv (eqF (ap1 rtC2 c) (ap1 rtC3 c))
      e4 = fireF rtFrmAdSu1 rtC3 (testFtag fAdSu1) c
             (ftSkip fAdSu1 fAdSu2 val K ftEq (decideNatNeq fAdSu2 fAdSu1 (\ ())))
      e5 : Deriv (eqF (ap1 rtC3 c) (ap1 rtFrmAdSu2 c))
      e5 = fireT rtFrmAdSu2 rtC4 (testFtag fAdSu2) c (ftFire fAdSu2 val K ftEq)
      e6 : Deriv (eqF (ap1 rtFrmAdSu2 c)
                      (cfgRT (su# (ad# (ap1 rFdata c) (ap1 rVal c))) (ap1 rRest c)))
      e6 = rtFrmAdSu2_value val K
      eFdata : Deriv (eqF (ap1 rFdata c) v1)
      eFdata = ruleTrans (rFdata_rt val K)
                 (ruleTrans (cong1 Snd (frameProj (frmAdSu2 v1) rest)) (frmAdSu2_body v1))
      eRest : Deriv (eqF (ap1 rRest c) rest)
      eRest = ruleTrans (rRest_rt val K) (restProj (frmAdSu2 v1) rest)
      eV : Deriv (eqF (su# (ad# (ap1 rFdata c) (ap1 rVal c))) (su# (ad# v1 val)))
      eV = congR Pair tagSu
             (congR Pair tagAd
                (ruleTrans (congL Pair (ap1 rVal c) eFdata) (congR Pair v1 (rVal_rt val K))))
      e7 : Deriv (eqF (cfgRT (su# (ad# (ap1 rFdata c) (ap1 rVal c))) (ap1 rRest c))
                      (cfgRT (su# (ad# v1 val)) rest))
      e7 = congR Pair (natCode mRT)
             (ruleTrans (congL Pair (ap1 rRest c) eV)
                        (congR Pair (su# (ad# v1 val)) eRest))
  in ruleTrans e0 (ruleTrans e1 (ruleTrans e2
       (ruleTrans e3 (ruleTrans e4 (ruleTrans e5 (ruleTrans e6 e7))))))

------------------------------------------------------------------------
-- frmAd1 :  cfgRT val (kons (frmAd1 y) rest)
--        ->  cfgEV y (kons (frmAd2 val) rest) .

devStepU_frmAd1 : (val y rest : Term) ->
  Deriv (eqF (ap1 devStepU (cfgRT val (kons (frmAd1 y) rest)))
             (cfgEV y (kons (frmAd2 val) rest)))
devStepU_frmAd1 val y rest =
  let K : Term
      K = kons (frmAd1 y) rest
      c : Term
      c = cfgRT val K
      ftEq : Deriv (eqF (ap1 Fst (ap1 Fst (ap1 Snd K))) (natCode fAd1))
      ftEq = ruleTrans (cong1 Fst (frameProj (frmAd1 y) rest)) (frmAd1_tag y)
      e0 : Deriv (eqF (ap1 devStepU c) (ap1 modeRT c))
      e0 = fireF evBranch modeRT isEV c (isEV_cfgRT val K)
      e1 : Deriv (eqF (ap1 modeRT c) (ap1 rtBranch c))
      e1 = fireT rtBranch u isRT c (isRT_cfgRT val K)
      e2 : Deriv (eqF (ap1 rtBranch c) (ap1 rtCons c))
      e2 = fireT rtCons rtEmpty rHasFrame c
             (ruleTrans (rHasFrame_rt val K) (konsFlag_cons (frmAd1 y) rest))
      e3 : Deriv (eqF (ap1 rtCons c) (ap1 rtC2 c))
      e3 = fireF rtFrmSu rtC2 (testFtag fSu) c
             (ftSkip fSu fAd1 val K ftEq (decideNatNeq fAd1 fSu (\ ())))
      e4 : Deriv (eqF (ap1 rtC2 c) (ap1 rtC3 c))
      e4 = fireF rtFrmAdSu1 rtC3 (testFtag fAdSu1) c
             (ftSkip fAdSu1 fAd1 val K ftEq (decideNatNeq fAd1 fAdSu1 (\ ())))
      e5 : Deriv (eqF (ap1 rtC3 c) (ap1 rtC4 c))
      e5 = fireF rtFrmAdSu2 rtC4 (testFtag fAdSu2) c
             (ftSkip fAdSu2 fAd1 val K ftEq (decideNatNeq fAd1 fAdSu2 (\ ())))
      e6 : Deriv (eqF (ap1 rtC4 c) (ap1 rtFrmAd1 c))
      e6 = fireT rtFrmAd1 rtFrmAd2 (testFtag fAd1) c (ftFire fAd1 val K ftEq)
      e7 : Deriv (eqF (ap1 rtFrmAd1 c)
                      (cfgEV (ap1 rFdata c)
                             (kons (frmAd2 (ap1 rVal c)) (ap1 rRest c))))
      e7 = rtFrmAd1_value val K
      eFdata : Deriv (eqF (ap1 rFdata c) y)
      eFdata = ruleTrans (rFdata_rt val K)
                 (ruleTrans (cong1 Snd (frameProj (frmAd1 y) rest)) (frmAd1_body y))
      eRest : Deriv (eqF (ap1 rRest c) rest)
      eRest = ruleTrans (rRest_rt val K) (restProj (frmAd1 y) rest)
      e8 : Deriv (eqF (cfgEV (ap1 rFdata c)
                             (kons (frmAd2 (ap1 rVal c)) (ap1 rRest c)))
                      (cfgEV y (kons (frmAd2 val) rest)))
      e8 = congR Pair (natCode mEV)
             (ruleTrans (congL Pair (kons (frmAd2 (ap1 rVal c)) (ap1 rRest c)) eFdata)
                        (congR Pair y
                           (congR Pair (ap1 s O)
                              (ruleTrans
                                (congL Pair (ap1 rRest c)
                                   (congR Pair (natCode fAd2) (rVal_rt val K)))
                                (congR Pair (frmAd2 val) eRest)))))
  in ruleTrans e0 (ruleTrans e1 (ruleTrans e2
       (ruleTrans e3 (ruleTrans e4 (ruleTrans e5 (ruleTrans e6 (ruleTrans e7 e8)))))))

------------------------------------------------------------------------
-- frmAd2 :  cfgRT val (kons (frmAd2 v1) rest)  ->  cfgRT (ad# v1 val) rest .

devStepU_frmAd2 : (val v1 rest : Term) ->
  Deriv (eqF (ap1 devStepU (cfgRT val (kons (frmAd2 v1) rest)))
             (cfgRT (ad# v1 val) rest))
devStepU_frmAd2 val v1 rest =
  let K : Term
      K = kons (frmAd2 v1) rest
      c : Term
      c = cfgRT val K
      ftEq : Deriv (eqF (ap1 Fst (ap1 Fst (ap1 Snd K))) (natCode fAd2))
      ftEq = ruleTrans (cong1 Fst (frameProj (frmAd2 v1) rest)) (frmAd2_tag v1)
      e0 : Deriv (eqF (ap1 devStepU c) (ap1 modeRT c))
      e0 = fireF evBranch modeRT isEV c (isEV_cfgRT val K)
      e1 : Deriv (eqF (ap1 modeRT c) (ap1 rtBranch c))
      e1 = fireT rtBranch u isRT c (isRT_cfgRT val K)
      e2 : Deriv (eqF (ap1 rtBranch c) (ap1 rtCons c))
      e2 = fireT rtCons rtEmpty rHasFrame c
             (ruleTrans (rHasFrame_rt val K) (konsFlag_cons (frmAd2 v1) rest))
      e3 : Deriv (eqF (ap1 rtCons c) (ap1 rtC2 c))
      e3 = fireF rtFrmSu rtC2 (testFtag fSu) c
             (ftSkip fSu fAd2 val K ftEq (decideNatNeq fAd2 fSu (\ ())))
      e4 : Deriv (eqF (ap1 rtC2 c) (ap1 rtC3 c))
      e4 = fireF rtFrmAdSu1 rtC3 (testFtag fAdSu1) c
             (ftSkip fAdSu1 fAd2 val K ftEq (decideNatNeq fAd2 fAdSu1 (\ ())))
      e5 : Deriv (eqF (ap1 rtC3 c) (ap1 rtC4 c))
      e5 = fireF rtFrmAdSu2 rtC4 (testFtag fAdSu2) c
             (ftSkip fAdSu2 fAd2 val K ftEq (decideNatNeq fAd2 fAdSu2 (\ ())))
      e6 : Deriv (eqF (ap1 rtC4 c) (ap1 rtFrmAd2 c))
      e6 = fireF rtFrmAd1 rtFrmAd2 (testFtag fAd1) c
             (ftSkip fAd1 fAd2 val K ftEq (decideNatNeq fAd2 fAd1 (\ ())))
      e7 : Deriv (eqF (ap1 rtFrmAd2 c)
                      (cfgRT (ad# (ap1 rFdata c) (ap1 rVal c)) (ap1 rRest c)))
      e7 = rtFrmAd2_value val K
      eFdata : Deriv (eqF (ap1 rFdata c) v1)
      eFdata = ruleTrans (rFdata_rt val K)
                 (ruleTrans (cong1 Snd (frameProj (frmAd2 v1) rest)) (frmAd2_body v1))
      eRest : Deriv (eqF (ap1 rRest c) rest)
      eRest = ruleTrans (rRest_rt val K) (restProj (frmAd2 v1) rest)
      eV : Deriv (eqF (ad# (ap1 rFdata c) (ap1 rVal c)) (ad# v1 val))
      eV = congR Pair tagAd
             (ruleTrans (congL Pair (ap1 rVal c) eFdata) (congR Pair v1 (rVal_rt val K)))
      e8 : Deriv (eqF (cfgRT (ad# (ap1 rFdata c) (ap1 rVal c)) (ap1 rRest c))
                      (cfgRT (ad# v1 val) rest))
      e8 = congR Pair (natCode mRT)
             (ruleTrans (congL Pair (ap1 rRest c) eV)
                        (congR Pair (ad# v1 val) eRest))
  in ruleTrans e0 (ruleTrans e1 (ruleTrans e2
       (ruleTrans e3 (ruleTrans e4 (ruleTrans e5 (ruleTrans e6 (ruleTrans e7 e8)))))))
