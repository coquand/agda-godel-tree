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
  ( ze# ; su# ; ad# ; hd_ze ; hd_su ; hd_ad ; ar_su ; ad1 ; ad2 )

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
