{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.EvalUEval -- the universal interpreter assembled (EVALU-DESIGN.md,
-- Phase E1, layer 3): the initialiser  initF , the read-off  readout , and
--   evalU = Post readout (Fan (Lift1 initF) v (iter stepU))  : Fun2 ,
-- with  ap2 evalU e n = readout( stepU^n (init e) ) .

module BRA4.EvalUEval where

open import BRA4.Base
open import BRA4.EvalU
open import BRA4.EvalUStep
  using ( stepU ; fork ; fireT )

open import BRA3.Church          using ( pi )
open import BRA3.ChurchT117      using ( Fst )
open import BRA3.ChurchT116      using ( Snd )
open import BRA3.PairAlgebra     using
  ( axFst ; axSnd ; compose1U ; compose1U_eq ; Post ; axPost )
open import BRA3.Fan             using ( Lift1 ; Lift1_eq )
open import BRA3.SubT.NatEq      using ( natEqF ; natEq_eq )
open import BRA3.Dispatch        using ( constN ; constN_eq )
open import BRA3.CourseOfValues  using ( iter )

------------------------------------------------------------------------
-- initF : Fun1 -- ap1 initF e = cfgEV e O konEmpty  (apply program e to O).

initF : Fun1
initF = C pi (constN tagEV) (C pi (C pi u o) (C pi o o))

initF_eq : (e : Term) -> Deriv (eqF (ap1 initF e) (cfgEV e O konEmpty))
initF_eq e =
  let eL : Deriv (eqF (ap1 (C pi u o) e) (ap2 pi e O))
      eL = ruleTrans (ax_C pi u o e)
             (ruleTrans (congL pi (ap1 o e) (ax_u e)) (congR pi e (ax_o e)))
      eR : Deriv (eqF (ap1 (C pi o o) e) (ap2 pi O O))
      eR = ruleTrans (ax_C pi o o e)
             (ruleTrans (congL pi (ap1 o e) (ax_o e)) (congR pi O (ax_o e)))
      eInner : Deriv (eqF (ap1 (C pi (C pi u o) (C pi o o)) e)
                          (ap2 pi (ap2 pi e O) (ap2 pi O O)))
      eInner = ruleTrans (ax_C pi (C pi u o) (C pi o o) e)
                 (ruleTrans (congL pi (ap1 (C pi o o) e) eL) (congR pi (ap2 pi e O) eR))
      e1 = ax_C pi (constN tagEV) (C pi (C pi u o) (C pi o o)) e
  in ruleTrans e1
       (ruleTrans (congL pi (ap1 (C pi (C pi u o) (C pi o o)) e) (constN_eq tagEV e))
                  (congR pi (natCode tagEV) eInner))

------------------------------------------------------------------------
-- readout : Fun1 -- mode = tagHALT ? s value : O .
--   readout = fork (compose1U s Snd) o isHalt .

isHalt : Fun1
isHalt = C natEqF Fst (constN tagHALT)

readout : Fun1
readout = fork (compose1U s Snd) o isHalt

isHalt_cfgHALT : (val : Term) -> Deriv (eqF (ap1 isHalt (cfgHALT val)) (ap1 s O))
isHalt_cfgHALT val =
  let c : Term
      c = cfgHALT val
      e1 = ax_C natEqF Fst (constN tagHALT) c
      e2 = congL natEqF (ap1 (constN tagHALT) c) (mode_cfgHALT val)
      e3 = congR natEqF (natCode tagHALT) (constN_eq tagHALT c)
  in ruleTrans e1 (ruleTrans e2 (ruleTrans e3 (natEq_eq tagHALT)))

readout_halt : (val : Term) -> Deriv (eqF (ap1 readout (cfgHALT val)) (ap1 s val))
readout_halt val =
  let c : Term
      c = cfgHALT val
      fire : Deriv (eqF (ap1 readout c) (ap1 (compose1U s Snd) c))
      fire = fireT (compose1U s Snd) o isHalt c (isHalt_cfgHALT val)
      val_eq : Deriv (eqF (ap1 (compose1U s Snd) c) (ap1 s val))
      val_eq = ruleTrans (compose1U_eq s Snd c) (cong1 s (body_cfgHALT val))
  in ruleTrans fire val_eq

------------------------------------------------------------------------
-- evalU : Fun2 .

evalU : Fun2
evalU = Post readout (Fan (Lift1 initF) v (iter stepU))

evalU_unfold : (e n : Term) ->
  Deriv (eqF (ap2 evalU e n) (ap1 readout (ap2 (iter stepU) (ap1 initF e) n)))
evalU_unfold e n =
  let G : Fun2
      G = Fan (Lift1 initF) v (iter stepU)
      e1 : Deriv (eqF (ap2 evalU e n) (ap1 readout (ap2 G e n)))
      e1 = axPost readout G e n
      e2 : Deriv (eqF (ap2 G e n)
                      (ap2 (iter stepU) (ap2 (Lift1 initF) e n) (ap2 v e n)))
      e2 = axFan (Lift1 initF) v (iter stepU) e n
      e5 : Deriv (eqF (ap2 (iter stepU) (ap2 (Lift1 initF) e n) (ap2 v e n))
                      (ap2 (iter stepU) (ap1 initF e) n))
      e5 = ruleTrans (congL (iter stepU) (ap2 v e n) (Lift1_eq initF e n))
                     (congR (iter stepU) (ap1 initF e) (ax_v e n))
  in ruleTrans e1 (cong1 readout (ruleTrans e2 e5))
