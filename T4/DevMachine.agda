{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.DevMachine -- STAGE I3 of attempt3 §11, layer 1: the CK-machine
-- coding layer for the toy TRS's COMPLETE DEVELOPMENT  dev .
--
-- Following the fuel-iteration / CK-machine architecture (the EvalU
-- pattern), the complete development  dev  is computed by a small-step
-- machine whose one step is a NON-RECURSIVE combinator iterated on a
-- fuel counter.  This file is the EvalU.agda analog: the configuration
-- and continuation-frame ENCODING plus the read-back projection lemmas
-- (all  axFst / axSnd ).  The step combinator  devStepU  (layer 2) and
-- the assembly  devF = readout(iter devStepU n (init e))  (layer 3) and
-- the  dev  closure equations build on top.
--
-- ======================================================================
-- THE MACHINE.   dev  is a bottom-up traversal:
--     dev ze            = ze
--     dev (su t)        = su (dev t)
--     dev (ad ze y)     = dev y
--     dev (ad (su x) y) = su (ad (dev x) (dev y))
--     dev (ad (ad p q) y) = ad (dev (ad p q)) (dev y)
-- realised as a CK machine over the T4.TrsCodeObj codes:
--
--   cfgEV  t K  -- "develop term  t , then continue with  K "
--   cfgRT  val K  -- "return developed value  val  to continuation  K "
--   cfgHALT val   -- "done; the developed term is  val "
--
-- Continuation frames (right-nested tagged list  kont ):
--   frmSu        -- await  dev t ;  return  su# (dev t)
--   frmAdSu1 y   -- (ad (su x) y, stage 1) await dev x = v1; go develop y
--                   under  frmAdSu2 v1
--   frmAdSu2 v1  -- await dev y = v2; return  su# (ad# v1 v2)
--   frmAd1 y     -- (ad (ad..) y, stage 1) await dev a = v1; go develop y
--                   under  frmAd2 v1
--   frmAd2 v1    -- await dev y = v2; return  ad# v1 v2
-- (the  ad ze y  case needs NO frame:  cfgEV (ad# ze# y) K  ->  cfgEV y K .)
--
-- Transitions (realised by  devStepU  in layer 2):
--   cfgEV t K , hd t = ze       ->  cfgRT t K
--   cfgEV t K , hd t = su, t=su# t1  ->  cfgEV t1 (kons frmSu K)
--   cfgEV t K , hd t = ad, t=ad# a y :
--       hd a = ze  ->  cfgEV y K
--       hd a = su  ->  cfgEV (ar a) (kons (frmAdSu1 y) K)
--       hd a = ad  ->  cfgEV a (kons (frmAd1 y) K)
--   cfgRT val konEmpty            ->  cfgHALT val
--   cfgRT val (kons frmSu rest)   ->  cfgRT (su# val) rest
--   cfgRT val (kons (frmAdSu1 y) rest) -> cfgEV y (kons (frmAdSu2 val) rest)
--   cfgRT val (kons (frmAdSu2 v1) rest)-> cfgRT (su# (ad# v1 val)) rest
--   cfgRT val (kons (frmAd1 y) rest)   -> cfgEV y (kons (frmAd2 val) rest)
--   cfgRT val (kons (frmAd2 v1) rest)  -> cfgRT (ad# v1 val) rest
--
-- This layer: the constructors + projection lemmas only.  No dispatch
-- logic, no induction, no postulates, no holes.

module T4.DevMachine where

open import T4.Base
open import T4.TrsCodeObj using ( ze# ; su# ; ad# )

------------------------------------------------------------------------
-- Tags.  Config modes and frame kinds live in two disjoint namespaces
-- (a mode tag is read at a config position, a frame tag at a frame
-- position), so the small numerals may be reused.

mEV : Nat
mEV = 1

mRT : Nat
mRT = 2

mHALT : Nat
mHALT = 3

fSu : Nat
fSu = 1

fAdSu1 : Nat
fAdSu1 = 2

fAdSu2 : Nat
fAdSu2 = 3

fAd1 : Nat
fAd1 = 4

fAd2 : Nat
fAd2 = 5

------------------------------------------------------------------------
-- Configurations.  Uniform tagged pairs:  Pair (natCode mode) payload .

cfgEV : Term -> Term -> Term
cfgEV t K = ap2 Pair (natCode mEV) (ap2 Pair t K)

cfgRT : Term -> Term -> Term
cfgRT val K = ap2 Pair (natCode mRT) (ap2 Pair val K)

cfgHALT : Term -> Term
cfgHALT val = ap2 Pair (natCode mHALT) val

------------------------------------------------------------------------
-- Continuation list.  TAGGED so emptiness is a NUMERAL test (the head
-- flag  O / s O  is usable directly as a condFork flag):
--   konEmpty        = Pair O      O
--   kons frame rest = Pair (s O)  (Pair frame rest)

konEmpty : Term
konEmpty = ap2 Pair O O

kons : Term -> Term -> Term
kons frame rest = ap2 Pair (ap1 s O) (ap2 Pair frame rest)

------------------------------------------------------------------------
-- Continuation frames.

frmSu : Term
frmSu = ap2 Pair (natCode fSu) O

frmAdSu1 : Term -> Term
frmAdSu1 y = ap2 Pair (natCode fAdSu1) y

frmAdSu2 : Term -> Term
frmAdSu2 v1 = ap2 Pair (natCode fAdSu2) v1

frmAd1 : Term -> Term
frmAd1 y = ap2 Pair (natCode fAd1) y

frmAd2 : Term -> Term
frmAd2 v1 = ap2 Pair (natCode fAd2) v1

------------------------------------------------------------------------
-- Config projections: mode (= Fst config) and body (= Snd config).

mode_cfgEV : (t K : Term) -> Deriv (eqF (ap1 Fst (cfgEV t K)) (natCode mEV))
mode_cfgEV t K = axFst (natCode mEV) (ap2 Pair t K)

mode_cfgRT : (val K : Term) -> Deriv (eqF (ap1 Fst (cfgRT val K)) (natCode mRT))
mode_cfgRT val K = axFst (natCode mRT) (ap2 Pair val K)

mode_cfgHALT : (val : Term) -> Deriv (eqF (ap1 Fst (cfgHALT val)) (natCode mHALT))
mode_cfgHALT val = axFst (natCode mHALT) val

body_cfgEV : (t K : Term) -> Deriv (eqF (ap1 Snd (cfgEV t K)) (ap2 Pair t K))
body_cfgEV t K = axSnd (natCode mEV) (ap2 Pair t K)

body_cfgRT : (val K : Term) -> Deriv (eqF (ap1 Snd (cfgRT val K)) (ap2 Pair val K))
body_cfgRT val K = axSnd (natCode mRT) (ap2 Pair val K)

body_cfgHALT : (val : Term) -> Deriv (eqF (ap1 Snd (cfgHALT val)) val)
body_cfgHALT val = axSnd (natCode mHALT) val

-- EV / RT body fields:  body = Pair term/val  kont .

ev_term : (t K : Term) -> Deriv (eqF (ap1 Fst (ap2 Pair t K)) t)
ev_term t K = axFst t K

ev_kont : (t K : Term) -> Deriv (eqF (ap1 Snd (ap2 Pair t K)) K)
ev_kont t K = axSnd t K

rt_val : (val K : Term) -> Deriv (eqF (ap1 Fst (ap2 Pair val K)) val)
rt_val val K = axFst val K

rt_kont : (val K : Term) -> Deriv (eqF (ap1 Snd (ap2 Pair val K)) K)
rt_kont val K = axSnd val K

------------------------------------------------------------------------
-- Kont (tagged-list) projections.

konsFlag_empty : Deriv (eqF (ap1 Fst konEmpty) O)
konsFlag_empty = axFst O O

konsFlag_cons : (frame rest : Term) -> Deriv (eqF (ap1 Fst (kons frame rest)) (ap1 s O))
konsFlag_cons frame rest = axFst (ap1 s O) (ap2 Pair frame rest)

konsBody : (frame rest : Term) ->
            Deriv (eqF (ap1 Snd (kons frame rest)) (ap2 Pair frame rest))
konsBody frame rest = axSnd (ap1 s O) (ap2 Pair frame rest)

konsHd : (frame rest : Term) -> Deriv (eqF (ap1 Fst (ap2 Pair frame rest)) frame)
konsHd frame rest = axFst frame rest

konsTl : (frame rest : Term) -> Deriv (eqF (ap1 Snd (ap2 Pair frame rest)) rest)
konsTl frame rest = axSnd frame rest

------------------------------------------------------------------------
-- Frame tag (= Fst frame) and payload (= Snd frame) projections.

frmSu_tag : Deriv (eqF (ap1 Fst frmSu) (natCode fSu))
frmSu_tag = axFst (natCode fSu) O

frmAdSu1_tag : (y : Term) -> Deriv (eqF (ap1 Fst (frmAdSu1 y)) (natCode fAdSu1))
frmAdSu1_tag y = axFst (natCode fAdSu1) y

frmAdSu1_body : (y : Term) -> Deriv (eqF (ap1 Snd (frmAdSu1 y)) y)
frmAdSu1_body y = axSnd (natCode fAdSu1) y

frmAdSu2_tag : (v1 : Term) -> Deriv (eqF (ap1 Fst (frmAdSu2 v1)) (natCode fAdSu2))
frmAdSu2_tag v1 = axFst (natCode fAdSu2) v1

frmAdSu2_body : (v1 : Term) -> Deriv (eqF (ap1 Snd (frmAdSu2 v1)) v1)
frmAdSu2_body v1 = axSnd (natCode fAdSu2) v1

frmAd1_tag : (y : Term) -> Deriv (eqF (ap1 Fst (frmAd1 y)) (natCode fAd1))
frmAd1_tag y = axFst (natCode fAd1) y

frmAd1_body : (y : Term) -> Deriv (eqF (ap1 Snd (frmAd1 y)) y)
frmAd1_body y = axSnd (natCode fAd1) y

frmAd2_tag : (v1 : Term) -> Deriv (eqF (ap1 Fst (frmAd2 v1)) (natCode fAd2))
frmAd2_tag v1 = axFst (natCode fAd2) v1

frmAd2_body : (v1 : Term) -> Deriv (eqF (ap1 Snd (frmAd2 v1)) v1)
frmAd2_body v1 = axSnd (natCode fAd2) v1
