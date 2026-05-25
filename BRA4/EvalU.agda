{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.EvalU -- the universal fuelled interpreter for the standard
-- Chaitin-Goedel I route (CHAITIN-G1-STANDARD-DIRECTION.md, EVALU-DESIGN.md).
--
-- This file: Phase E1, layer 1 -- the program coding (uniform `mcode`),
-- the configuration / continuation-frame encoding, and the soundness
-- projection lemmas.  `stepU` (the one-reduction combinator), `evalU`,
-- and `evalU_correct` build on top in the following layers.
--
-- ======================================================================
-- THE MACHINE (recap of EVALU-DESIGN.md).
-- ======================================================================
--
-- A small-step CK machine: `stepU : Fun1` is one total reduction (a
-- combinator, no recursion); `evalU(e,n)` = readout( stepU^n (init e) ),
-- the n-fold `iter` of `stepU`.  Configurations:
--
--   cfgEV   fc a K = pi (natCode tagEV)   (pi (pi fc a) K)   -- apply code fc to value a
--   cfgRT   v  K   = pi (natCode tagRT)   (pi v K)           -- return value v to kont K
--   cfgHALT v      = pi (natCode tagHALT) v                  -- halted with value v (kont empty)
--
-- Continuation frames (kont = right-nested list, empty = O, cons = pi frame rest):
--
--   frmApp2 Fc w     = pi (natCode tagApp2) (pi Fc w)             -- await z; EV(Fc, pi w z)
--   frmC1   gc h2c a  = pi (natCode tagC1)  (pi gc (pi h2c a))     -- C: await h1 a
--   frmR1   rc h1c x m = pi (natCode tagR1) (pi rc (pi h1c (pi x m))) -- R: await h2(x,m)
--   frmM    gc k      = pi (natCode tagM)   (pi gc k)             -- mu: await g k

module BRA4.EvalU where

open import BRA4.Base
open import BRA4.Tags
  using ( tag_s ; tag_o ; tag_u ; tag_C ; tag_v ; tag_R )

open import BRA3.Church      using ( pi )
open import BRA3.ChurchT117  using ( Fst )
open import BRA3.ChurchT116  using ( Snd )
open import BRA3.PairAlgebra using ( axFst ; axSnd )

------------------------------------------------------------------------
-- Tags.  Two disjoint namespaces (modes/frames inspected at config /
-- frame positions; code head-tags inspected at code positions), so the
-- small numbers may be reused across namespaces.

tagEV : Nat
tagEV = 1

tagRT : Nat
tagRT = 2

tagHALT : Nat
tagHALT = 3

tagApp2 : Nat
tagApp2 = 1

tagC1 : Nat
tagC1 = 2

tagR1 : Nat
tagR1 = 3

tagM : Nat
tagM = 4

-- The one new code head-tag (mu); the rest are BRA4.Tags tag_s..tag_R.
tag_mu : Nat
tag_mu = 13

------------------------------------------------------------------------
-- Uniform program coding.  Every node is  pi (natCode tag) payload ,
-- so the head tag is always  Fst  and the payload always  Snd .

mcode1 : Fun1 -> Term
mcode2 : Fun2 -> Term

mcode1 s           = ap2 pi (natCode tag_s) O
mcode1 o           = ap2 pi (natCode tag_o) O
mcode1 u           = ap2 pi (natCode tag_u) O
mcode1 (C g h1 h2) = ap2 pi (natCode tag_C)
                       (ap2 pi (mcode2 g) (ap2 pi (mcode1 h1) (mcode1 h2)))

mcode2 v           = ap2 pi (natCode tag_v) O
mcode2 (R g h1 h2) = ap2 pi (natCode tag_R)
                       (ap2 pi (mcode1 g) (ap2 pi (mcode2 h1) (mcode2 h2)))

mcodeMu : Term -> Term
mcodeMu gc = ap2 pi (natCode tag_mu) gc

------------------------------------------------------------------------
-- Configuration constructors.

cfgEV : Term -> Term -> Term -> Term
cfgEV fc a K = ap2 pi (natCode tagEV) (ap2 pi (ap2 pi fc a) K)

cfgRT : Term -> Term -> Term
cfgRT val K = ap2 pi (natCode tagRT) (ap2 pi val K)

cfgHALT : Term -> Term
cfgHALT val = ap2 pi (natCode tagHALT) val

------------------------------------------------------------------------
-- Continuation list.  TAGGED so that emptiness is a NUMERAL test:
-- the head flag is  O  (empty) or  s O  (cons), usable directly as a
-- condFork flag (a bare  pi  flag would not reduce condFork).
--
--   konEmpty       = pi O      O
--   kons frame rest = pi (s O) (pi frame rest)

konEmpty : Term
konEmpty = ap2 pi O O

kons : Term -> Term -> Term
kons frame rest = ap2 pi (ap1 s O) (ap2 pi frame rest)

------------------------------------------------------------------------
-- Frame constructors.

frmApp2 : Term -> Term -> Term
frmApp2 Fc w = ap2 pi (natCode tagApp2) (ap2 pi Fc w)

frmC1 : Term -> Term -> Term -> Term
frmC1 gc h2c a = ap2 pi (natCode tagC1) (ap2 pi gc (ap2 pi h2c a))

frmR1 : Term -> Term -> Term -> Term -> Term
frmR1 rc h1c x m = ap2 pi (natCode tagR1) (ap2 pi rc (ap2 pi h1c (ap2 pi x m)))

frmM : Term -> Term -> Term
frmM gc k = ap2 pi (natCode tagM) (ap2 pi gc k)

------------------------------------------------------------------------
-- Soundness projection lemmas: how Fst / Snd extract each field.  All
-- direct  axFst / axSnd .  These confirm the encoding is read-back-able
-- and supply the pieces  stepU 's dispatch composes.

-- Config mode (= Fst config) and body (= Snd config).

mode_cfgEV : (fc a K : Term) -> Deriv (eqF (ap1 Fst (cfgEV fc a K)) (natCode tagEV))
mode_cfgEV fc a K = axFst (natCode tagEV) (ap2 pi (ap2 pi fc a) K)

mode_cfgRT : (val K : Term) -> Deriv (eqF (ap1 Fst (cfgRT val K)) (natCode tagRT))
mode_cfgRT val K = axFst (natCode tagRT) (ap2 pi val K)

mode_cfgHALT : (val : Term) -> Deriv (eqF (ap1 Fst (cfgHALT val)) (natCode tagHALT))
mode_cfgHALT val = axFst (natCode tagHALT) val

body_cfgEV : (fc a K : Term) -> Deriv (eqF (ap1 Snd (cfgEV fc a K)) (ap2 pi (ap2 pi fc a) K))
body_cfgEV fc a K = axSnd (natCode tagEV) (ap2 pi (ap2 pi fc a) K)

body_cfgRT : (val K : Term) -> Deriv (eqF (ap1 Snd (cfgRT val K)) (ap2 pi val K))
body_cfgRT val K = axSnd (natCode tagRT) (ap2 pi val K)

body_cfgHALT : (val : Term) -> Deriv (eqF (ap1 Snd (cfgHALT val)) val)
body_cfgHALT val = axSnd (natCode tagHALT) val

-- EV body fields:  body = pi (pi fc a) K .
ev_funarg : (fc a K : Term) -> Deriv (eqF (ap1 Fst (ap2 pi (ap2 pi fc a) K)) (ap2 pi fc a))
ev_funarg fc a K = axFst (ap2 pi fc a) K

ev_kont : (fc a K : Term) -> Deriv (eqF (ap1 Snd (ap2 pi (ap2 pi fc a) K)) K)
ev_kont fc a K = axSnd (ap2 pi fc a) K

ev_fun : (fc a : Term) -> Deriv (eqF (ap1 Fst (ap2 pi fc a)) fc)
ev_fun fc a = axFst fc a

ev_arg : (fc a : Term) -> Deriv (eqF (ap1 Snd (ap2 pi fc a)) a)
ev_arg fc a = axSnd fc a

-- RT body fields:  body = pi val K .
rt_val : (val K : Term) -> Deriv (eqF (ap1 Fst (ap2 pi val K)) val)
rt_val val K = axFst val K

rt_kont : (val K : Term) -> Deriv (eqF (ap1 Snd (ap2 pi val K)) K)
rt_kont val K = axSnd val K

------------------------------------------------------------------------
-- Kont (tagged-list) projections.

konsFlag_empty : Deriv (eqF (ap1 Fst konEmpty) O)
konsFlag_empty = axFst O O

konsFlag_cons : (frame rest : Term) -> Deriv (eqF (ap1 Fst (kons frame rest)) (ap1 s O))
konsFlag_cons frame rest = axFst (ap1 s O) (ap2 pi frame rest)

konsBody : (frame rest : Term) ->
            Deriv (eqF (ap1 Snd (kons frame rest)) (ap2 pi frame rest))
konsBody frame rest = axSnd (ap1 s O) (ap2 pi frame rest)

konsHd : (frame rest : Term) -> Deriv (eqF (ap1 Fst (ap2 pi frame rest)) frame)
konsHd frame rest = axFst frame rest

konsTl : (frame rest : Term) -> Deriv (eqF (ap1 Snd (ap2 pi frame rest)) rest)
konsTl frame rest = axSnd frame rest

------------------------------------------------------------------------
-- Frame field projections.

frmApp2_tag : (Fc w : Term) -> Deriv (eqF (ap1 Fst (frmApp2 Fc w)) (natCode tagApp2))
frmApp2_tag Fc w = axFst (natCode tagApp2) (ap2 pi Fc w)

frmApp2_body : (Fc w : Term) -> Deriv (eqF (ap1 Snd (frmApp2 Fc w)) (ap2 pi Fc w))
frmApp2_body Fc w = axSnd (natCode tagApp2) (ap2 pi Fc w)

frmC1_tag : (gc h2c a : Term) -> Deriv (eqF (ap1 Fst (frmC1 gc h2c a)) (natCode tagC1))
frmC1_tag gc h2c a = axFst (natCode tagC1) (ap2 pi gc (ap2 pi h2c a))

frmC1_body : (gc h2c a : Term) ->
             Deriv (eqF (ap1 Snd (frmC1 gc h2c a)) (ap2 pi gc (ap2 pi h2c a)))
frmC1_body gc h2c a = axSnd (natCode tagC1) (ap2 pi gc (ap2 pi h2c a))

frmR1_tag : (rc h1c x m : Term) -> Deriv (eqF (ap1 Fst (frmR1 rc h1c x m)) (natCode tagR1))
frmR1_tag rc h1c x m = axFst (natCode tagR1) (ap2 pi rc (ap2 pi h1c (ap2 pi x m)))

frmR1_body : (rc h1c x m : Term) ->
             Deriv (eqF (ap1 Snd (frmR1 rc h1c x m)) (ap2 pi rc (ap2 pi h1c (ap2 pi x m))))
frmR1_body rc h1c x m = axSnd (natCode tagR1) (ap2 pi rc (ap2 pi h1c (ap2 pi x m)))

frmM_tag : (gc k : Term) -> Deriv (eqF (ap1 Fst (frmM gc k)) (natCode tagM))
frmM_tag gc k = axFst (natCode tagM) (ap2 pi gc k)

frmM_body : (gc k : Term) -> Deriv (eqF (ap1 Snd (frmM gc k)) (ap2 pi gc k))
frmM_body gc k = axSnd (natCode tagM) (ap2 pi gc k)

------------------------------------------------------------------------
-- Code head-tag / payload projections (always Fst / Snd, by uniformity).

head_mcode1_s : Deriv (eqF (ap1 Fst (mcode1 s)) (natCode tag_s))
head_mcode1_s = axFst (natCode tag_s) O

head_mcode1_o : Deriv (eqF (ap1 Fst (mcode1 o)) (natCode tag_o))
head_mcode1_o = axFst (natCode tag_o) O

head_mcode1_u : Deriv (eqF (ap1 Fst (mcode1 u)) (natCode tag_u))
head_mcode1_u = axFst (natCode tag_u) O

head_mcode1_C :
  (g : Fun2) (h1 h2 : Fun1) ->
  Deriv (eqF (ap1 Fst (mcode1 (C g h1 h2))) (natCode tag_C))
head_mcode1_C g h1 h2 =
  axFst (natCode tag_C) (ap2 pi (mcode2 g) (ap2 pi (mcode1 h1) (mcode1 h2)))

head_mcode2_v : Deriv (eqF (ap1 Fst (mcode2 v)) (natCode tag_v))
head_mcode2_v = axFst (natCode tag_v) O

head_mcode2_R :
  (g : Fun1) (h1 h2 : Fun2) ->
  Deriv (eqF (ap1 Fst (mcode2 (R g h1 h2))) (natCode tag_R))
head_mcode2_R g h1 h2 =
  axFst (natCode tag_R) (ap2 pi (mcode1 g) (ap2 pi (mcode2 h1) (mcode2 h2)))

head_mcodeMu : (gc : Term) -> Deriv (eqF (ap1 Fst (mcodeMu gc)) (natCode tag_mu))
head_mcodeMu gc = axFst (natCode tag_mu) gc

payload_mcode1_C :
  (g : Fun2) (h1 h2 : Fun1) ->
  Deriv (eqF (ap1 Snd (mcode1 (C g h1 h2)))
              (ap2 pi (mcode2 g) (ap2 pi (mcode1 h1) (mcode1 h2))))
payload_mcode1_C g h1 h2 =
  axSnd (natCode tag_C) (ap2 pi (mcode2 g) (ap2 pi (mcode1 h1) (mcode1 h2)))

payload_mcode2_R :
  (g : Fun1) (h1 h2 : Fun2) ->
  Deriv (eqF (ap1 Snd (mcode2 (R g h1 h2)))
              (ap2 pi (mcode1 g) (ap2 pi (mcode2 h1) (mcode2 h2))))
payload_mcode2_R g h1 h2 =
  axSnd (natCode tag_R) (ap2 pi (mcode1 g) (ap2 pi (mcode2 h1) (mcode2 h2)))

payload_mcodeMu : (gc : Term) -> Deriv (eqF (ap1 Snd (mcodeMu gc)) gc)
payload_mcodeMu gc = axSnd (natCode tag_mu) gc
