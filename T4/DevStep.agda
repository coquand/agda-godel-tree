{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.DevStep -- STAGE I3 of attempt3 §11, layer 2: the one-step
-- combinator  devStepU : Fun1  of the complete-development CK machine
-- (the EvalUStep.agda analog).
--
-- devStepU is a pure combinator (NO recursion): a dispatch on the
-- configuration mode (EV / RT / HALT), with a 3-way head-tag cascade
-- inside EV (+ a 3-way first-child cascade in the ad case) and a 5-way
-- frame cascade (+ empty test) inside RT.  Built from Fst / Snd / Pair /
-- condFork / natEqF surgery via the `fork` helper (T4.EvalUStep).
--
-- This file: the definitions (accessors, branch bodies, cascades,
-- devStepU) and the per-transition reduction lemmas  devStepU_* , one
-- per row of the transition table in T4.DevMachine's header.

module T4.DevStep where

open import T4.Base
open import T4.DevMachine
open import T4.TrsCodeObj using
  ( ze# ; su# ; ad# ; tagZe ; tagSu ; tagAd
  ; hd_ze ; hd_su ; hd_ad ; ar_su ; ad1 ; ad2 )

open import T4.EvalUStep using ( fork ; fireT ; fireF )
open import BRA3.Fan      using ( compose1U_eq )
open import BRA3.SubT.NatEq    using ( natEqF ; natEq_eq )
open import BRA3.SubT.V2NatNeq using ( NatNeqWitness ; natEqF_at_neq ; decideNatNeq )

------------------------------------------------------------------------
-- The kont-cons builder (Fun1 layer):
--   ap1 (konsF FF FR) c = kons (FF c) (FR c) .

konsF : Fun1 -> Fun1 -> Fun1
konsF FF FR = C Pair (constN 1) (C Pair FF FR)

konsF_value : (FF FR : Fun1) (c : Term) ->
  Deriv (eqF (ap1 (konsF FF FR) c) (kons (ap1 FF c) (ap1 FR c)))
konsF_value FF FR c =
  ruleTrans (ax_C Pair (constN 1) (C Pair FF FR) c)
    (ruleTrans (congL Pair (ap1 (C Pair FF FR) c) (constN_eq 1 c))
      (congR Pair (ap1 s O) (ax_C Pair FF FR c)))

------------------------------------------------------------------------
-- EV accessors (config = cfgEV t K).

eTerm : Fun1                 -- t
eTerm = compose1U Fst Snd

eKont : Fun1                 -- K
eKont = compose1U Snd Snd

eHd : Fun1                   -- Fst t   (head tag of t)
eHd = compose1U Fst eTerm

eAr : Fun1                   -- Snd t   (payload: t1 for su#, Pair a y for ad#)
eAr = compose1U Snd eTerm

eFirst : Fun1                -- Fst (Snd t)   (first subterm a of ad#)
eFirst = compose1U Fst eAr

eSecond : Fun1               -- Snd (Snd t)   (second subterm y of ad#)
eSecond = compose1U Snd eAr

eFirstHd : Fun1              -- Fst (Fst (Snd t))   (head tag of a)
eFirstHd = compose1U Fst eFirst

eFirstAr : Fun1              -- Snd (Fst (Snd t))   (ar of a: x for su#)
eFirstAr = compose1U Snd eFirst

-- Accessor value lemmas (generic in t, K).

eTerm_ev : (t K : Term) -> Deriv (eqF (ap1 eTerm (cfgEV t K)) t)
eTerm_ev t K =
  ruleTrans (compose1U_eq Fst Snd (cfgEV t K))
    (ruleTrans (cong1 Fst (body_cfgEV t K)) (ev_term t K))

eKont_ev : (t K : Term) -> Deriv (eqF (ap1 eKont (cfgEV t K)) K)
eKont_ev t K =
  ruleTrans (compose1U_eq Snd Snd (cfgEV t K))
    (ruleTrans (cong1 Snd (body_cfgEV t K)) (ev_kont t K))

eHd_ev : (t K : Term) -> Deriv (eqF (ap1 eHd (cfgEV t K)) (ap1 Fst t))
eHd_ev t K =
  ruleTrans (compose1U_eq Fst eTerm (cfgEV t K)) (cong1 Fst (eTerm_ev t K))

eAr_ev : (t K : Term) -> Deriv (eqF (ap1 eAr (cfgEV t K)) (ap1 Snd t))
eAr_ev t K =
  ruleTrans (compose1U_eq Snd eTerm (cfgEV t K)) (cong1 Snd (eTerm_ev t K))

eFirst_ev : (t K : Term) -> Deriv (eqF (ap1 eFirst (cfgEV t K)) (ap1 Fst (ap1 Snd t)))
eFirst_ev t K =
  ruleTrans (compose1U_eq Fst eAr (cfgEV t K)) (cong1 Fst (eAr_ev t K))

eSecond_ev : (t K : Term) -> Deriv (eqF (ap1 eSecond (cfgEV t K)) (ap1 Snd (ap1 Snd t)))
eSecond_ev t K =
  ruleTrans (compose1U_eq Snd eAr (cfgEV t K)) (cong1 Snd (eAr_ev t K))

eFirstHd_ev : (t K : Term) ->
  Deriv (eqF (ap1 eFirstHd (cfgEV t K)) (ap1 Fst (ap1 Fst (ap1 Snd t))))
eFirstHd_ev t K =
  ruleTrans (compose1U_eq Fst eFirst (cfgEV t K)) (cong1 Fst (eFirst_ev t K))

eFirstAr_ev : (t K : Term) ->
  Deriv (eqF (ap1 eFirstAr (cfgEV t K)) (ap1 Snd (ap1 Fst (ap1 Snd t))))
eFirstAr_ev t K =
  ruleTrans (compose1U_eq Snd eFirst (cfgEV t K)) (cong1 Snd (eFirst_ev t K))

------------------------------------------------------------------------
-- Frame builders (Fun1 of config).

mkFrmSu : Fun1               -- frmSu (constant)
mkFrmSu = C Pair (constN fSu) o

mkFrmSu_value : (c : Term) -> Deriv (eqF (ap1 mkFrmSu c) frmSu)
mkFrmSu_value c =
  ruleTrans (ax_C Pair (constN fSu) o c)
    (ruleTrans (congL Pair (ap1 o c) (constN_eq fSu c))
      (congR Pair (natCode fSu) (ax_o c)))

mkFrmAdSu1 : Fun1            -- frmAdSu1 (eSecond) = frmAdSu1 y
mkFrmAdSu1 = C Pair (constN fAdSu1) eSecond

mkFrmAd1 : Fun1              -- frmAd1 (eSecond) = frmAd1 y
mkFrmAd1 = C Pair (constN fAd1) eSecond

------------------------------------------------------------------------
-- EV branch bodies (Fun1 of config) + their value lemmas.

-- ze:  cfgRT t K   (dev ze = ze; return t unchanged).
evZe : Fun1
evZe = C Pair (constN mRT) (C Pair eTerm eKont)

evZe_value : (t K : Term) -> Deriv (eqF (ap1 evZe (cfgEV t K)) (cfgRT t K))
evZe_value t K =
  ruleTrans (ax_C Pair (constN mRT) (C Pair eTerm eKont) (cfgEV t K))
    (ruleTrans (congL Pair (ap1 (C Pair eTerm eKont) (cfgEV t K)) (constN_eq mRT (cfgEV t K)))
      (congR Pair (natCode mRT)
        (ruleTrans (ax_C Pair eTerm eKont (cfgEV t K))
          (ruleTrans (congL Pair (ap1 eKont (cfgEV t K)) (eTerm_ev t K))
            (congR Pair t (eKont_ev t K))))))

-- su:  cfgEV (Snd t) (kons frmSu K).
evSu : Fun1
evSu = C Pair (constN mEV) (C Pair eAr (konsF mkFrmSu eKont))

evSu_value : (t K : Term) ->
  Deriv (eqF (ap1 evSu (cfgEV t K)) (cfgEV (ap1 Snd t) (kons frmSu K)))
evSu_value t K =
  let c : Term
      c = cfgEV t K
      eKt : Deriv (eqF (ap1 (konsF mkFrmSu eKont) c) (kons frmSu K))
      eKt = ruleTrans (konsF_value mkFrmSu eKont c)
              (congR Pair (ap1 s O)
                (ruleTrans (congL Pair (ap1 eKont c) (mkFrmSu_value c))
                           (congR Pair frmSu (eKont_ev t K))))
  in ruleTrans (ax_C Pair (constN mEV) (C Pair eAr (konsF mkFrmSu eKont)) c)
       (ruleTrans (congL Pair (ap1 (C Pair eAr (konsF mkFrmSu eKont)) c) (constN_eq mEV c))
         (congR Pair (natCode mEV)
           (ruleTrans (ax_C Pair eAr (konsF mkFrmSu eKont) c)
             (ruleTrans (congL Pair (ap1 (konsF mkFrmSu eKont) c) (eAr_ev t K))
               (congR Pair (ap1 Snd t) eKt)))))

-- ad / first = ze:  cfgEV (Snd (Snd t)) K   (dev (ad ze y) = dev y).
evAdZe : Fun1
evAdZe = C Pair (constN mEV) (C Pair eSecond eKont)

evAdZe_value : (t K : Term) ->
  Deriv (eqF (ap1 evAdZe (cfgEV t K)) (cfgEV (ap1 Snd (ap1 Snd t)) K))
evAdZe_value t K =
  ruleTrans (ax_C Pair (constN mEV) (C Pair eSecond eKont) (cfgEV t K))
    (ruleTrans (congL Pair (ap1 (C Pair eSecond eKont) (cfgEV t K)) (constN_eq mEV (cfgEV t K)))
      (congR Pair (natCode mEV)
        (ruleTrans (ax_C Pair eSecond eKont (cfgEV t K))
          (ruleTrans (congL Pair (ap1 eKont (cfgEV t K)) (eSecond_ev t K))
            (congR Pair (ap1 Snd (ap1 Snd t)) (eKont_ev t K))))))

-- ad / first = su:  cfgEV (Snd (Fst (Snd t))) (kons (frmAdSu1 (Snd (Snd t))) K).
evAdSu : Fun1
evAdSu = C Pair (constN mEV) (C Pair eFirstAr (konsF mkFrmAdSu1 eKont))

evAdSu_value : (t K : Term) ->
  Deriv (eqF (ap1 evAdSu (cfgEV t K))
             (cfgEV (ap1 Snd (ap1 Fst (ap1 Snd t)))
                    (kons (frmAdSu1 (ap1 Snd (ap1 Snd t))) K)))
evAdSu_value t K =
  let c : Term
      c = cfgEV t K
      eFrm : Deriv (eqF (ap1 mkFrmAdSu1 c) (frmAdSu1 (ap1 Snd (ap1 Snd t))))
      eFrm = ruleTrans (ax_C Pair (constN fAdSu1) eSecond c)
               (ruleTrans (congL Pair (ap1 eSecond c) (constN_eq fAdSu1 c))
                 (congR Pair (natCode fAdSu1) (eSecond_ev t K)))
      eKt : Deriv (eqF (ap1 (konsF mkFrmAdSu1 eKont) c)
                       (kons (frmAdSu1 (ap1 Snd (ap1 Snd t))) K))
      eKt = ruleTrans (konsF_value mkFrmAdSu1 eKont c)
              (congR Pair (ap1 s O)
                (ruleTrans (congL Pair (ap1 eKont c) eFrm)
                           (congR Pair (frmAdSu1 (ap1 Snd (ap1 Snd t))) (eKont_ev t K))))
  in ruleTrans (ax_C Pair (constN mEV) (C Pair eFirstAr (konsF mkFrmAdSu1 eKont)) c)
       (ruleTrans (congL Pair (ap1 (C Pair eFirstAr (konsF mkFrmAdSu1 eKont)) c) (constN_eq mEV c))
         (congR Pair (natCode mEV)
           (ruleTrans (ax_C Pair eFirstAr (konsF mkFrmAdSu1 eKont) c)
             (ruleTrans (congL Pair (ap1 (konsF mkFrmAdSu1 eKont) c) (eFirstAr_ev t K))
               (congR Pair (ap1 Snd (ap1 Fst (ap1 Snd t))) eKt)))))

-- ad / first = ad:  cfgEV (Fst (Snd t)) (kons (frmAd1 (Snd (Snd t))) K).
evAdAd : Fun1
evAdAd = C Pair (constN mEV) (C Pair eFirst (konsF mkFrmAd1 eKont))

evAdAd_value : (t K : Term) ->
  Deriv (eqF (ap1 evAdAd (cfgEV t K))
             (cfgEV (ap1 Fst (ap1 Snd t))
                    (kons (frmAd1 (ap1 Snd (ap1 Snd t))) K)))
evAdAd_value t K =
  let c : Term
      c = cfgEV t K
      eFrm : Deriv (eqF (ap1 mkFrmAd1 c) (frmAd1 (ap1 Snd (ap1 Snd t))))
      eFrm = ruleTrans (ax_C Pair (constN fAd1) eSecond c)
               (ruleTrans (congL Pair (ap1 eSecond c) (constN_eq fAd1 c))
                 (congR Pair (natCode fAd1) (eSecond_ev t K)))
      eKt : Deriv (eqF (ap1 (konsF mkFrmAd1 eKont) c)
                       (kons (frmAd1 (ap1 Snd (ap1 Snd t))) K))
      eKt = ruleTrans (konsF_value mkFrmAd1 eKont c)
              (congR Pair (ap1 s O)
                (ruleTrans (congL Pair (ap1 eKont c) eFrm)
                           (congR Pair (frmAd1 (ap1 Snd (ap1 Snd t))) (eKont_ev t K))))
  in ruleTrans (ax_C Pair (constN mEV) (C Pair eFirst (konsF mkFrmAd1 eKont)) c)
       (ruleTrans (congL Pair (ap1 (C Pair eFirst (konsF mkFrmAd1 eKont)) c) (constN_eq mEV c))
         (congR Pair (natCode mEV)
           (ruleTrans (ax_C Pair eFirst (konsF mkFrmAd1 eKont) c)
             (ruleTrans (congL Pair (ap1 (konsF mkFrmAd1 eKont) c) (eFirst_ev t K))
               (congR Pair (ap1 Fst (ap1 Snd t)) eKt)))))

------------------------------------------------------------------------
-- EV cascades.  Head-tag tests (TrsCodeObj tags 0/1/2).

testHd : Nat -> Fun1
testHd k = C natEqF eHd (constN k)

testFirstHd : Nat -> Fun1
testFirstHd k = C natEqF eFirstHd (constN k)

-- ad sub-cascade: first = ze (0) ; else first = su (1) ; else ad (2).
evAd : Fun1
evAd = fork evAdZe (fork evAdSu evAdAd (testFirstHd 1)) (testFirstHd 0)

evBranch : Fun1
evBranch = fork evZe (fork evSu evAd (testHd 1)) (testHd 0)

------------------------------------------------------------------------
-- RT accessors (config = cfgRT val K).

rVal : Fun1                  -- val
rVal = compose1U Fst Snd

rKont : Fun1                 -- K
rKont = compose1U Snd Snd

rHasFrame : Fun1            -- Fst K   (O empty / s O cons)
rHasFrame = compose1U Fst rKont

rCons : Fun1                -- Snd K = Pair frame rest  (when cons)
rCons = compose1U Snd rKont

rFrame : Fun1
rFrame = compose1U Fst rCons

rRest : Fun1
rRest = compose1U Snd rCons

rFtag : Fun1                -- Fst frame
rFtag = compose1U Fst rFrame

rFdata : Fun1              -- Snd frame
rFdata = compose1U Snd rFrame

-- Accessor value lemmas (generic in val, K).

rVal_rt : (val K : Term) -> Deriv (eqF (ap1 rVal (cfgRT val K)) val)
rVal_rt val K =
  ruleTrans (compose1U_eq Fst Snd (cfgRT val K))
    (ruleTrans (cong1 Fst (body_cfgRT val K)) (rt_val val K))

rKont_rt : (val K : Term) -> Deriv (eqF (ap1 rKont (cfgRT val K)) K)
rKont_rt val K =
  ruleTrans (compose1U_eq Snd Snd (cfgRT val K))
    (ruleTrans (cong1 Snd (body_cfgRT val K)) (rt_kont val K))

rHasFrame_rt : (val K : Term) -> Deriv (eqF (ap1 rHasFrame (cfgRT val K)) (ap1 Fst K))
rHasFrame_rt val K =
  ruleTrans (compose1U_eq Fst rKont (cfgRT val K)) (cong1 Fst (rKont_rt val K))

rCons_rt : (val K : Term) -> Deriv (eqF (ap1 rCons (cfgRT val K)) (ap1 Snd K))
rCons_rt val K =
  ruleTrans (compose1U_eq Snd rKont (cfgRT val K)) (cong1 Snd (rKont_rt val K))

rFrame_rt : (val K : Term) ->
  Deriv (eqF (ap1 rFrame (cfgRT val K)) (ap1 Fst (ap1 Snd K)))
rFrame_rt val K =
  ruleTrans (compose1U_eq Fst rCons (cfgRT val K)) (cong1 Fst (rCons_rt val K))

rRest_rt : (val K : Term) ->
  Deriv (eqF (ap1 rRest (cfgRT val K)) (ap1 Snd (ap1 Snd K)))
rRest_rt val K =
  ruleTrans (compose1U_eq Snd rCons (cfgRT val K)) (cong1 Snd (rCons_rt val K))

rFtag_rt : (val K : Term) ->
  Deriv (eqF (ap1 rFtag (cfgRT val K)) (ap1 Fst (ap1 Fst (ap1 Snd K))))
rFtag_rt val K =
  ruleTrans (compose1U_eq Fst rFrame (cfgRT val K)) (cong1 Fst (rFrame_rt val K))

rFdata_rt : (val K : Term) ->
  Deriv (eqF (ap1 rFdata (cfgRT val K)) (ap1 Snd (ap1 Fst (ap1 Snd K))))
rFdata_rt val K =
  ruleTrans (compose1U_eq Snd rFrame (cfgRT val K)) (cong1 Snd (rFrame_rt val K))

------------------------------------------------------------------------
-- RT frame builders.

mkFrmAdSu2 : Fun1            -- frmAdSu2 val
mkFrmAdSu2 = C Pair (constN fAdSu2) rVal

mkFrmAd2 : Fun1             -- frmAd2 val
mkFrmAd2 = C Pair (constN fAd2) rVal

------------------------------------------------------------------------
-- RT branch bodies + value lemmas.

-- empty kont:  cfgHALT val.
rtEmpty : Fun1
rtEmpty = C Pair (constN mHALT) rVal

rtEmpty_value : (val K : Term) -> Deriv (eqF (ap1 rtEmpty (cfgRT val K)) (cfgHALT val))
rtEmpty_value val K =
  ruleTrans (ax_C Pair (constN mHALT) rVal (cfgRT val K))
    (ruleTrans (congL Pair (ap1 rVal (cfgRT val K)) (constN_eq mHALT (cfgRT val K)))
      (congR Pair (natCode mHALT) (rVal_rt val K)))

-- frmSu:  cfgRT (su# val) rest.
mkSuVal : Fun1              -- su# val = Pair (natCode 1) val
mkSuVal = C Pair (constN 1) rVal

rtFrmSu : Fun1
rtFrmSu = C Pair (constN mRT) (C Pair mkSuVal rRest)

rtFrmSu_value : (val K : Term) ->
  Deriv (eqF (ap1 rtFrmSu (cfgRT val K)) (cfgRT (su# (ap1 rVal (cfgRT val K))) (ap1 rRest (cfgRT val K))))
rtFrmSu_value val K =
  let c : Term
      c = cfgRT val K
      eSu : Deriv (eqF (ap1 mkSuVal c) (su# (ap1 rVal c)))
      eSu = ruleTrans (ax_C Pair (constN 1) rVal c)
              (congL Pair (ap1 rVal c) (constN_eq 1 c))
  in ruleTrans (ax_C Pair (constN mRT) (C Pair mkSuVal rRest) c)
       (ruleTrans (congL Pair (ap1 (C Pair mkSuVal rRest) c) (constN_eq mRT c))
         (congR Pair (natCode mRT)
           (ruleTrans (ax_C Pair mkSuVal rRest c)
             (congL Pair (ap1 rRest c) eSu))))

-- frmAdSu1:  cfgEV (Snd frame = y) (kons (frmAdSu2 val) rest).
rtFrmAdSu1 : Fun1
rtFrmAdSu1 = C Pair (constN mEV) (C Pair rFdata (konsF mkFrmAdSu2 rRest))

rtFrmAdSu1_value : (val K : Term) ->
  Deriv (eqF (ap1 rtFrmAdSu1 (cfgRT val K))
             (cfgEV (ap1 rFdata (cfgRT val K))
                    (kons (frmAdSu2 (ap1 rVal (cfgRT val K))) (ap1 rRest (cfgRT val K)))))
rtFrmAdSu1_value val K =
  let c : Term
      c = cfgRT val K
      eFrm : Deriv (eqF (ap1 mkFrmAdSu2 c) (frmAdSu2 (ap1 rVal c)))
      eFrm = ruleTrans (ax_C Pair (constN fAdSu2) rVal c)
               (congL Pair (ap1 rVal c) (constN_eq fAdSu2 c))
      eKt : Deriv (eqF (ap1 (konsF mkFrmAdSu2 rRest) c)
                       (kons (frmAdSu2 (ap1 rVal c)) (ap1 rRest c)))
      eKt = ruleTrans (konsF_value mkFrmAdSu2 rRest c)
              (congR Pair (ap1 s O) (congL Pair (ap1 rRest c) eFrm))
  in ruleTrans (ax_C Pair (constN mEV) (C Pair rFdata (konsF mkFrmAdSu2 rRest)) c)
       (ruleTrans (congL Pair (ap1 (C Pair rFdata (konsF mkFrmAdSu2 rRest)) c) (constN_eq mEV c))
         (congR Pair (natCode mEV)
           (ruleTrans (ax_C Pair rFdata (konsF mkFrmAdSu2 rRest) c)
             (congR Pair (ap1 rFdata c) eKt))))

-- frmAdSu2:  cfgRT (su# (ad# v1 val)) rest.
mkAdSu2 : Fun1             -- ad# (Snd frame = v1) val
mkAdSu2 = C Pair (constN 2) (C Pair rFdata rVal)

mkSuAd : Fun1             -- su# (ad# v1 val)
mkSuAd = C Pair (constN 1) mkAdSu2

rtFrmAdSu2 : Fun1
rtFrmAdSu2 = C Pair (constN mRT) (C Pair mkSuAd rRest)

rtFrmAdSu2_value : (val K : Term) ->
  Deriv (eqF (ap1 rtFrmAdSu2 (cfgRT val K))
             (cfgRT (su# (ad# (ap1 rFdata (cfgRT val K)) (ap1 rVal (cfgRT val K))))
                    (ap1 rRest (cfgRT val K))))
rtFrmAdSu2_value val K =
  let c : Term
      c = cfgRT val K
      eAd : Deriv (eqF (ap1 mkAdSu2 c) (ad# (ap1 rFdata c) (ap1 rVal c)))
      eAd = ruleTrans (ax_C Pair (constN 2) (C Pair rFdata rVal) c)
              (ruleTrans (congL Pair (ap1 (C Pair rFdata rVal) c) (constN_eq 2 c))
                (congR Pair (natCode 2) (ax_C Pair rFdata rVal c)))
      eSuAd : Deriv (eqF (ap1 mkSuAd c) (su# (ad# (ap1 rFdata c) (ap1 rVal c))))
      eSuAd = ruleTrans (ax_C Pair (constN 1) mkAdSu2 c)
                (ruleTrans (congL Pair (ap1 mkAdSu2 c) (constN_eq 1 c))
                  (congR Pair (ap1 s O) eAd))
  in ruleTrans (ax_C Pair (constN mRT) (C Pair mkSuAd rRest) c)
       (ruleTrans (congL Pair (ap1 (C Pair mkSuAd rRest) c) (constN_eq mRT c))
         (congR Pair (natCode mRT)
           (ruleTrans (ax_C Pair mkSuAd rRest c)
             (congL Pair (ap1 rRest c) eSuAd))))

-- frmAd1:  cfgEV (Snd frame = y) (kons (frmAd2 val) rest).
rtFrmAd1 : Fun1
rtFrmAd1 = C Pair (constN mEV) (C Pair rFdata (konsF mkFrmAd2 rRest))

rtFrmAd1_value : (val K : Term) ->
  Deriv (eqF (ap1 rtFrmAd1 (cfgRT val K))
             (cfgEV (ap1 rFdata (cfgRT val K))
                    (kons (frmAd2 (ap1 rVal (cfgRT val K))) (ap1 rRest (cfgRT val K)))))
rtFrmAd1_value val K =
  let c : Term
      c = cfgRT val K
      eFrm : Deriv (eqF (ap1 mkFrmAd2 c) (frmAd2 (ap1 rVal c)))
      eFrm = ruleTrans (ax_C Pair (constN fAd2) rVal c)
               (congL Pair (ap1 rVal c) (constN_eq fAd2 c))
      eKt : Deriv (eqF (ap1 (konsF mkFrmAd2 rRest) c)
                       (kons (frmAd2 (ap1 rVal c)) (ap1 rRest c)))
      eKt = ruleTrans (konsF_value mkFrmAd2 rRest c)
              (congR Pair (ap1 s O) (congL Pair (ap1 rRest c) eFrm))
  in ruleTrans (ax_C Pair (constN mEV) (C Pair rFdata (konsF mkFrmAd2 rRest)) c)
       (ruleTrans (congL Pair (ap1 (C Pair rFdata (konsF mkFrmAd2 rRest)) c) (constN_eq mEV c))
         (congR Pair (natCode mEV)
           (ruleTrans (ax_C Pair rFdata (konsF mkFrmAd2 rRest) c)
             (congR Pair (ap1 rFdata c) eKt))))

-- frmAd2:  cfgRT (ad# v1 val) rest.
mkAd2 : Fun1              -- ad# (Snd frame = v1) val
mkAd2 = C Pair (constN 2) (C Pair rFdata rVal)

rtFrmAd2 : Fun1
rtFrmAd2 = C Pair (constN mRT) (C Pair mkAd2 rRest)

rtFrmAd2_value : (val K : Term) ->
  Deriv (eqF (ap1 rtFrmAd2 (cfgRT val K))
             (cfgRT (ad# (ap1 rFdata (cfgRT val K)) (ap1 rVal (cfgRT val K)))
                    (ap1 rRest (cfgRT val K))))
rtFrmAd2_value val K =
  let c : Term
      c = cfgRT val K
      eAd : Deriv (eqF (ap1 mkAd2 c) (ad# (ap1 rFdata c) (ap1 rVal c)))
      eAd = ruleTrans (ax_C Pair (constN 2) (C Pair rFdata rVal) c)
              (ruleTrans (congL Pair (ap1 (C Pair rFdata rVal) c) (constN_eq 2 c))
                (congR Pair (natCode 2) (ax_C Pair rFdata rVal c)))
  in ruleTrans (ax_C Pair (constN mRT) (C Pair mkAd2 rRest) c)
       (ruleTrans (congL Pair (ap1 (C Pair mkAd2 rRest) c) (constN_eq mRT c))
         (congR Pair (natCode mRT)
           (ruleTrans (ax_C Pair mkAd2 rRest c)
             (congL Pair (ap1 rRest c) eAd))))

------------------------------------------------------------------------
-- RT cascades.

testFtag : Nat -> Fun1
testFtag k = C natEqF rFtag (constN k)

rtCons : Fun1
rtCons =
  fork rtFrmSu
    (fork rtFrmAdSu1
      (fork rtFrmAdSu2
        (fork rtFrmAd1 rtFrmAd2 (testFtag fAd1))
        (testFtag fAdSu2))
      (testFtag fAdSu1))
    (testFtag fSu)

rtBranch : Fun1
rtBranch = fork rtCons rtEmpty rHasFrame

------------------------------------------------------------------------
-- Mode dispatch and devStepU.

isEV : Fun1
isEV = C natEqF Fst (constN mEV)

isRT : Fun1
isRT = C natEqF Fst (constN mRT)

modeRT : Fun1
modeRT = fork rtBranch u isRT

devStepU : Fun1
devStepU = fork evBranch modeRT isEV

------------------------------------------------------------------------
-- Mode-test value lemmas.

isEV_cfgEV : (t K : Term) -> Deriv (eqF (ap1 isEV (cfgEV t K)) (ap1 s O))
isEV_cfgEV t K =
  let c = cfgEV t K
  in ruleTrans (ax_C natEqF Fst (constN mEV) c)
       (ruleTrans (congL natEqF (ap1 (constN mEV) c) (mode_cfgEV t K))
         (ruleTrans (congR natEqF (natCode mEV) (constN_eq mEV c)) (natEq_eq mEV)))

isEV_cfgRT : (val K : Term) -> Deriv (eqF (ap1 isEV (cfgRT val K)) O)
isEV_cfgRT val K =
  let c = cfgRT val K
  in ruleTrans (ax_C natEqF Fst (constN mEV) c)
       (ruleTrans (congL natEqF (ap1 (constN mEV) c) (mode_cfgRT val K))
         (ruleTrans (congR natEqF (natCode mRT) (constN_eq mEV c))
           (natEqF_at_neq mRT mEV (decideNatNeq mRT mEV (\ ())))))

isRT_cfgRT : (val K : Term) -> Deriv (eqF (ap1 isRT (cfgRT val K)) (ap1 s O))
isRT_cfgRT val K =
  let c = cfgRT val K
  in ruleTrans (ax_C natEqF Fst (constN mRT) c)
       (ruleTrans (congL natEqF (ap1 (constN mRT) c) (mode_cfgRT val K))
         (ruleTrans (congR natEqF (natCode mRT) (constN_eq mRT c)) (natEq_eq mRT)))

------------------------------------------------------------------------
-- EV head-tag test fire / skip, given the head value.

testHd_at : (k : Nat) (t K : Term) (tg : Nat) ->
  Deriv (eqF (ap1 Fst t) (natCode tg)) ->
  Deriv (eqF (ap1 (testHd k) (cfgEV t K)) (ap2 natEqF (natCode tg) (natCode k)))
testHd_at k t K tg headeq =
  let c = cfgEV t K
  in ruleTrans (ax_C natEqF eHd (constN k) c)
       (ruleTrans (congL natEqF (ap1 (constN k) c) (ruleTrans (eHd_ev t K) headeq))
         (congR natEqF (natCode tg) (constN_eq k c)))

hdFire : (k : Nat) (t K : Term) ->
  Deriv (eqF (ap1 Fst t) (natCode k)) ->
  Deriv (eqF (ap1 (testHd k) (cfgEV t K)) (ap1 s O))
hdFire k t K headeq = ruleTrans (testHd_at k t K k headeq) (natEq_eq k)

hdSkip : (k tg : Nat) (t K : Term) ->
  Deriv (eqF (ap1 Fst t) (natCode tg)) -> NatNeqWitness tg k ->
  Deriv (eqF (ap1 (testHd k) (cfgEV t K)) O)
hdSkip k tg t K headeq w = ruleTrans (testHd_at k t K tg headeq) (natEqF_at_neq tg k w)

testFirstHd_at : (k : Nat) (t K : Term) (tg : Nat) ->
  Deriv (eqF (ap1 Fst (ap1 Fst (ap1 Snd t))) (natCode tg)) ->
  Deriv (eqF (ap1 (testFirstHd k) (cfgEV t K)) (ap2 natEqF (natCode tg) (natCode k)))
testFirstHd_at k t K tg headeq =
  let c = cfgEV t K
  in ruleTrans (ax_C natEqF eFirstHd (constN k) c)
       (ruleTrans (congL natEqF (ap1 (constN k) c) (ruleTrans (eFirstHd_ev t K) headeq))
         (congR natEqF (natCode tg) (constN_eq k c)))

fhFire : (k : Nat) (t K : Term) ->
  Deriv (eqF (ap1 Fst (ap1 Fst (ap1 Snd t))) (natCode k)) ->
  Deriv (eqF (ap1 (testFirstHd k) (cfgEV t K)) (ap1 s O))
fhFire k t K headeq = ruleTrans (testFirstHd_at k t K k headeq) (natEq_eq k)

fhSkip : (k tg : Nat) (t K : Term) ->
  Deriv (eqF (ap1 Fst (ap1 Fst (ap1 Snd t))) (natCode tg)) -> NatNeqWitness tg k ->
  Deriv (eqF (ap1 (testFirstHd k) (cfgEV t K)) O)
fhSkip k tg t K headeq w = ruleTrans (testFirstHd_at k t K tg headeq) (natEqF_at_neq tg k w)

------------------------------------------------------------------------
-- RT frame / hasFrame test fire / skip.

testFtag_at : (k : Nat) (val K : Term) (tg : Nat) ->
  Deriv (eqF (ap1 Fst (ap1 Fst (ap1 Snd K))) (natCode tg)) ->
  Deriv (eqF (ap1 (testFtag k) (cfgRT val K)) (ap2 natEqF (natCode tg) (natCode k)))
testFtag_at k val K tg ftageq =
  let c = cfgRT val K
  in ruleTrans (ax_C natEqF rFtag (constN k) c)
       (ruleTrans (congL natEqF (ap1 (constN k) c) (ruleTrans (rFtag_rt val K) ftageq))
         (congR natEqF (natCode tg) (constN_eq k c)))

ftFire : (k : Nat) (val K : Term) ->
  Deriv (eqF (ap1 Fst (ap1 Fst (ap1 Snd K))) (natCode k)) ->
  Deriv (eqF (ap1 (testFtag k) (cfgRT val K)) (ap1 s O))
ftFire k val K ftageq = ruleTrans (testFtag_at k val K k ftageq) (natEq_eq k)

ftSkip : (k tg : Nat) (val K : Term) ->
  Deriv (eqF (ap1 Fst (ap1 Fst (ap1 Snd K))) (natCode tg)) -> NatNeqWitness tg k ->
  Deriv (eqF (ap1 (testFtag k) (cfgRT val K)) O)
ftSkip k tg val K ftageq w = ruleTrans (testFtag_at k val K tg ftageq) (natEqF_at_neq tg k w)
