{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.EvalUStep -- the one-reduction combinator  stepU : Fun1  of the
-- universal interpreter (EVALU-DESIGN.md, Phase E1, layer 2).
--
-- stepU is a pure combinator (NO recursion): a 3-way dispatch on the
-- configuration mode (EV / RT / HALT), with a 7-way tag cascade inside
-- EV and a 4-way frame cascade (+ empty test) inside RT.  Built from
-- Fst / Snd / pi / condFork / natEqF surgery via the `fork` helper.
--
-- This layer: the definitions (accessors, branch bodies, cascades,
-- stepU) and the per-transition reduction lemmas  stepU_at_* .

module BRA4.EvalUStep where

open import BRA4.Base
open import BRA4.Tags
  using ( tag_s ; tag_o ; tag_u ; tag_C ; tag_v ; tag_R )
open import BRA4.EvalU

open import BRA3.Church          using ( pi ; predecessor ; T_p_S_v0 )
open import BRA3.ChurchT117      using ( Fst )
open import BRA3.ChurchT116      using ( Snd )
open import BRA3.PairAlgebra     using ( axFst ; axSnd ; compose1U ; compose1U_eq )
open import BRA3.Dispatch        using
  ( condFork ; condFork_true_nc ; condFork_false ; constN ; constN_eq )
open import BRA3.SubT.NatEq      using ( natEqF ; natEq_eq )
open import BRA3.SubT.V2NatNeq   using ( NatNeqWitness ; natEqF_at_neq ; decideNatNeq )

------------------------------------------------------------------------
-- The dispatch combinator:  fork trueB falseB flag .
--   ap1 (fork T F flag) c = condFork (pi (T c) (F c)) (flag c)
--   flag c = s _ -> T c   ;   flag c = O -> F c .

fork : Fun1 -> Fun1 -> Fun1 -> Fun1
fork trueB falseB flag = C condFork (C pi trueB falseB) flag

-- The kont-cons builder:  ap1 (konsF FF FR) c = kons (FF c) (FR c) .
konsF : Fun1 -> Fun1 -> Fun1
konsF FF FR = C pi (constN 1) (C pi FF FR)

------------------------------------------------------------------------
-- EV accessors (config = cfgEV fc a K).

gFunarg : Fun1                       -- Fst (Snd c) = pi fc a
gFunarg = compose1U Fst Snd

gKont : Fun1                         -- Snd (Snd c) = K
gKont = compose1U Snd Snd

gFc : Fun1                           -- fc
gFc = compose1U Fst gFunarg

gArg : Fun1                          -- a
gArg = compose1U Snd gFunarg

gTag : Fun1                          -- Fst fc
gTag = compose1U Fst gFc

gPayload : Fun1                      -- Snd fc
gPayload = compose1U Snd gFc

gPayG : Fun1                         -- Fst payload   (gc, for C / R)
gPayG = compose1U Fst gPayload

gPaySub : Fun1                       -- Snd payload   (pi h1c h2c)
gPaySub = compose1U Snd gPayload

gPayH1 : Fun1
gPayH1 = compose1U Fst gPaySub

gPayH2 : Fun1
gPayH2 = compose1U Snd gPaySub

gArgX : Fun1                         -- Fst a   (x, for R)
gArgX = compose1U Fst gArg

gArgM : Fun1                         -- Snd a   (m, for R)
gArgM = compose1U Snd gArg

gMpred : Fun1                        -- predecessor m
gMpred = compose1U predecessor gArgM

------------------------------------------------------------------------
-- EV branch bodies (Fun1 of config).

evBody_s : Fun1                      -- cfgRT (s a) K
evBody_s = C pi (constN tagRT) (C pi (compose1U s gArg) gKont)

evBody_o : Fun1                      -- cfgRT O K
evBody_o = C pi (constN tagRT) (C pi o gKont)

evBody_u : Fun1                      -- cfgRT a K
evBody_u = C pi (constN tagRT) (C pi gArg gKont)

evBody_v : Fun1                      -- cfgRT (Snd a) K
evBody_v = C pi (constN tagRT) (C pi (compose1U Snd gArg) gKont)

-- C: push frmC1 gc h2c a, evaluate h1c on a.
mkFrmC1 : Fun1                       -- frmC1 gc h2c a
mkFrmC1 = C pi (constN tagC1) (C pi gPayG (C pi gPayH2 gArg))

evBody_C : Fun1                      -- cfgEV h1c a (kons (frmC1 gc h2c a) K)
evBody_C = C pi (constN tagEV) (C pi (C pi gPayH1 gArg) (konsF mkFrmC1 gKont))

-- mu: push frmM gc O, evaluate gc on O.  (payload IS gc.)
mkFrmM0 : Fun1                       -- frmM gc O
mkFrmM0 = C pi (constN tagM) (C pi gPayload o)

evBody_mu : Fun1                     -- cfgEV gc O (kons (frmM gc O) K)
evBody_mu = C pi (constN tagEV) (C pi (C pi gPayload o) (konsF mkFrmM0 gKont))

-- R base (m = O): cfgEV gc x K.
evBody_Rbase : Fun1
evBody_Rbase = C pi (constN tagEV) (C pi (C pi gPayG gArgX) gKont)

-- R step (m = s m'): cfgEV h2c (pi x m') (kons (frmR1 fc h1c x m') K).
mkFrmR1 : Fun1                       -- frmR1 fc h1c x m'   (fc = whole R-code = gFc)
mkFrmR1 = C pi (constN tagR1) (C pi gFc (C pi gPayH1 (C pi gArgX gMpred)))

evBody_Rstep : Fun1
evBody_Rstep =
  C pi (constN tagEV)
    (C pi (C pi gPayH2 (C pi gArgX gMpred)) (konsF mkFrmR1 gKont))

evBody_R : Fun1                      -- condFork on m
evBody_R = fork evBody_Rstep evBody_Rbase gArgM

------------------------------------------------------------------------
-- EV tag tests and the 7-way cascade.

testTag : Nat -> Fun1
testTag k = C natEqF gTag (constN k)

-- Named cascade levels (so the firing proofs can name each falseB).
evCascR : Fun1
evCascR = fork evBody_R evBody_mu (testTag tag_R)

evCascC : Fun1
evCascC = fork evBody_C evCascR (testTag tag_C)

evCascV : Fun1
evCascV = fork evBody_v evCascC (testTag tag_v)

evCascU : Fun1
evCascU = fork evBody_u evCascV (testTag tag_u)

evCascO : Fun1
evCascO = fork evBody_o evCascU (testTag tag_o)

evBranch : Fun1
evBranch = fork evBody_s evCascO (testTag tag_s)

------------------------------------------------------------------------
-- RT accessors (config = cfgRT val K).

rVal : Fun1                          -- val
rVal = compose1U Fst Snd

rKont : Fun1                         -- K
rKont = compose1U Snd Snd

rHasFrame : Fun1                     -- Fst K  (O / s O)
rHasFrame = compose1U Fst rKont

rConsPart : Fun1                     -- Snd K = pi frame rest  (when cons)
rConsPart = compose1U Snd rKont

rFrame : Fun1
rFrame = compose1U Fst rConsPart

rRest : Fun1
rRest = compose1U Snd rConsPart

rFtag : Fun1                         -- Fst frame
rFtag = compose1U Fst rFrame

rFdata : Fun1                        -- Snd frame
rFdata = compose1U Snd rFrame

-- frame-data subfields:  d1 = Fst fdata , d2 = Snd fdata ,
-- d21 = Fst (Snd fdata) , d22 = Snd (Snd fdata) ,
-- d221 = Fst (Snd (Snd fdata)) , d222 = Snd (Snd (Snd fdata)) .
d1 : Fun1
d1 = compose1U Fst rFdata
d2 : Fun1
d2 = compose1U Snd rFdata
d21 : Fun1
d21 = compose1U Fst d2
d22 : Fun1
d22 = compose1U Snd d2
d221 : Fun1
d221 = compose1U Fst d22
d222 : Fun1
d222 = compose1U Snd d22

------------------------------------------------------------------------
-- RT branch bodies.

rtEmptyBranch : Fun1                 -- cfgHALT val
rtEmptyBranch = C pi (constN tagHALT) rVal

-- fApp2: fdata = pi Fcode w ; cfgEV Fcode (pi w val) restK.
rtBody_App2 : Fun1
rtBody_App2 = C pi (constN tagEV) (C pi (C pi d1 (C pi d2 rVal)) rRest)

-- fC1: fdata = pi gc (pi h2c a) ; value v1 = val .
--   cfgEV h2c a (kons (frmApp2 gc v1) restK).
mkFrmApp2_C1 : Fun1                  -- frmApp2 gc val
mkFrmApp2_C1 = C pi (constN tagApp2) (C pi d1 rVal)

rtBody_C1 : Fun1
rtBody_C1 = C pi (constN tagEV) (C pi (C pi d21 d22) (konsF mkFrmApp2_C1 rRest))

-- fR1: fdata = pi rc (pi h1c (pi x m')) ; value inner = val .
--   cfgEV rc (pi x m') (kons (frmApp2 h1c inner) restK).
mkFrmApp2_R1 : Fun1                  -- frmApp2 h1c val   (h1c = d21)
mkFrmApp2_R1 = C pi (constN tagApp2) (C pi d21 rVal)

rtBody_R1 : Fun1
rtBody_R1 =
  C pi (constN tagEV) (C pi (C pi d1 (C pi d221 d222)) (konsF mkFrmApp2_R1 rRest))

-- fM: fdata = pi gc k ; value w = val .  condFork on w.
rtBody_Mbase : Fun1                  -- w = O : cfgRT k restK
rtBody_Mbase = C pi (constN tagRT) (C pi d2 rRest)

mkFrmM_sk : Fun1                     -- frmM gc (s k)
mkFrmM_sk = C pi (constN tagM) (C pi d1 (compose1U s d2))

rtBody_Mstep : Fun1                  -- w = s _ : cfgEV gc (s k) (kons (frmM gc (s k)) restK)
rtBody_Mstep =
  C pi (constN tagEV) (C pi (C pi d1 (compose1U s d2)) (konsF mkFrmM_sk rRest))

rtBody_M : Fun1
rtBody_M = fork rtBody_Mstep rtBody_Mbase rVal

------------------------------------------------------------------------
-- RT frame tests and the 4-way cascade; the cons/empty split.

testFtag : Nat -> Fun1
testFtag k = C natEqF rFtag (constN k)

rtCascR1 : Fun1
rtCascR1 = fork rtBody_R1 rtBody_M (testFtag tagR1)

rtCascC1 : Fun1
rtCascC1 = fork rtBody_C1 rtCascR1 (testFtag tagC1)

rtConsBranch : Fun1
rtConsBranch = fork rtBody_App2 rtCascC1 (testFtag tagApp2)

rtBranch : Fun1
rtBranch = fork rtConsBranch rtEmptyBranch rHasFrame

------------------------------------------------------------------------
-- The mode dispatch and  stepU .

isEV : Fun1
isEV = C natEqF Fst (constN tagEV)

isRT : Fun1
isRT = C natEqF Fst (constN tagRT)

modeRT : Fun1
modeRT = fork rtBranch u isRT

stepU : Fun1
stepU = fork evBranch modeRT isEV

------------------------------------------------------------------------
-- Generic cascade firing (the Parse stepBody_to_* pattern, parametric).

fireT : (trueB falseB flag : Fun1) (input : Term) ->
        Deriv (eqF (ap1 flag input) (ap1 s O)) ->
        Deriv (eqF (ap1 (fork trueB falseB flag) input) (ap1 trueB input))
fireT trueB falseB flag input flagT =
  let pairT : Term
      pairT = ap1 (C pi trueB falseB) input
      e1 : Deriv (eqF (ap1 (fork trueB falseB flag) input)
                      (ap2 condFork pairT (ap1 flag input)))
      e1 = ax_C condFork (C pi trueB falseB) flag input
      e2 : Deriv (eqF (ap2 condFork pairT (ap1 flag input))
                      (ap2 condFork pairT (ap1 s O)))
      e2 = congR condFork pairT flagT
      e3 : Deriv (eqF (ap2 condFork pairT (ap1 s O)) (ap1 Fst pairT))
      e3 = condFork_true_nc pairT O
      e4 : Deriv (eqF pairT (ap2 pi (ap1 trueB input) (ap1 falseB input)))
      e4 = ax_C pi trueB falseB input
      e5 : Deriv (eqF (ap1 Fst (ap2 pi (ap1 trueB input) (ap1 falseB input)))
                      (ap1 trueB input))
      e5 = axFst (ap1 trueB input) (ap1 falseB input)
  in ruleTrans e1 (ruleTrans e2 (ruleTrans e3 (ruleTrans (cong1 Fst e4) e5)))

fireF : (trueB falseB flag : Fun1) (input : Term) ->
        Deriv (eqF (ap1 flag input) O) ->
        Deriv (eqF (ap1 (fork trueB falseB flag) input) (ap1 falseB input))
fireF trueB falseB flag input flagF =
  let pairT : Term
      pairT = ap1 (C pi trueB falseB) input
      e1 : Deriv (eqF (ap1 (fork trueB falseB flag) input)
                      (ap2 condFork pairT (ap1 flag input)))
      e1 = ax_C condFork (C pi trueB falseB) flag input
      e2 : Deriv (eqF (ap2 condFork pairT (ap1 flag input)) (ap2 condFork pairT O))
      e2 = congR condFork pairT flagF
      e3 : Deriv (eqF (ap2 condFork pairT O) (ap1 Snd pairT))
      e3 = condFork_false pairT
      e4 : Deriv (eqF pairT (ap2 pi (ap1 trueB input) (ap1 falseB input)))
      e4 = ax_C pi trueB falseB input
      e5 : Deriv (eqF (ap1 Snd (ap2 pi (ap1 trueB input) (ap1 falseB input)))
                      (ap1 falseB input))
      e5 = axSnd (ap1 trueB input) (ap1 falseB input)
  in ruleTrans e1 (ruleTrans e2 (ruleTrans e3 (ruleTrans (cong1 Snd e4) e5)))

------------------------------------------------------------------------
-- EV accessor-value lemmas (config = cfgEV fc a K).

gFunarg_ev : (fc a K : Term) -> Deriv (eqF (ap1 gFunarg (cfgEV fc a K)) (ap2 pi fc a))
gFunarg_ev fc a K =
  ruleTrans (compose1U_eq Fst Snd (cfgEV fc a K))
    (ruleTrans (cong1 Fst (body_cfgEV fc a K)) (ev_funarg fc a K))

gKont_ev : (fc a K : Term) -> Deriv (eqF (ap1 gKont (cfgEV fc a K)) K)
gKont_ev fc a K =
  ruleTrans (compose1U_eq Snd Snd (cfgEV fc a K))
    (ruleTrans (cong1 Snd (body_cfgEV fc a K)) (ev_kont fc a K))

gFc_ev : (fc a K : Term) -> Deriv (eqF (ap1 gFc (cfgEV fc a K)) fc)
gFc_ev fc a K =
  ruleTrans (compose1U_eq Fst gFunarg (cfgEV fc a K))
    (ruleTrans (cong1 Fst (gFunarg_ev fc a K)) (ev_fun fc a))

gArg_ev : (fc a K : Term) -> Deriv (eqF (ap1 gArg (cfgEV fc a K)) a)
gArg_ev fc a K =
  ruleTrans (compose1U_eq Snd gFunarg (cfgEV fc a K))
    (ruleTrans (cong1 Snd (gFunarg_ev fc a K)) (ev_arg fc a))

gTag_ev : (fc a K : Term) -> Deriv (eqF (ap1 gTag (cfgEV fc a K)) (ap1 Fst fc))
gTag_ev fc a K =
  ruleTrans (compose1U_eq Fst gFc (cfgEV fc a K)) (cong1 Fst (gFc_ev fc a K))

gPayload_ev : (fc a K : Term) -> Deriv (eqF (ap1 gPayload (cfgEV fc a K)) (ap1 Snd fc))
gPayload_ev fc a K =
  ruleTrans (compose1U_eq Snd gFc (cfgEV fc a K)) (cong1 Snd (gFc_ev fc a K))

------------------------------------------------------------------------
-- Mode test value at cfgEV.

isEV_cfgEV : (fc a K : Term) -> Deriv (eqF (ap1 isEV (cfgEV fc a K)) (ap1 s O))
isEV_cfgEV fc a K =
  let c : Term
      c = cfgEV fc a K
      e1 : Deriv (eqF (ap1 isEV c) (ap2 natEqF (ap1 Fst c) (ap1 (constN tagEV) c)))
      e1 = ax_C natEqF Fst (constN tagEV) c
      e2 : Deriv (eqF (ap2 natEqF (ap1 Fst c) (ap1 (constN tagEV) c))
                      (ap2 natEqF (natCode tagEV) (ap1 (constN tagEV) c)))
      e2 = congL natEqF (ap1 (constN tagEV) c) (mode_cfgEV fc a K)
      e3 : Deriv (eqF (ap2 natEqF (natCode tagEV) (ap1 (constN tagEV) c))
                      (ap2 natEqF (natCode tagEV) (natCode tagEV)))
      e3 = congR natEqF (natCode tagEV) (constN_eq tagEV c)
  in ruleTrans e1 (ruleTrans e2 (ruleTrans e3 (natEq_eq tagEV)))

------------------------------------------------------------------------
-- EV tag test value + fire / skip helpers.

testTag_at : (k : Nat) (fc a K : Term) (tg : Nat) ->
  Deriv (eqF (ap1 Fst fc) (natCode tg)) ->
  Deriv (eqF (ap1 (testTag k) (cfgEV fc a K)) (ap2 natEqF (natCode tg) (natCode k)))
testTag_at k fc a K tg headeq =
  let c : Term
      c = cfgEV fc a K
      e1 : Deriv (eqF (ap1 (testTag k) c) (ap2 natEqF (ap1 gTag c) (ap1 (constN k) c)))
      e1 = ax_C natEqF gTag (constN k) c
      gtag_v : Deriv (eqF (ap1 gTag c) (natCode tg))
      gtag_v = ruleTrans (gTag_ev fc a K) headeq
      e2 = congL natEqF (ap1 (constN k) c) gtag_v
      e3 = congR natEqF (natCode tg) (constN_eq k c)
  in ruleTrans e1 (ruleTrans e2 e3)

ttFireAt : (k : Nat) (fc a K : Term) ->
  Deriv (eqF (ap1 Fst fc) (natCode k)) ->
  Deriv (eqF (ap1 (testTag k) (cfgEV fc a K)) (ap1 s O))
ttFireAt k fc a K headeq =
  ruleTrans (testTag_at k fc a K k headeq) (natEq_eq k)

ttSkipAt : (k tg : Nat) (fc a K : Term) ->
  Deriv (eqF (ap1 Fst fc) (natCode tg)) -> NatNeqWitness tg k ->
  Deriv (eqF (ap1 (testTag k) (cfgEV fc a K)) O)
ttSkipAt k tg fc a K headeq w =
  ruleTrans (testTag_at k fc a K tg headeq) (natEqF_at_neq tg k w)

------------------------------------------------------------------------
-- EV leaf branch-body value lemmas.

evBody_s_value : (fc a K : Term) ->
  Deriv (eqF (ap1 evBody_s (cfgEV fc a K)) (cfgRT (ap1 s a) K))
evBody_s_value fc a K =
  let c : Term
      c = cfgEV fc a K
      e1 = ax_C pi (constN tagRT) (C pi (compose1U s gArg) gKont) c
      eRT = constN_eq tagRT c
      eInner1 = ax_C pi (compose1U s gArg) gKont c
      eSA : Deriv (eqF (ap1 (compose1U s gArg) c) (ap1 s a))
      eSA = ruleTrans (compose1U_eq s gArg c) (cong1 s (gArg_ev fc a K))
      eInner : Deriv (eqF (ap1 (C pi (compose1U s gArg) gKont) c) (ap2 pi (ap1 s a) K))
      eInner = ruleTrans eInner1
                 (ruleTrans (congL pi (ap1 gKont c) eSA)
                            (congR pi (ap1 s a) (gKont_ev fc a K)))
  in ruleTrans e1
       (ruleTrans (congL pi (ap1 (C pi (compose1U s gArg) gKont) c) eRT)
                  (congR pi (natCode tagRT) eInner))

evBody_o_value : (fc a K : Term) ->
  Deriv (eqF (ap1 evBody_o (cfgEV fc a K)) (cfgRT O K))
evBody_o_value fc a K =
  let c : Term
      c = cfgEV fc a K
      e1 = ax_C pi (constN tagRT) (C pi o gKont) c
      eRT = constN_eq tagRT c
      eInner1 = ax_C pi o gKont c
      eInner : Deriv (eqF (ap1 (C pi o gKont) c) (ap2 pi O K))
      eInner = ruleTrans eInner1
                 (ruleTrans (congL pi (ap1 gKont c) (ax_o c))
                            (congR pi O (gKont_ev fc a K)))
  in ruleTrans e1
       (ruleTrans (congL pi (ap1 (C pi o gKont) c) eRT)
                  (congR pi (natCode tagRT) eInner))

evBody_u_value : (fc a K : Term) ->
  Deriv (eqF (ap1 evBody_u (cfgEV fc a K)) (cfgRT a K))
evBody_u_value fc a K =
  let c : Term
      c = cfgEV fc a K
      e1 = ax_C pi (constN tagRT) (C pi gArg gKont) c
      eRT = constN_eq tagRT c
      eInner1 = ax_C pi gArg gKont c
      eInner : Deriv (eqF (ap1 (C pi gArg gKont) c) (ap2 pi a K))
      eInner = ruleTrans eInner1
                 (ruleTrans (congL pi (ap1 gKont c) (gArg_ev fc a K))
                            (congR pi a (gKont_ev fc a K)))
  in ruleTrans e1
       (ruleTrans (congL pi (ap1 (C pi gArg gKont) c) eRT)
                  (congR pi (natCode tagRT) eInner))

evBody_v_value : (fc a K : Term) ->
  Deriv (eqF (ap1 evBody_v (cfgEV fc a K)) (cfgRT (ap1 Snd a) K))
evBody_v_value fc a K =
  let c : Term
      c = cfgEV fc a K
      e1 = ax_C pi (constN tagRT) (C pi (compose1U Snd gArg) gKont) c
      eRT = constN_eq tagRT c
      eInner1 = ax_C pi (compose1U Snd gArg) gKont c
      eSnd : Deriv (eqF (ap1 (compose1U Snd gArg) c) (ap1 Snd a))
      eSnd = ruleTrans (compose1U_eq Snd gArg c) (cong1 Snd (gArg_ev fc a K))
      eInner : Deriv (eqF (ap1 (C pi (compose1U Snd gArg) gKont) c) (ap2 pi (ap1 Snd a) K))
      eInner = ruleTrans eInner1
                 (ruleTrans (congL pi (ap1 gKont c) eSnd)
                            (congR pi (ap1 Snd a) (gKont_ev fc a K)))
  in ruleTrans e1
       (ruleTrans (congL pi (ap1 (C pi (compose1U Snd gArg) gKont) c) eRT)
                  (congR pi (natCode tagRT) eInner))

------------------------------------------------------------------------
-- EV leaf transition lemmas.

stepU_at_evS : (a K : Term) ->
  Deriv (eqF (ap1 stepU (cfgEV (mcode1 s) a K)) (cfgRT (ap1 s a) K))
stepU_at_evS a K =
  let c : Term
      c = cfgEV (mcode1 s) a K
      m1 = fireT evBranch modeRT isEV c (isEV_cfgEV (mcode1 s) a K)
      t1 = fireT evBody_s evCascO (testTag tag_s) c
             (ttFireAt tag_s (mcode1 s) a K head_mcode1_s)
  in ruleTrans m1 (ruleTrans t1 (evBody_s_value (mcode1 s) a K))

stepU_at_evO : (a K : Term) ->
  Deriv (eqF (ap1 stepU (cfgEV (mcode1 o) a K)) (cfgRT O K))
stepU_at_evO a K =
  let c : Term
      c = cfgEV (mcode1 o) a K
      m1 = fireT evBranch modeRT isEV c (isEV_cfgEV (mcode1 o) a K)
      sk = fireF evBody_s evCascO (testTag tag_s) c
             (ttSkipAt tag_s tag_o (mcode1 o) a K head_mcode1_o (decideNatNeq tag_o tag_s (\ ())))
      t1 = fireT evBody_o evCascU (testTag tag_o) c
             (ttFireAt tag_o (mcode1 o) a K head_mcode1_o)
  in ruleTrans m1 (ruleTrans sk (ruleTrans t1 (evBody_o_value (mcode1 o) a K)))

stepU_at_evU : (a K : Term) ->
  Deriv (eqF (ap1 stepU (cfgEV (mcode1 u) a K)) (cfgRT a K))
stepU_at_evU a K =
  let c : Term
      c = cfgEV (mcode1 u) a K
      m1 = fireT evBranch modeRT isEV c (isEV_cfgEV (mcode1 u) a K)
      sk_s = fireF evBody_s evCascO (testTag tag_s) c
               (ttSkipAt tag_s tag_u (mcode1 u) a K head_mcode1_u (decideNatNeq tag_u tag_s (\ ())))
      sk_o = fireF evBody_o evCascU (testTag tag_o) c
               (ttSkipAt tag_o tag_u (mcode1 u) a K head_mcode1_u (decideNatNeq tag_u tag_o (\ ())))
      t1 = fireT evBody_u evCascV (testTag tag_u) c
             (ttFireAt tag_u (mcode1 u) a K head_mcode1_u)
  in ruleTrans m1 (ruleTrans sk_s (ruleTrans sk_o (ruleTrans t1 (evBody_u_value (mcode1 u) a K))))

stepU_at_evV : (arg K : Term) ->
  Deriv (eqF (ap1 stepU (cfgEV (mcode2 v) arg K)) (cfgRT (ap1 Snd arg) K))
stepU_at_evV arg K =
  let c : Term
      c = cfgEV (mcode2 v) arg K
      m1 = fireT evBranch modeRT isEV c (isEV_cfgEV (mcode2 v) arg K)
      sk_s = fireF evBody_s evCascO (testTag tag_s) c
               (ttSkipAt tag_s tag_v (mcode2 v) arg K head_mcode2_v (decideNatNeq tag_v tag_s (\ ())))
      sk_o = fireF evBody_o evCascU (testTag tag_o) c
               (ttSkipAt tag_o tag_v (mcode2 v) arg K head_mcode2_v (decideNatNeq tag_v tag_o (\ ())))
      sk_u = fireF evBody_u evCascV (testTag tag_u) c
               (ttSkipAt tag_u tag_v (mcode2 v) arg K head_mcode2_v (decideNatNeq tag_v tag_u (\ ())))
      t1 = fireT evBody_v evCascC (testTag tag_v) c
             (ttFireAt tag_v (mcode2 v) arg K head_mcode2_v)
  in ruleTrans m1 (ruleTrans sk_s (ruleTrans sk_o (ruleTrans sk_u
       (ruleTrans t1 (evBody_v_value (mcode2 v) arg K)))))

------------------------------------------------------------------------
-- EV payload / arg sub-accessor value lemmas (generic in fc).

gPayG_ev : (fc a K : Term) ->
  Deriv (eqF (ap1 gPayG (cfgEV fc a K)) (ap1 Fst (ap1 Snd fc)))
gPayG_ev fc a K =
  ruleTrans (compose1U_eq Fst gPayload (cfgEV fc a K)) (cong1 Fst (gPayload_ev fc a K))

gPaySub_ev : (fc a K : Term) ->
  Deriv (eqF (ap1 gPaySub (cfgEV fc a K)) (ap1 Snd (ap1 Snd fc)))
gPaySub_ev fc a K =
  ruleTrans (compose1U_eq Snd gPayload (cfgEV fc a K)) (cong1 Snd (gPayload_ev fc a K))

gPayH1_ev : (fc a K : Term) ->
  Deriv (eqF (ap1 gPayH1 (cfgEV fc a K)) (ap1 Fst (ap1 Snd (ap1 Snd fc))))
gPayH1_ev fc a K =
  ruleTrans (compose1U_eq Fst gPaySub (cfgEV fc a K)) (cong1 Fst (gPaySub_ev fc a K))

gPayH2_ev : (fc a K : Term) ->
  Deriv (eqF (ap1 gPayH2 (cfgEV fc a K)) (ap1 Snd (ap1 Snd (ap1 Snd fc))))
gPayH2_ev fc a K =
  ruleTrans (compose1U_eq Snd gPaySub (cfgEV fc a K)) (cong1 Snd (gPaySub_ev fc a K))

gArgX_ev : (fc a K : Term) -> Deriv (eqF (ap1 gArgX (cfgEV fc a K)) (ap1 Fst a))
gArgX_ev fc a K =
  ruleTrans (compose1U_eq Fst gArg (cfgEV fc a K)) (cong1 Fst (gArg_ev fc a K))

gArgM_ev : (fc a K : Term) -> Deriv (eqF (ap1 gArgM (cfgEV fc a K)) (ap1 Snd a))
gArgM_ev fc a K =
  ruleTrans (compose1U_eq Snd gArg (cfgEV fc a K)) (cong1 Snd (gArg_ev fc a K))

------------------------------------------------------------------------
-- EV C branch-body value (generic in fc, given the payload values).

evBody_C_value : (fc a K gc h1c h2c : Term) ->
  Deriv (eqF (ap1 gPayG  (cfgEV fc a K)) gc)  ->
  Deriv (eqF (ap1 gPayH1 (cfgEV fc a K)) h1c) ->
  Deriv (eqF (ap1 gPayH2 (cfgEV fc a K)) h2c) ->
  Deriv (eqF (ap1 evBody_C (cfgEV fc a K))
              (cfgEV h1c a (kons (frmC1 gc h2c a) K)))
evBody_C_value fc a K gc h1c h2c hG hH1 hH2 =
  let c : Term
      c = cfgEV fc a K
      eA : Deriv (eqF (ap1 gArg c) a)
      eA = gArg_ev fc a K
      eK : Deriv (eqF (ap1 gKont c) K)
      eK = gKont_ev fc a K
      -- left:  (C pi gPayH1 gArg) c = pi h1c a
      eL : Deriv (eqF (ap1 (C pi gPayH1 gArg) c) (ap2 pi h1c a))
      eL = ruleTrans (ax_C pi gPayH1 gArg c)
             (ruleTrans (congL pi (ap1 gArg c) hH1) (congR pi h1c eA))
      -- mkFrmC1 c = frmC1 gc h2c a
      eH2a : Deriv (eqF (ap1 (C pi gPayH2 gArg) c) (ap2 pi h2c a))
      eH2a = ruleTrans (ax_C pi gPayH2 gArg c)
               (ruleTrans (congL pi (ap1 gArg c) hH2) (congR pi h2c eA))
      eSub : Deriv (eqF (ap1 (C pi gPayG (C pi gPayH2 gArg)) c) (ap2 pi gc (ap2 pi h2c a)))
      eSub = ruleTrans (ax_C pi gPayG (C pi gPayH2 gArg) c)
               (ruleTrans (congL pi (ap1 (C pi gPayH2 gArg) c) hG) (congR pi gc eH2a))
      eFrm : Deriv (eqF (ap1 mkFrmC1 c) (frmC1 gc h2c a))
      eFrm = ruleTrans (ax_C pi (constN tagC1) (C pi gPayG (C pi gPayH2 gArg)) c)
               (ruleTrans (congL pi (ap1 (C pi gPayG (C pi gPayH2 gArg)) c) (constN_eq tagC1 c))
                          (congR pi (natCode tagC1) eSub))
      -- konsF mkFrmC1 gKont c = kons (frmC1 gc h2c a) K
      eInner2 : Deriv (eqF (ap1 (C pi mkFrmC1 gKont) c) (ap2 pi (frmC1 gc h2c a) K))
      eInner2 = ruleTrans (ax_C pi mkFrmC1 gKont c)
                  (ruleTrans (congL pi (ap1 gKont c) eFrm) (congR pi (frmC1 gc h2c a) eK))
      eKons : Deriv (eqF (ap1 (konsF mkFrmC1 gKont) c) (kons (frmC1 gc h2c a) K))
      eKons = ruleTrans (ax_C pi (constN 1) (C pi mkFrmC1 gKont) c)
                (ruleTrans (congL pi (ap1 (C pi mkFrmC1 gKont) c) (constN_eq 1 c))
                           (congR pi (natCode 1) eInner2))
      -- inner body
      eBody : Deriv (eqF (ap1 (C pi (C pi gPayH1 gArg) (konsF mkFrmC1 gKont)) c)
                         (ap2 pi (ap2 pi h1c a) (kons (frmC1 gc h2c a) K)))
      eBody = ruleTrans (ax_C pi (C pi gPayH1 gArg) (konsF mkFrmC1 gKont) c)
                (ruleTrans (congL pi (ap1 (konsF mkFrmC1 gKont) c) eL)
                           (congR pi (ap2 pi h1c a) eKons))
      e1 : Deriv (eqF (ap1 evBody_C c)
                      (ap2 pi (ap1 (constN tagEV) c)
                              (ap1 (C pi (C pi gPayH1 gArg) (konsF mkFrmC1 gKont)) c)))
      e1 = ax_C pi (constN tagEV) (C pi (C pi gPayH1 gArg) (konsF mkFrmC1 gKont)) c
  in ruleTrans e1
       (ruleTrans (congL pi (ap1 (C pi (C pi gPayH1 gArg) (konsF mkFrmC1 gKont)) c)
                            (constN_eq tagEV c))
                  (congR pi (natCode tagEV) eBody))

------------------------------------------------------------------------
-- Concrete C-code payload accessor values.

snd_snd_mcode1_C : (g : Fun2) (h1 h2 : Fun1) ->
  Deriv (eqF (ap1 Snd (ap1 Snd (mcode1 (C g h1 h2)))) (ap2 pi (mcode1 h1) (mcode1 h2)))
snd_snd_mcode1_C g h1 h2 =
  ruleTrans (cong1 Snd (payload_mcode1_C g h1 h2))
            (axSnd (mcode2 g) (ap2 pi (mcode1 h1) (mcode1 h2)))

gPayG_evC : (g : Fun2) (h1 h2 : Fun1) (a K : Term) ->
  Deriv (eqF (ap1 gPayG (cfgEV (mcode1 (C g h1 h2)) a K)) (mcode2 g))
gPayG_evC g h1 h2 a K =
  ruleTrans (gPayG_ev (mcode1 (C g h1 h2)) a K)
    (ruleTrans (cong1 Fst (payload_mcode1_C g h1 h2))
               (axFst (mcode2 g) (ap2 pi (mcode1 h1) (mcode1 h2))))

gPayH1_evC : (g : Fun2) (h1 h2 : Fun1) (a K : Term) ->
  Deriv (eqF (ap1 gPayH1 (cfgEV (mcode1 (C g h1 h2)) a K)) (mcode1 h1))
gPayH1_evC g h1 h2 a K =
  ruleTrans (gPayH1_ev (mcode1 (C g h1 h2)) a K)
    (ruleTrans (cong1 Fst (snd_snd_mcode1_C g h1 h2)) (axFst (mcode1 h1) (mcode1 h2)))

gPayH2_evC : (g : Fun2) (h1 h2 : Fun1) (a K : Term) ->
  Deriv (eqF (ap1 gPayH2 (cfgEV (mcode1 (C g h1 h2)) a K)) (mcode1 h2))
gPayH2_evC g h1 h2 a K =
  ruleTrans (gPayH2_ev (mcode1 (C g h1 h2)) a K)
    (ruleTrans (cong1 Snd (snd_snd_mcode1_C g h1 h2)) (axSnd (mcode1 h1) (mcode1 h2)))

------------------------------------------------------------------------
-- EV C transition.

stepU_at_evC : (g : Fun2) (h1 h2 : Fun1) (a K : Term) ->
  Deriv (eqF (ap1 stepU (cfgEV (mcode1 (C g h1 h2)) a K))
              (cfgEV (mcode1 h1) a (kons (frmC1 (mcode2 g) (mcode1 h2) a) K)))
stepU_at_evC g h1 h2 a K =
  let fc : Term
      fc = mcode1 (C g h1 h2)
      c : Term
      c = cfgEV fc a K
      hd : Deriv (eqF (ap1 Fst fc) (natCode tag_C))
      hd = head_mcode1_C g h1 h2
      m1 = fireT evBranch modeRT isEV c (isEV_cfgEV fc a K)
      sk_s = fireF evBody_s evCascO (testTag tag_s) c
               (ttSkipAt tag_s tag_C fc a K hd (decideNatNeq tag_C tag_s (\ ())))
      sk_o = fireF evBody_o evCascU (testTag tag_o) c
               (ttSkipAt tag_o tag_C fc a K hd (decideNatNeq tag_C tag_o (\ ())))
      sk_u = fireF evBody_u evCascV (testTag tag_u) c
               (ttSkipAt tag_u tag_C fc a K hd (decideNatNeq tag_C tag_u (\ ())))
      sk_v = fireF evBody_v evCascC (testTag tag_v) c
               (ttSkipAt tag_v tag_C fc a K hd (decideNatNeq tag_C tag_v (\ ())))
      t_C = fireT evBody_C evCascR (testTag tag_C) c (ttFireAt tag_C fc a K hd)
      val = evBody_C_value fc a K (mcode2 g) (mcode1 h1) (mcode1 h2)
              (gPayG_evC g h1 h2 a K) (gPayH1_evC g h1 h2 a K) (gPayH2_evC g h1 h2 a K)
  in ruleTrans m1 (ruleTrans sk_s (ruleTrans sk_o (ruleTrans sk_u
       (ruleTrans sk_v (ruleTrans t_C val)))))

-- Code-level C-dispatch: same transition as stepU_at_evC but for ARBITRARY
-- child codes -- the first child  h1c  need NOT be  mcode1  of a pure Fun1 (it
-- may be a mu-program code  mcodeMu ...).  The C-branch keys only on the head
-- tag  tag_C  and on the generic payload accessors (gPayG/gPayH1/gPayH2_ev),
-- so the proof is stepU_at_evC verbatim with  hd  and the three payload
-- extractions redone for the general code  pi tag_C (pi gc (pi h1c h2c)) .
stepU_at_evC_code : (gc h1c h2c a K : Term) ->
  Deriv (eqF (ap1 stepU (cfgEV (ap2 pi (natCode tag_C) (ap2 pi gc (ap2 pi h1c h2c))) a K))
              (cfgEV h1c a (kons (frmC1 gc h2c a) K)))
stepU_at_evC_code gc h1c h2c a K =
  let payload : Term
      payload = ap2 pi gc (ap2 pi h1c h2c)
      fc : Term
      fc = ap2 pi (natCode tag_C) payload
      c : Term
      c = cfgEV fc a K
      hd : Deriv (eqF (ap1 Fst fc) (natCode tag_C))
      hd = axFst (natCode tag_C) payload
      m1 = fireT evBranch modeRT isEV c (isEV_cfgEV fc a K)
      sk_s = fireF evBody_s evCascO (testTag tag_s) c
               (ttSkipAt tag_s tag_C fc a K hd (decideNatNeq tag_C tag_s (\ ())))
      sk_o = fireF evBody_o evCascU (testTag tag_o) c
               (ttSkipAt tag_o tag_C fc a K hd (decideNatNeq tag_C tag_o (\ ())))
      sk_u = fireF evBody_u evCascV (testTag tag_u) c
               (ttSkipAt tag_u tag_C fc a K hd (decideNatNeq tag_C tag_u (\ ())))
      sk_v = fireF evBody_v evCascC (testTag tag_v) c
               (ttSkipAt tag_v tag_C fc a K hd (decideNatNeq tag_C tag_v (\ ())))
      t_C = fireT evBody_C evCascR (testTag tag_C) c (ttFireAt tag_C fc a K hd)
      eG : Deriv (eqF (ap1 gPayG c) gc)
      eG = ruleTrans (gPayG_ev fc a K)
             (ruleTrans (cong1 Fst (axSnd (natCode tag_C) payload))
                        (axFst gc (ap2 pi h1c h2c)))
      eH1 : Deriv (eqF (ap1 gPayH1 c) h1c)
      eH1 = ruleTrans (gPayH1_ev fc a K)
              (ruleTrans (cong1 Fst (cong1 Snd (axSnd (natCode tag_C) payload)))
                (ruleTrans (cong1 Fst (axSnd gc (ap2 pi h1c h2c)))
                           (axFst h1c h2c)))
      eH2 : Deriv (eqF (ap1 gPayH2 c) h2c)
      eH2 = ruleTrans (gPayH2_ev fc a K)
              (ruleTrans (cong1 Snd (cong1 Snd (axSnd (natCode tag_C) payload)))
                (ruleTrans (cong1 Snd (axSnd gc (ap2 pi h1c h2c)))
                           (axSnd h1c h2c)))
      val = evBody_C_value fc a K gc h1c h2c eG eH1 eH2
  in ruleTrans m1 (ruleTrans sk_s (ruleTrans sk_o (ruleTrans sk_u
       (ruleTrans sk_v (ruleTrans t_C val)))))

------------------------------------------------------------------------
-- Generalized true-firing: flag = s n for ANY n (condFork fires Fst).

fireT_s : (trueB falseB flag : Fun1) (input n : Term) ->
        Deriv (eqF (ap1 flag input) (ap1 s n)) ->
        Deriv (eqF (ap1 (fork trueB falseB flag) input) (ap1 trueB input))
fireT_s trueB falseB flag input n flagT =
  let pairT : Term
      pairT = ap1 (C pi trueB falseB) input
      e1 = ax_C condFork (C pi trueB falseB) flag input
      e2 = congR condFork pairT flagT
      e3 = condFork_true_nc pairT n
      e4 = ax_C pi trueB falseB input
      e5 = axFst (ap1 trueB input) (ap1 falseB input)
  in ruleTrans e1 (ruleTrans e2 (ruleTrans e3 (ruleTrans (cong1 Fst e4) e5)))

-- config arg-rewrite helper.
cfgArgRw : (gc Y Y' K : Term) ->
  Deriv (eqF Y Y') -> Deriv (eqF (cfgEV gc Y K) (cfgEV gc Y' K))
cfgArgRw gc Y Y' K e = congR pi (natCode tagEV) (congL pi K (congR pi gc e))

------------------------------------------------------------------------
-- EV mu.

gPayload_evMu : (gc a K : Term) ->
  Deriv (eqF (ap1 gPayload (cfgEV (mcodeMu gc) a K)) gc)
gPayload_evMu gc a K =
  ruleTrans (gPayload_ev (mcodeMu gc) a K) (payload_mcodeMu gc)

evBody_mu_value : (fc a K gc : Term) ->
  Deriv (eqF (ap1 gPayload (cfgEV fc a K)) gc) ->
  Deriv (eqF (ap1 evBody_mu (cfgEV fc a K)) (cfgEV gc O (kons (frmM gc O) K)))
evBody_mu_value fc a K gc hG =
  let c : Term
      c = cfgEV fc a K
      eK : Deriv (eqF (ap1 gKont c) K)
      eK = gKont_ev fc a K
      -- (C pi gPayload o) c = pi gc O
      eGcO : Deriv (eqF (ap1 (C pi gPayload o) c) (ap2 pi gc O))
      eGcO = ruleTrans (ax_C pi gPayload o c)
               (ruleTrans (congL pi (ap1 o c) hG) (congR pi gc (ax_o c)))
      eFrm : Deriv (eqF (ap1 mkFrmM0 c) (frmM gc O))
      eFrm = ruleTrans (ax_C pi (constN tagM) (C pi gPayload o) c)
               (ruleTrans (congL pi (ap1 (C pi gPayload o) c) (constN_eq tagM c))
                          (congR pi (natCode tagM) eGcO))
      eInner2 : Deriv (eqF (ap1 (C pi mkFrmM0 gKont) c) (ap2 pi (frmM gc O) K))
      eInner2 = ruleTrans (ax_C pi mkFrmM0 gKont c)
                  (ruleTrans (congL pi (ap1 gKont c) eFrm) (congR pi (frmM gc O) eK))
      eKons : Deriv (eqF (ap1 (konsF mkFrmM0 gKont) c) (kons (frmM gc O) K))
      eKons = ruleTrans (ax_C pi (constN 1) (C pi mkFrmM0 gKont) c)
                (ruleTrans (congL pi (ap1 (C pi mkFrmM0 gKont) c) (constN_eq 1 c))
                           (congR pi (natCode 1) eInner2))
      eBody : Deriv (eqF (ap1 (C pi (C pi gPayload o) (konsF mkFrmM0 gKont)) c)
                         (ap2 pi (ap2 pi gc O) (kons (frmM gc O) K)))
      eBody = ruleTrans (ax_C pi (C pi gPayload o) (konsF mkFrmM0 gKont) c)
                (ruleTrans (congL pi (ap1 (konsF mkFrmM0 gKont) c) eGcO)
                           (congR pi (ap2 pi gc O) eKons))
      e1 = ax_C pi (constN tagEV) (C pi (C pi gPayload o) (konsF mkFrmM0 gKont)) c
  in ruleTrans e1
       (ruleTrans (congL pi (ap1 (C pi (C pi gPayload o) (konsF mkFrmM0 gKont)) c)
                            (constN_eq tagEV c))
                  (congR pi (natCode tagEV) eBody))

stepU_at_evMu : (gc a K : Term) ->
  Deriv (eqF (ap1 stepU (cfgEV (mcodeMu gc) a K)) (cfgEV gc O (kons (frmM gc O) K)))
stepU_at_evMu gc a K =
  let fc : Term
      fc = mcodeMu gc
      c : Term
      c = cfgEV fc a K
      hd : Deriv (eqF (ap1 Fst fc) (natCode tag_mu))
      hd = head_mcodeMu gc
      m1 = fireT evBranch modeRT isEV c (isEV_cfgEV fc a K)
      sk_s = fireF evBody_s evCascO (testTag tag_s) c
               (ttSkipAt tag_s tag_mu fc a K hd (decideNatNeq tag_mu tag_s (\ ())))
      sk_o = fireF evBody_o evCascU (testTag tag_o) c
               (ttSkipAt tag_o tag_mu fc a K hd (decideNatNeq tag_mu tag_o (\ ())))
      sk_u = fireF evBody_u evCascV (testTag tag_u) c
               (ttSkipAt tag_u tag_mu fc a K hd (decideNatNeq tag_mu tag_u (\ ())))
      sk_v = fireF evBody_v evCascC (testTag tag_v) c
               (ttSkipAt tag_v tag_mu fc a K hd (decideNatNeq tag_mu tag_v (\ ())))
      sk_C = fireF evBody_C evCascR (testTag tag_C) c
               (ttSkipAt tag_C tag_mu fc a K hd (decideNatNeq tag_mu tag_C (\ ())))
      sk_R = fireF evBody_R evBody_mu (testTag tag_R) c
               (ttSkipAt tag_R tag_mu fc a K hd (decideNatNeq tag_mu tag_R (\ ())))
      val = evBody_mu_value fc a K gc (gPayload_evMu gc a K)
  in ruleTrans m1 (ruleTrans sk_s (ruleTrans sk_o (ruleTrans sk_u (ruleTrans sk_v
       (ruleTrans sk_C (ruleTrans sk_R val))))))

------------------------------------------------------------------------
-- Concrete R-code payload accessor values.

snd_snd_mcode2_R : (g : Fun1) (h1 h2 : Fun2) ->
  Deriv (eqF (ap1 Snd (ap1 Snd (mcode2 (R g h1 h2)))) (ap2 pi (mcode2 h1) (mcode2 h2)))
snd_snd_mcode2_R g h1 h2 =
  ruleTrans (cong1 Snd (payload_mcode2_R g h1 h2))
            (axSnd (mcode1 g) (ap2 pi (mcode2 h1) (mcode2 h2)))

gPayG_evR : (g : Fun1) (h1 h2 : Fun2) (a K : Term) ->
  Deriv (eqF (ap1 gPayG (cfgEV (mcode2 (R g h1 h2)) a K)) (mcode1 g))
gPayG_evR g h1 h2 a K =
  ruleTrans (gPayG_ev (mcode2 (R g h1 h2)) a K)
    (ruleTrans (cong1 Fst (payload_mcode2_R g h1 h2))
               (axFst (mcode1 g) (ap2 pi (mcode2 h1) (mcode2 h2))))

gPayH1_evR : (g : Fun1) (h1 h2 : Fun2) (a K : Term) ->
  Deriv (eqF (ap1 gPayH1 (cfgEV (mcode2 (R g h1 h2)) a K)) (mcode2 h1))
gPayH1_evR g h1 h2 a K =
  ruleTrans (gPayH1_ev (mcode2 (R g h1 h2)) a K)
    (ruleTrans (cong1 Fst (snd_snd_mcode2_R g h1 h2)) (axFst (mcode2 h1) (mcode2 h2)))

gPayH2_evR : (g : Fun1) (h1 h2 : Fun2) (a K : Term) ->
  Deriv (eqF (ap1 gPayH2 (cfgEV (mcode2 (R g h1 h2)) a K)) (mcode2 h2))
gPayH2_evR g h1 h2 a K =
  ruleTrans (gPayH2_ev (mcode2 (R g h1 h2)) a K)
    (ruleTrans (cong1 Snd (snd_snd_mcode2_R g h1 h2)) (axSnd (mcode2 h1) (mcode2 h2)))

-- predecessor of a successor.
pred_s : (m : Term) -> Deriv (eqF (ap1 predecessor (ap1 s m)) m)
pred_s m = ruleInst 0 m T_p_S_v0

------------------------------------------------------------------------
-- EV R base branch-body value (generic in fc, given gPayG = gc).

evBody_Rbase_value : (fc a K gc : Term) ->
  Deriv (eqF (ap1 gPayG (cfgEV fc a K)) gc) ->
  Deriv (eqF (ap1 evBody_Rbase (cfgEV fc a K)) (cfgEV gc (ap1 Fst a) K))
evBody_Rbase_value fc a K gc hG =
  let c : Term
      c = cfgEV fc a K
      eGX : Deriv (eqF (ap1 (C pi gPayG gArgX) c) (ap2 pi gc (ap1 Fst a)))
      eGX = ruleTrans (ax_C pi gPayG gArgX c)
              (ruleTrans (congL pi (ap1 gArgX c) hG) (congR pi gc (gArgX_ev fc a K)))
      eBody : Deriv (eqF (ap1 (C pi (C pi gPayG gArgX) gKont) c)
                         (ap2 pi (ap2 pi gc (ap1 Fst a)) K))
      eBody = ruleTrans (ax_C pi (C pi gPayG gArgX) gKont c)
                (ruleTrans (congL pi (ap1 gKont c) eGX)
                           (congR pi (ap2 pi gc (ap1 Fst a)) (gKont_ev fc a K)))
      e1 = ax_C pi (constN tagEV) (C pi (C pi gPayG gArgX) gKont) c
  in ruleTrans e1
       (ruleTrans (congL pi (ap1 (C pi (C pi gPayG gArgX) gKont) c) (constN_eq tagEV c))
                  (congR pi (natCode tagEV) eBody))

------------------------------------------------------------------------
-- EV R step branch-body value (generic; gFc = fc by gFc_ev).

evBody_Rstep_value : (fc a K h1c h2c x m' : Term) ->
  Deriv (eqF (ap1 gPayH1 (cfgEV fc a K)) h1c) ->
  Deriv (eqF (ap1 gPayH2 (cfgEV fc a K)) h2c) ->
  Deriv (eqF (ap1 gArgX  (cfgEV fc a K)) x)   ->
  Deriv (eqF (ap1 gMpred (cfgEV fc a K)) m')  ->
  Deriv (eqF (ap1 evBody_Rstep (cfgEV fc a K))
              (cfgEV h2c (ap2 pi x m') (kons (frmR1 fc h1c x m') K)))
evBody_Rstep_value fc a K h1c h2c x m' hH1 hH2 hX hMp =
  let c : Term
      c = cfgEV fc a K
      eXM : Deriv (eqF (ap1 (C pi gArgX gMpred) c) (ap2 pi x m'))
      eXM = ruleTrans (ax_C pi gArgX gMpred c)
              (ruleTrans (congL pi (ap1 gMpred c) hX) (congR pi x hMp))
      eLeft : Deriv (eqF (ap1 (C pi gPayH2 (C pi gArgX gMpred)) c)
                         (ap2 pi h2c (ap2 pi x m')))
      eLeft = ruleTrans (ax_C pi gPayH2 (C pi gArgX gMpred) c)
                (ruleTrans (congL pi (ap1 (C pi gArgX gMpred) c) hH2)
                           (congR pi h2c eXM))
      eFcsub : Deriv (eqF (ap1 (C pi gPayH1 (C pi gArgX gMpred)) c)
                          (ap2 pi h1c (ap2 pi x m')))
      eFcsub = ruleTrans (ax_C pi gPayH1 (C pi gArgX gMpred) c)
                 (ruleTrans (congL pi (ap1 (C pi gArgX gMpred) c) hH1)
                            (congR pi h1c eXM))
      eFcsub2 : Deriv (eqF (ap1 (C pi gFc (C pi gPayH1 (C pi gArgX gMpred))) c)
                           (ap2 pi fc (ap2 pi h1c (ap2 pi x m'))))
      eFcsub2 = ruleTrans (ax_C pi gFc (C pi gPayH1 (C pi gArgX gMpred)) c)
                  (ruleTrans (congL pi (ap1 (C pi gPayH1 (C pi gArgX gMpred)) c)
                                       (gFc_ev fc a K))
                             (congR pi fc eFcsub))
      eFrm : Deriv (eqF (ap1 mkFrmR1 c) (frmR1 fc h1c x m'))
      eFrm = ruleTrans (ax_C pi (constN tagR1)
                              (C pi gFc (C pi gPayH1 (C pi gArgX gMpred))) c)
               (ruleTrans (congL pi (ap1 (C pi gFc (C pi gPayH1 (C pi gArgX gMpred))) c)
                                    (constN_eq tagR1 c))
                          (congR pi (natCode tagR1) eFcsub2))
      eInner2 : Deriv (eqF (ap1 (C pi mkFrmR1 gKont) c) (ap2 pi (frmR1 fc h1c x m') K))
      eInner2 = ruleTrans (ax_C pi mkFrmR1 gKont c)
                  (ruleTrans (congL pi (ap1 gKont c) eFrm)
                             (congR pi (frmR1 fc h1c x m') (gKont_ev fc a K)))
      eKons : Deriv (eqF (ap1 (konsF mkFrmR1 gKont) c) (kons (frmR1 fc h1c x m') K))
      eKons = ruleTrans (ax_C pi (constN 1) (C pi mkFrmR1 gKont) c)
                (ruleTrans (congL pi (ap1 (C pi mkFrmR1 gKont) c) (constN_eq 1 c))
                           (congR pi (natCode 1) eInner2))
      eBody : Deriv (eqF (ap1 (C pi (C pi gPayH2 (C pi gArgX gMpred)) (konsF mkFrmR1 gKont)) c)
                         (ap2 pi (ap2 pi h2c (ap2 pi x m')) (kons (frmR1 fc h1c x m') K)))
      eBody = ruleTrans (ax_C pi (C pi gPayH2 (C pi gArgX gMpred)) (konsF mkFrmR1 gKont) c)
                (ruleTrans (congL pi (ap1 (konsF mkFrmR1 gKont) c) eLeft)
                           (congR pi (ap2 pi h2c (ap2 pi x m')) eKons))
      e1 = ax_C pi (constN tagEV)
                   (C pi (C pi gPayH2 (C pi gArgX gMpred)) (konsF mkFrmR1 gKont)) c
  in ruleTrans e1
       (ruleTrans (congL pi (ap1 (C pi (C pi gPayH2 (C pi gArgX gMpred))
                                       (konsF mkFrmR1 gKont)) c)
                            (constN_eq tagEV c))
                  (congR pi (natCode tagEV) eBody))

------------------------------------------------------------------------
-- EV R transitions.

stepU_at_evRbase : (g : Fun1) (h1 h2 : Fun2) (x K : Term) ->
  Deriv (eqF (ap1 stepU (cfgEV (mcode2 (R g h1 h2)) (ap2 pi x O) K))
              (cfgEV (mcode1 g) x K))
stepU_at_evRbase g h1 h2 x K =
  let fc : Term
      fc = mcode2 (R g h1 h2)
      arg : Term
      arg = ap2 pi x O
      c : Term
      c = cfgEV fc arg K
      hd : Deriv (eqF (ap1 Fst fc) (natCode tag_R))
      hd = head_mcode2_R g h1 h2
      m1 = fireT evBranch modeRT isEV c (isEV_cfgEV fc arg K)
      sk_s = fireF evBody_s evCascO (testTag tag_s) c
               (ttSkipAt tag_s tag_R fc arg K hd (decideNatNeq tag_R tag_s (\ ())))
      sk_o = fireF evBody_o evCascU (testTag tag_o) c
               (ttSkipAt tag_o tag_R fc arg K hd (decideNatNeq tag_R tag_o (\ ())))
      sk_u = fireF evBody_u evCascV (testTag tag_u) c
               (ttSkipAt tag_u tag_R fc arg K hd (decideNatNeq tag_R tag_u (\ ())))
      sk_v = fireF evBody_v evCascC (testTag tag_v) c
               (ttSkipAt tag_v tag_R fc arg K hd (decideNatNeq tag_R tag_v (\ ())))
      sk_C = fireF evBody_C evCascR (testTag tag_C) c
               (ttSkipAt tag_C tag_R fc arg K hd (decideNatNeq tag_R tag_C (\ ())))
      t_R = fireT evBody_R evBody_mu (testTag tag_R) c (ttFireAt tag_R fc arg K hd)
      gArgM_O : Deriv (eqF (ap1 gArgM c) O)
      gArgM_O = ruleTrans (gArgM_ev fc arg K) (axSnd x O)
      r_base = fireF evBody_Rstep evBody_Rbase gArgM c gArgM_O
      val = evBody_Rbase_value fc arg K (mcode1 g) (gPayG_evR g h1 h2 arg K)
      adj : Deriv (eqF (cfgEV (mcode1 g) (ap1 Fst arg) K) (cfgEV (mcode1 g) x K))
      adj = cfgArgRw (mcode1 g) (ap1 Fst arg) x K (axFst x O)
  in ruleTrans m1 (ruleTrans sk_s (ruleTrans sk_o (ruleTrans sk_u (ruleTrans sk_v
       (ruleTrans sk_C (ruleTrans t_R (ruleTrans r_base (ruleTrans val adj))))))))

stepU_at_evRstep : (g : Fun1) (h1 h2 : Fun2) (x m K : Term) ->
  Deriv (eqF (ap1 stepU (cfgEV (mcode2 (R g h1 h2)) (ap2 pi x (ap1 s m)) K))
              (cfgEV (mcode2 h2) (ap2 pi x m)
                     (kons (frmR1 (mcode2 (R g h1 h2)) (mcode2 h1) x m) K)))
stepU_at_evRstep g h1 h2 x m K =
  let fc : Term
      fc = mcode2 (R g h1 h2)
      arg : Term
      arg = ap2 pi x (ap1 s m)
      c : Term
      c = cfgEV fc arg K
      hd : Deriv (eqF (ap1 Fst fc) (natCode tag_R))
      hd = head_mcode2_R g h1 h2
      m1 = fireT evBranch modeRT isEV c (isEV_cfgEV fc arg K)
      sk_s = fireF evBody_s evCascO (testTag tag_s) c
               (ttSkipAt tag_s tag_R fc arg K hd (decideNatNeq tag_R tag_s (\ ())))
      sk_o = fireF evBody_o evCascU (testTag tag_o) c
               (ttSkipAt tag_o tag_R fc arg K hd (decideNatNeq tag_R tag_o (\ ())))
      sk_u = fireF evBody_u evCascV (testTag tag_u) c
               (ttSkipAt tag_u tag_R fc arg K hd (decideNatNeq tag_R tag_u (\ ())))
      sk_v = fireF evBody_v evCascC (testTag tag_v) c
               (ttSkipAt tag_v tag_R fc arg K hd (decideNatNeq tag_R tag_v (\ ())))
      sk_C = fireF evBody_C evCascR (testTag tag_C) c
               (ttSkipAt tag_C tag_R fc arg K hd (decideNatNeq tag_R tag_C (\ ())))
      t_R = fireT evBody_R evBody_mu (testTag tag_R) c (ttFireAt tag_R fc arg K hd)
      gArgM_sm : Deriv (eqF (ap1 gArgM c) (ap1 s m))
      gArgM_sm = ruleTrans (gArgM_ev fc arg K) (axSnd x (ap1 s m))
      r_step = fireT_s evBody_Rstep evBody_Rbase gArgM c m gArgM_sm
      hX : Deriv (eqF (ap1 gArgX c) x)
      hX = ruleTrans (gArgX_ev fc arg K) (axFst x (ap1 s m))
      hMp : Deriv (eqF (ap1 gMpred c) m)
      hMp = ruleTrans (compose1U_eq predecessor gArgM c)
              (ruleTrans (cong1 predecessor gArgM_sm) (pred_s m))
      val = evBody_Rstep_value fc arg K (mcode2 h1) (mcode2 h2) x m
              (gPayH1_evR g h1 h2 arg K) (gPayH2_evR g h1 h2 arg K) hX hMp
  in ruleTrans m1 (ruleTrans sk_s (ruleTrans sk_o (ruleTrans sk_u (ruleTrans sk_v
       (ruleTrans sk_C (ruleTrans t_R (ruleTrans r_step val)))))))

------------------------------------------------------------------------
-- Mode tests at cfgRT / cfgHALT.

isEV_cfgRT : (val K : Term) -> Deriv (eqF (ap1 isEV (cfgRT val K)) O)
isEV_cfgRT val K =
  let c : Term
      c = cfgRT val K
      e1 = ax_C natEqF Fst (constN tagEV) c
      e2 = congL natEqF (ap1 (constN tagEV) c) (mode_cfgRT val K)
      e3 = congR natEqF (natCode tagRT) (constN_eq tagEV c)
  in ruleTrans e1 (ruleTrans e2 (ruleTrans e3
       (natEqF_at_neq tagRT tagEV (decideNatNeq tagRT tagEV (\ ())))))

isRT_cfgRT : (val K : Term) -> Deriv (eqF (ap1 isRT (cfgRT val K)) (ap1 s O))
isRT_cfgRT val K =
  let c : Term
      c = cfgRT val K
      e1 = ax_C natEqF Fst (constN tagRT) c
      e2 = congL natEqF (ap1 (constN tagRT) c) (mode_cfgRT val K)
      e3 = congR natEqF (natCode tagRT) (constN_eq tagRT c)
  in ruleTrans e1 (ruleTrans e2 (ruleTrans e3 (natEq_eq tagRT)))

isEV_cfgHALT : (val : Term) -> Deriv (eqF (ap1 isEV (cfgHALT val)) O)
isEV_cfgHALT val =
  let c : Term
      c = cfgHALT val
      e1 = ax_C natEqF Fst (constN tagEV) c
      e2 = congL natEqF (ap1 (constN tagEV) c) (mode_cfgHALT val)
      e3 = congR natEqF (natCode tagHALT) (constN_eq tagEV c)
  in ruleTrans e1 (ruleTrans e2 (ruleTrans e3
       (natEqF_at_neq tagHALT tagEV (decideNatNeq tagHALT tagEV (\ ())))))

isRT_cfgHALT : (val : Term) -> Deriv (eqF (ap1 isRT (cfgHALT val)) O)
isRT_cfgHALT val =
  let c : Term
      c = cfgHALT val
      e1 = ax_C natEqF Fst (constN tagRT) c
      e2 = congL natEqF (ap1 (constN tagRT) c) (mode_cfgHALT val)
      e3 = congR natEqF (natCode tagHALT) (constN_eq tagRT c)
  in ruleTrans e1 (ruleTrans e2 (ruleTrans e3
       (natEqF_at_neq tagHALT tagRT (decideNatNeq tagHALT tagRT (\ ())))))

------------------------------------------------------------------------
-- RT accessor-value lemmas.

rVal_ev : (val K : Term) -> Deriv (eqF (ap1 rVal (cfgRT val K)) val)
rVal_ev val K =
  ruleTrans (compose1U_eq Fst Snd (cfgRT val K))
    (ruleTrans (cong1 Fst (body_cfgRT val K)) (rt_val val K))

rKont_ev : (val K : Term) -> Deriv (eqF (ap1 rKont (cfgRT val K)) K)
rKont_ev val K =
  ruleTrans (compose1U_eq Snd Snd (cfgRT val K))
    (ruleTrans (cong1 Snd (body_cfgRT val K)) (rt_kont val K))

rHasFrame_ev : (val K : Term) -> Deriv (eqF (ap1 rHasFrame (cfgRT val K)) (ap1 Fst K))
rHasFrame_ev val K =
  ruleTrans (compose1U_eq Fst rKont (cfgRT val K)) (cong1 Fst (rKont_ev val K))

rHasFrame_empty : (val : Term) -> Deriv (eqF (ap1 rHasFrame (cfgRT val konEmpty)) O)
rHasFrame_empty val = ruleTrans (rHasFrame_ev val konEmpty) konsFlag_empty

rHasFrame_cons : (val frame rest : Term) ->
  Deriv (eqF (ap1 rHasFrame (cfgRT val (kons frame rest))) (ap1 s O))
rHasFrame_cons val frame rest =
  ruleTrans (rHasFrame_ev val (kons frame rest)) (konsFlag_cons frame rest)

------------------------------------------------------------------------
-- HALT fixpoint and RT-empty (halt) transitions.

stepU_at_halt : (val : Term) -> Deriv (eqF (ap1 stepU (cfgHALT val)) (cfgHALT val))
stepU_at_halt val =
  let c : Term
      c = cfgHALT val
      m1 = fireF evBranch modeRT isEV c (isEV_cfgHALT val)
      m2 = fireF rtBranch u isRT c (isRT_cfgHALT val)
  in ruleTrans m1 (ruleTrans m2 (ax_u c))

rtEmptyBranch_value : (val K : Term) ->
  Deriv (eqF (ap1 rtEmptyBranch (cfgRT val K)) (cfgHALT val))
rtEmptyBranch_value val K =
  let c : Term
      c = cfgRT val K
      e1 = ax_C pi (constN tagHALT) rVal c
  in ruleTrans e1
       (ruleTrans (congL pi (ap1 rVal c) (constN_eq tagHALT c))
                  (congR pi (natCode tagHALT) (rVal_ev val K)))

stepU_at_rtEmpty : (val : Term) ->
  Deriv (eqF (ap1 stepU (cfgRT val konEmpty)) (cfgHALT val))
stepU_at_rtEmpty val =
  let c : Term
      c = cfgRT val konEmpty
      m1 = fireF evBranch modeRT isEV c (isEV_cfgRT val konEmpty)
      m2 = fireT rtBranch u isRT c (isRT_cfgRT val konEmpty)
      m3 = fireF rtConsBranch rtEmptyBranch rHasFrame c (rHasFrame_empty val)
  in ruleTrans m1 (ruleTrans m2 (ruleTrans m3 (rtEmptyBranch_value val konEmpty)))

------------------------------------------------------------------------
-- RT frame / frame-data accessor lemmas (config = cfgRT val (kons frame rest)).

rConsPart_ev : (val K : Term) -> Deriv (eqF (ap1 rConsPart (cfgRT val K)) (ap1 Snd K))
rConsPart_ev val K =
  ruleTrans (compose1U_eq Snd rKont (cfgRT val K)) (cong1 Snd (rKont_ev val K))

rConsPart_cons : (val frame rest : Term) ->
  Deriv (eqF (ap1 rConsPart (cfgRT val (kons frame rest))) (ap2 pi frame rest))
rConsPart_cons val frame rest =
  ruleTrans (rConsPart_ev val (kons frame rest)) (konsBody frame rest)

rFrame_cons : (val frame rest : Term) ->
  Deriv (eqF (ap1 rFrame (cfgRT val (kons frame rest))) frame)
rFrame_cons val frame rest =
  ruleTrans (compose1U_eq Fst rConsPart (cfgRT val (kons frame rest)))
    (ruleTrans (cong1 Fst (rConsPart_cons val frame rest)) (konsHd frame rest))

rRest_cons : (val frame rest : Term) ->
  Deriv (eqF (ap1 rRest (cfgRT val (kons frame rest))) rest)
rRest_cons val frame rest =
  ruleTrans (compose1U_eq Snd rConsPart (cfgRT val (kons frame rest)))
    (ruleTrans (cong1 Snd (rConsPart_cons val frame rest)) (konsTl frame rest))

rFtag_cons : (val frame rest : Term) ->
  Deriv (eqF (ap1 rFtag (cfgRT val (kons frame rest))) (ap1 Fst frame))
rFtag_cons val frame rest =
  ruleTrans (compose1U_eq Fst rFrame (cfgRT val (kons frame rest)))
            (cong1 Fst (rFrame_cons val frame rest))

rFdata_cons : (val frame rest : Term) ->
  Deriv (eqF (ap1 rFdata (cfgRT val (kons frame rest))) (ap1 Snd frame))
rFdata_cons val frame rest =
  ruleTrans (compose1U_eq Snd rFrame (cfgRT val (kons frame rest)))
            (cong1 Snd (rFrame_cons val frame rest))

dGet1 : (val frame rest : Term) ->
  Deriv (eqF (ap1 d1 (cfgRT val (kons frame rest))) (ap1 Fst (ap1 Snd frame)))
dGet1 val frame rest =
  ruleTrans (compose1U_eq Fst rFdata (cfgRT val (kons frame rest)))
            (cong1 Fst (rFdata_cons val frame rest))

dGet2 : (val frame rest : Term) ->
  Deriv (eqF (ap1 d2 (cfgRT val (kons frame rest))) (ap1 Snd (ap1 Snd frame)))
dGet2 val frame rest =
  ruleTrans (compose1U_eq Snd rFdata (cfgRT val (kons frame rest)))
            (cong1 Snd (rFdata_cons val frame rest))

dGet21 : (val frame rest : Term) ->
  Deriv (eqF (ap1 d21 (cfgRT val (kons frame rest))) (ap1 Fst (ap1 Snd (ap1 Snd frame))))
dGet21 val frame rest =
  ruleTrans (compose1U_eq Fst d2 (cfgRT val (kons frame rest))) (cong1 Fst (dGet2 val frame rest))

dGet22 : (val frame rest : Term) ->
  Deriv (eqF (ap1 d22 (cfgRT val (kons frame rest))) (ap1 Snd (ap1 Snd (ap1 Snd frame))))
dGet22 val frame rest =
  ruleTrans (compose1U_eq Snd d2 (cfgRT val (kons frame rest))) (cong1 Snd (dGet2 val frame rest))

dGet221 : (val frame rest : Term) ->
  Deriv (eqF (ap1 d221 (cfgRT val (kons frame rest)))
              (ap1 Fst (ap1 Snd (ap1 Snd (ap1 Snd frame)))))
dGet221 val frame rest =
  ruleTrans (compose1U_eq Fst d22 (cfgRT val (kons frame rest))) (cong1 Fst (dGet22 val frame rest))

dGet222 : (val frame rest : Term) ->
  Deriv (eqF (ap1 d222 (cfgRT val (kons frame rest)))
              (ap1 Snd (ap1 Snd (ap1 Snd (ap1 Snd frame)))))
dGet222 val frame rest =
  ruleTrans (compose1U_eq Snd d22 (cfgRT val (kons frame rest))) (cong1 Snd (dGet22 val frame rest))

------------------------------------------------------------------------
-- Frame-tag test value + fire / skip helpers.

testFtag_at : (k : Nat) (val frame rest : Term) (ftg : Nat) ->
  Deriv (eqF (ap1 Fst frame) (natCode ftg)) ->
  Deriv (eqF (ap1 (testFtag k) (cfgRT val (kons frame rest)))
              (ap2 natEqF (natCode ftg) (natCode k)))
testFtag_at k val frame rest ftg hftag =
  let c : Term
      c = cfgRT val (kons frame rest)
      e1 = ax_C natEqF rFtag (constN k) c
      rft_v = ruleTrans (rFtag_cons val frame rest) hftag
      e2 = congL natEqF (ap1 (constN k) c) rft_v
      e3 = congR natEqF (natCode ftg) (constN_eq k c)
  in ruleTrans e1 (ruleTrans e2 e3)

ftFireAt : (k : Nat) (val frame rest : Term) ->
  Deriv (eqF (ap1 Fst frame) (natCode k)) ->
  Deriv (eqF (ap1 (testFtag k) (cfgRT val (kons frame rest))) (ap1 s O))
ftFireAt k val frame rest hftag =
  ruleTrans (testFtag_at k val frame rest k hftag) (natEq_eq k)

ftSkipAt : (k ftg : Nat) (val frame rest : Term) ->
  Deriv (eqF (ap1 Fst frame) (natCode ftg)) -> NatNeqWitness ftg k ->
  Deriv (eqF (ap1 (testFtag k) (cfgRT val (kons frame rest))) O)
ftSkipAt k ftg val frame rest hftag w =
  ruleTrans (testFtag_at k val frame rest ftg hftag) (natEqF_at_neq ftg k w)

------------------------------------------------------------------------
-- RT App2 frame transition.

rtBody_App2_value : (val frame rest Fc w : Term) ->
  Deriv (eqF (ap1 d1 (cfgRT val (kons frame rest))) Fc) ->
  Deriv (eqF (ap1 d2 (cfgRT val (kons frame rest))) w) ->
  Deriv (eqF (ap1 rtBody_App2 (cfgRT val (kons frame rest)))
              (cfgEV Fc (ap2 pi w val) rest))
rtBody_App2_value val frame rest Fc w hd1 hd2 =
  let c : Term
      c = cfgRT val (kons frame rest)
      eVal = rVal_ev val (kons frame rest)
      eRest = rRest_cons val frame rest
      eWval : Deriv (eqF (ap1 (C pi d2 rVal) c) (ap2 pi w val))
      eWval = ruleTrans (ax_C pi d2 rVal c)
                (ruleTrans (congL pi (ap1 rVal c) hd2) (congR pi w eVal))
      eFcWval : Deriv (eqF (ap1 (C pi d1 (C pi d2 rVal)) c) (ap2 pi Fc (ap2 pi w val)))
      eFcWval = ruleTrans (ax_C pi d1 (C pi d2 rVal) c)
                  (ruleTrans (congL pi (ap1 (C pi d2 rVal) c) hd1) (congR pi Fc eWval))
      eBody : Deriv (eqF (ap1 (C pi (C pi d1 (C pi d2 rVal)) rRest) c)
                         (ap2 pi (ap2 pi Fc (ap2 pi w val)) rest))
      eBody = ruleTrans (ax_C pi (C pi d1 (C pi d2 rVal)) rRest c)
                (ruleTrans (congL pi (ap1 rRest c) eFcWval)
                           (congR pi (ap2 pi Fc (ap2 pi w val)) eRest))
      e1 = ax_C pi (constN tagEV) (C pi (C pi d1 (C pi d2 rVal)) rRest) c
  in ruleTrans e1
       (ruleTrans (congL pi (ap1 (C pi (C pi d1 (C pi d2 rVal)) rRest) c) (constN_eq tagEV c))
                  (congR pi (natCode tagEV) eBody))

d1_App2 : (val Fc w rest : Term) ->
  Deriv (eqF (ap1 d1 (cfgRT val (kons (frmApp2 Fc w) rest))) Fc)
d1_App2 val Fc w rest =
  ruleTrans (dGet1 val (frmApp2 Fc w) rest)
    (ruleTrans (cong1 Fst (frmApp2_body Fc w)) (axFst Fc w))

d2_App2 : (val Fc w rest : Term) ->
  Deriv (eqF (ap1 d2 (cfgRT val (kons (frmApp2 Fc w) rest))) w)
d2_App2 val Fc w rest =
  ruleTrans (dGet2 val (frmApp2 Fc w) rest)
    (ruleTrans (cong1 Snd (frmApp2_body Fc w)) (axSnd Fc w))

stepU_at_rtApp2 : (val Fc w rest : Term) ->
  Deriv (eqF (ap1 stepU (cfgRT val (kons (frmApp2 Fc w) rest)))
              (cfgEV Fc (ap2 pi w val) rest))
stepU_at_rtApp2 val Fc w rest =
  let frame : Term
      frame = frmApp2 Fc w
      c : Term
      c = cfgRT val (kons frame rest)
      m1 = fireF evBranch modeRT isEV c (isEV_cfgRT val (kons frame rest))
      m2 = fireT rtBranch u isRT c (isRT_cfgRT val (kons frame rest))
      m3 = fireT rtConsBranch rtEmptyBranch rHasFrame c (rHasFrame_cons val frame rest)
      ft = fireT rtBody_App2 rtCascC1 (testFtag tagApp2) c
             (ftFireAt tagApp2 val frame rest (frmApp2_tag Fc w))
      val_eq = rtBody_App2_value val frame rest Fc w
                 (d1_App2 val Fc w rest) (d2_App2 val Fc w rest)
  in ruleTrans m1 (ruleTrans m2 (ruleTrans m3 (ruleTrans ft val_eq)))

------------------------------------------------------------------------
-- RT C1 frame transition.

sndSnd_frmC1 : (gc h2c a : Term) ->
  Deriv (eqF (ap1 Snd (ap1 Snd (frmC1 gc h2c a))) (ap2 pi h2c a))
sndSnd_frmC1 gc h2c a =
  ruleTrans (cong1 Snd (frmC1_body gc h2c a)) (axSnd gc (ap2 pi h2c a))

d1_C1 : (val gc h2c a rest : Term) ->
  Deriv (eqF (ap1 d1 (cfgRT val (kons (frmC1 gc h2c a) rest))) gc)
d1_C1 val gc h2c a rest =
  ruleTrans (dGet1 val (frmC1 gc h2c a) rest)
    (ruleTrans (cong1 Fst (frmC1_body gc h2c a)) (axFst gc (ap2 pi h2c a)))

d21_C1 : (val gc h2c a rest : Term) ->
  Deriv (eqF (ap1 d21 (cfgRT val (kons (frmC1 gc h2c a) rest))) h2c)
d21_C1 val gc h2c a rest =
  ruleTrans (dGet21 val (frmC1 gc h2c a) rest)
    (ruleTrans (cong1 Fst (sndSnd_frmC1 gc h2c a)) (axFst h2c a))

d22_C1 : (val gc h2c a rest : Term) ->
  Deriv (eqF (ap1 d22 (cfgRT val (kons (frmC1 gc h2c a) rest))) a)
d22_C1 val gc h2c a rest =
  ruleTrans (dGet22 val (frmC1 gc h2c a) rest)
    (ruleTrans (cong1 Snd (sndSnd_frmC1 gc h2c a)) (axSnd h2c a))

rtBody_C1_value : (val frame rest gc h2c a : Term) ->
  Deriv (eqF (ap1 d1  (cfgRT val (kons frame rest))) gc)  ->
  Deriv (eqF (ap1 d21 (cfgRT val (kons frame rest))) h2c) ->
  Deriv (eqF (ap1 d22 (cfgRT val (kons frame rest))) a)   ->
  Deriv (eqF (ap1 rtBody_C1 (cfgRT val (kons frame rest)))
              (cfgEV h2c a (kons (frmApp2 gc val) rest)))
rtBody_C1_value val frame rest gc h2c a hd1 hd21 hd22 =
  let c : Term
      c = cfgRT val (kons frame rest)
      eVal = rVal_ev val (kons frame rest)
      eRest = rRest_cons val frame rest
      eGcVal : Deriv (eqF (ap1 (C pi d1 rVal) c) (ap2 pi gc val))
      eGcVal = ruleTrans (ax_C pi d1 rVal c)
                 (ruleTrans (congL pi (ap1 rVal c) hd1) (congR pi gc eVal))
      eFrm : Deriv (eqF (ap1 mkFrmApp2_C1 c) (frmApp2 gc val))
      eFrm = ruleTrans (ax_C pi (constN tagApp2) (C pi d1 rVal) c)
               (ruleTrans (congL pi (ap1 (C pi d1 rVal) c) (constN_eq tagApp2 c))
                          (congR pi (natCode tagApp2) eGcVal))
      eInner2 : Deriv (eqF (ap1 (C pi mkFrmApp2_C1 rRest) c) (ap2 pi (frmApp2 gc val) rest))
      eInner2 = ruleTrans (ax_C pi mkFrmApp2_C1 rRest c)
                  (ruleTrans (congL pi (ap1 rRest c) eFrm) (congR pi (frmApp2 gc val) eRest))
      eKons : Deriv (eqF (ap1 (konsF mkFrmApp2_C1 rRest) c) (kons (frmApp2 gc val) rest))
      eKons = ruleTrans (ax_C pi (constN 1) (C pi mkFrmApp2_C1 rRest) c)
                (ruleTrans (congL pi (ap1 (C pi mkFrmApp2_C1 rRest) c) (constN_eq 1 c))
                           (congR pi (natCode 1) eInner2))
      eH2a : Deriv (eqF (ap1 (C pi d21 d22) c) (ap2 pi h2c a))
      eH2a = ruleTrans (ax_C pi d21 d22 c)
               (ruleTrans (congL pi (ap1 d22 c) hd21) (congR pi h2c hd22))
      eBody : Deriv (eqF (ap1 (C pi (C pi d21 d22) (konsF mkFrmApp2_C1 rRest)) c)
                         (ap2 pi (ap2 pi h2c a) (kons (frmApp2 gc val) rest)))
      eBody = ruleTrans (ax_C pi (C pi d21 d22) (konsF mkFrmApp2_C1 rRest) c)
                (ruleTrans (congL pi (ap1 (konsF mkFrmApp2_C1 rRest) c) eH2a)
                           (congR pi (ap2 pi h2c a) eKons))
      e1 = ax_C pi (constN tagEV) (C pi (C pi d21 d22) (konsF mkFrmApp2_C1 rRest)) c
  in ruleTrans e1
       (ruleTrans (congL pi (ap1 (C pi (C pi d21 d22) (konsF mkFrmApp2_C1 rRest)) c)
                            (constN_eq tagEV c))
                  (congR pi (natCode tagEV) eBody))

stepU_at_rtC1 : (val gc h2c a rest : Term) ->
  Deriv (eqF (ap1 stepU (cfgRT val (kons (frmC1 gc h2c a) rest)))
              (cfgEV h2c a (kons (frmApp2 gc val) rest)))
stepU_at_rtC1 val gc h2c a rest =
  let frame : Term
      frame = frmC1 gc h2c a
      c : Term
      c = cfgRT val (kons frame rest)
      m1 = fireF evBranch modeRT isEV c (isEV_cfgRT val (kons frame rest))
      m2 = fireT rtBranch u isRT c (isRT_cfgRT val (kons frame rest))
      m3 = fireT rtConsBranch rtEmptyBranch rHasFrame c (rHasFrame_cons val frame rest)
      sk_app2 = fireF rtBody_App2 rtCascC1 (testFtag tagApp2) c
                  (ftSkipAt tagApp2 tagC1 val frame rest (frmC1_tag gc h2c a)
                    (decideNatNeq tagC1 tagApp2 (\ ())))
      ft = fireT rtBody_C1 rtCascR1 (testFtag tagC1) c
             (ftFireAt tagC1 val frame rest (frmC1_tag gc h2c a))
      val_eq = rtBody_C1_value val frame rest gc h2c a
                 (d1_C1 val gc h2c a rest) (d21_C1 val gc h2c a rest) (d22_C1 val gc h2c a rest)
  in ruleTrans m1 (ruleTrans m2 (ruleTrans m3 (ruleTrans sk_app2 (ruleTrans ft val_eq))))

------------------------------------------------------------------------
-- RT R1 frame transition.

sndSnd_frmR1 : (rc h1c x m : Term) ->
  Deriv (eqF (ap1 Snd (ap1 Snd (frmR1 rc h1c x m))) (ap2 pi h1c (ap2 pi x m)))
sndSnd_frmR1 rc h1c x m =
  ruleTrans (cong1 Snd (frmR1_body rc h1c x m)) (axSnd rc (ap2 pi h1c (ap2 pi x m)))

sndSndSnd_frmR1 : (rc h1c x m : Term) ->
  Deriv (eqF (ap1 Snd (ap1 Snd (ap1 Snd (frmR1 rc h1c x m)))) (ap2 pi x m))
sndSndSnd_frmR1 rc h1c x m =
  ruleTrans (cong1 Snd (sndSnd_frmR1 rc h1c x m)) (axSnd h1c (ap2 pi x m))

d1_R1 : (val rc h1c x m rest : Term) ->
  Deriv (eqF (ap1 d1 (cfgRT val (kons (frmR1 rc h1c x m) rest))) rc)
d1_R1 val rc h1c x m rest =
  ruleTrans (dGet1 val (frmR1 rc h1c x m) rest)
    (ruleTrans (cong1 Fst (frmR1_body rc h1c x m))
               (axFst rc (ap2 pi h1c (ap2 pi x m))))

d21_R1 : (val rc h1c x m rest : Term) ->
  Deriv (eqF (ap1 d21 (cfgRT val (kons (frmR1 rc h1c x m) rest))) h1c)
d21_R1 val rc h1c x m rest =
  ruleTrans (dGet21 val (frmR1 rc h1c x m) rest)
    (ruleTrans (cong1 Fst (sndSnd_frmR1 rc h1c x m)) (axFst h1c (ap2 pi x m)))

d221_R1 : (val rc h1c x m rest : Term) ->
  Deriv (eqF (ap1 d221 (cfgRT val (kons (frmR1 rc h1c x m) rest))) x)
d221_R1 val rc h1c x m rest =
  ruleTrans (dGet221 val (frmR1 rc h1c x m) rest)
    (ruleTrans (cong1 Fst (sndSndSnd_frmR1 rc h1c x m)) (axFst x m))

d222_R1 : (val rc h1c x m rest : Term) ->
  Deriv (eqF (ap1 d222 (cfgRT val (kons (frmR1 rc h1c x m) rest))) m)
d222_R1 val rc h1c x m rest =
  ruleTrans (dGet222 val (frmR1 rc h1c x m) rest)
    (ruleTrans (cong1 Snd (sndSndSnd_frmR1 rc h1c x m)) (axSnd x m))

rtBody_R1_value : (val frame rest rc h1c x m' : Term) ->
  Deriv (eqF (ap1 d1   (cfgRT val (kons frame rest))) rc)  ->
  Deriv (eqF (ap1 d21  (cfgRT val (kons frame rest))) h1c) ->
  Deriv (eqF (ap1 d221 (cfgRT val (kons frame rest))) x)   ->
  Deriv (eqF (ap1 d222 (cfgRT val (kons frame rest))) m')  ->
  Deriv (eqF (ap1 rtBody_R1 (cfgRT val (kons frame rest)))
              (cfgEV rc (ap2 pi x m') (kons (frmApp2 h1c val) rest)))
rtBody_R1_value val frame rest rc h1c x m' hd1 hd21 hd221 hd222 =
  let c : Term
      c = cfgRT val (kons frame rest)
      eVal = rVal_ev val (kons frame rest)
      eRest = rRest_cons val frame rest
      eXM : Deriv (eqF (ap1 (C pi d221 d222) c) (ap2 pi x m'))
      eXM = ruleTrans (ax_C pi d221 d222 c)
              (ruleTrans (congL pi (ap1 d222 c) hd221) (congR pi x hd222))
      eRcXM : Deriv (eqF (ap1 (C pi d1 (C pi d221 d222)) c) (ap2 pi rc (ap2 pi x m')))
      eRcXM = ruleTrans (ax_C pi d1 (C pi d221 d222) c)
                (ruleTrans (congL pi (ap1 (C pi d221 d222) c) hd1) (congR pi rc eXM))
      eH1val : Deriv (eqF (ap1 (C pi d21 rVal) c) (ap2 pi h1c val))
      eH1val = ruleTrans (ax_C pi d21 rVal c)
                 (ruleTrans (congL pi (ap1 rVal c) hd21) (congR pi h1c eVal))
      eFrm : Deriv (eqF (ap1 mkFrmApp2_R1 c) (frmApp2 h1c val))
      eFrm = ruleTrans (ax_C pi (constN tagApp2) (C pi d21 rVal) c)
               (ruleTrans (congL pi (ap1 (C pi d21 rVal) c) (constN_eq tagApp2 c))
                          (congR pi (natCode tagApp2) eH1val))
      eInner2 : Deriv (eqF (ap1 (C pi mkFrmApp2_R1 rRest) c) (ap2 pi (frmApp2 h1c val) rest))
      eInner2 = ruleTrans (ax_C pi mkFrmApp2_R1 rRest c)
                  (ruleTrans (congL pi (ap1 rRest c) eFrm) (congR pi (frmApp2 h1c val) eRest))
      eKons : Deriv (eqF (ap1 (konsF mkFrmApp2_R1 rRest) c) (kons (frmApp2 h1c val) rest))
      eKons = ruleTrans (ax_C pi (constN 1) (C pi mkFrmApp2_R1 rRest) c)
                (ruleTrans (congL pi (ap1 (C pi mkFrmApp2_R1 rRest) c) (constN_eq 1 c))
                           (congR pi (natCode 1) eInner2))
      eBody : Deriv (eqF (ap1 (C pi (C pi d1 (C pi d221 d222)) (konsF mkFrmApp2_R1 rRest)) c)
                         (ap2 pi (ap2 pi rc (ap2 pi x m')) (kons (frmApp2 h1c val) rest)))
      eBody = ruleTrans (ax_C pi (C pi d1 (C pi d221 d222)) (konsF mkFrmApp2_R1 rRest) c)
                (ruleTrans (congL pi (ap1 (konsF mkFrmApp2_R1 rRest) c) eRcXM)
                           (congR pi (ap2 pi rc (ap2 pi x m')) eKons))
      e1 = ax_C pi (constN tagEV) (C pi (C pi d1 (C pi d221 d222)) (konsF mkFrmApp2_R1 rRest)) c
  in ruleTrans e1
       (ruleTrans (congL pi (ap1 (C pi (C pi d1 (C pi d221 d222)) (konsF mkFrmApp2_R1 rRest)) c)
                            (constN_eq tagEV c))
                  (congR pi (natCode tagEV) eBody))

stepU_at_rtR1 : (val rc h1c x m rest : Term) ->
  Deriv (eqF (ap1 stepU (cfgRT val (kons (frmR1 rc h1c x m) rest)))
              (cfgEV rc (ap2 pi x m) (kons (frmApp2 h1c val) rest)))
stepU_at_rtR1 val rc h1c x m rest =
  let frame : Term
      frame = frmR1 rc h1c x m
      c : Term
      c = cfgRT val (kons frame rest)
      m1 = fireF evBranch modeRT isEV c (isEV_cfgRT val (kons frame rest))
      m2 = fireT rtBranch u isRT c (isRT_cfgRT val (kons frame rest))
      m3 = fireT rtConsBranch rtEmptyBranch rHasFrame c (rHasFrame_cons val frame rest)
      sk_app2 = fireF rtBody_App2 rtCascC1 (testFtag tagApp2) c
                  (ftSkipAt tagApp2 tagR1 val frame rest (frmR1_tag rc h1c x m)
                    (decideNatNeq tagR1 tagApp2 (\ ())))
      sk_C1 = fireF rtBody_C1 rtCascR1 (testFtag tagC1) c
                (ftSkipAt tagC1 tagR1 val frame rest (frmR1_tag rc h1c x m)
                  (decideNatNeq tagR1 tagC1 (\ ())))
      ft = fireT rtBody_R1 rtBody_M (testFtag tagR1) c
             (ftFireAt tagR1 val frame rest (frmR1_tag rc h1c x m))
      val_eq = rtBody_R1_value val frame rest rc h1c x m
                 (d1_R1 val rc h1c x m rest) (d21_R1 val rc h1c x m rest)
                 (d221_R1 val rc h1c x m rest) (d222_R1 val rc h1c x m rest)
  in ruleTrans m1 (ruleTrans m2 (ruleTrans m3 (ruleTrans sk_app2 (ruleTrans sk_C1
       (ruleTrans ft val_eq)))))

------------------------------------------------------------------------
-- RT mu-frame transitions (M-base: search hits; M-step: try next k).

d1_M : (val gc k rest : Term) ->
  Deriv (eqF (ap1 d1 (cfgRT val (kons (frmM gc k) rest))) gc)
d1_M val gc k rest =
  ruleTrans (dGet1 val (frmM gc k) rest)
    (ruleTrans (cong1 Fst (frmM_body gc k)) (axFst gc k))

d2_M : (val gc k rest : Term) ->
  Deriv (eqF (ap1 d2 (cfgRT val (kons (frmM gc k) rest))) k)
d2_M val gc k rest =
  ruleTrans (dGet2 val (frmM gc k) rest)
    (ruleTrans (cong1 Snd (frmM_body gc k)) (axSnd gc k))

-- common cascade prefix: reach rtBody_M (skip App2,C1,R1) at a frmM frame.
reach_rtBody_M : (val gc k rest : Term) ->
  Deriv (eqF (ap1 stepU (cfgRT val (kons (frmM gc k) rest)))
              (ap1 rtBody_M (cfgRT val (kons (frmM gc k) rest))))
reach_rtBody_M val gc k rest =
  let frame : Term
      frame = frmM gc k
      c : Term
      c = cfgRT val (kons frame rest)
      m1 = fireF evBranch modeRT isEV c (isEV_cfgRT val (kons frame rest))
      m2 = fireT rtBranch u isRT c (isRT_cfgRT val (kons frame rest))
      m3 = fireT rtConsBranch rtEmptyBranch rHasFrame c (rHasFrame_cons val frame rest)
      sk_app2 = fireF rtBody_App2 rtCascC1 (testFtag tagApp2) c
                  (ftSkipAt tagApp2 tagM val frame rest (frmM_tag gc k)
                    (decideNatNeq tagM tagApp2 (\ ())))
      sk_C1 = fireF rtBody_C1 rtCascR1 (testFtag tagC1) c
                (ftSkipAt tagC1 tagM val frame rest (frmM_tag gc k)
                  (decideNatNeq tagM tagC1 (\ ())))
      sk_R1 = fireF rtBody_R1 rtBody_M (testFtag tagR1) c
                (ftSkipAt tagR1 tagM val frame rest (frmM_tag gc k)
                  (decideNatNeq tagM tagR1 (\ ())))
  in ruleTrans m1 (ruleTrans m2 (ruleTrans m3 (ruleTrans sk_app2 (ruleTrans sk_C1 sk_R1))))

rtBody_Mbase_value : (val frame rest k : Term) ->
  Deriv (eqF (ap1 d2 (cfgRT val (kons frame rest))) k) ->
  Deriv (eqF (ap1 rtBody_Mbase (cfgRT val (kons frame rest))) (cfgRT k rest))
rtBody_Mbase_value val frame rest k hd2 =
  let c : Term
      c = cfgRT val (kons frame rest)
      eRest = rRest_cons val frame rest
      eKrest : Deriv (eqF (ap1 (C pi d2 rRest) c) (ap2 pi k rest))
      eKrest = ruleTrans (ax_C pi d2 rRest c)
                 (ruleTrans (congL pi (ap1 rRest c) hd2) (congR pi k eRest))
      e1 = ax_C pi (constN tagRT) (C pi d2 rRest) c
  in ruleTrans e1
       (ruleTrans (congL pi (ap1 (C pi d2 rRest) c) (constN_eq tagRT c))
                  (congR pi (natCode tagRT) eKrest))

stepU_at_rtMbase : (gc k rest : Term) ->
  Deriv (eqF (ap1 stepU (cfgRT O (kons (frmM gc k) rest))) (cfgRT k rest))
stepU_at_rtMbase gc k rest =
  let frame : Term
      frame = frmM gc k
      c : Term
      c = cfgRT O (kons frame rest)
      reach = reach_rtBody_M O gc k rest
      mbase = fireF rtBody_Mstep rtBody_Mbase rVal c (rVal_ev O (kons frame rest))
      val_eq = rtBody_Mbase_value O frame rest k (d2_M O gc k rest)
  in ruleTrans reach (ruleTrans mbase val_eq)

rtBody_Mstep_value : (val frame rest gc k : Term) ->
  Deriv (eqF (ap1 d1 (cfgRT val (kons frame rest))) gc) ->
  Deriv (eqF (ap1 d2 (cfgRT val (kons frame rest))) k) ->
  Deriv (eqF (ap1 rtBody_Mstep (cfgRT val (kons frame rest)))
              (cfgEV gc (ap1 s k) (kons (frmM gc (ap1 s k)) rest)))
rtBody_Mstep_value val frame rest gc k hd1 hd2 =
  let c : Term
      c = cfgRT val (kons frame rest)
      eRest = rRest_cons val frame rest
      eSk : Deriv (eqF (ap1 (compose1U s d2) c) (ap1 s k))
      eSk = ruleTrans (compose1U_eq s d2 c) (cong1 s hd2)
      eGcSk : Deriv (eqF (ap1 (C pi d1 (compose1U s d2)) c) (ap2 pi gc (ap1 s k)))
      eGcSk = ruleTrans (ax_C pi d1 (compose1U s d2) c)
                (ruleTrans (congL pi (ap1 (compose1U s d2) c) hd1) (congR pi gc eSk))
      eFrm : Deriv (eqF (ap1 mkFrmM_sk c) (frmM gc (ap1 s k)))
      eFrm = ruleTrans (ax_C pi (constN tagM) (C pi d1 (compose1U s d2)) c)
               (ruleTrans (congL pi (ap1 (C pi d1 (compose1U s d2)) c) (constN_eq tagM c))
                          (congR pi (natCode tagM) eGcSk))
      eInner2 : Deriv (eqF (ap1 (C pi mkFrmM_sk rRest) c) (ap2 pi (frmM gc (ap1 s k)) rest))
      eInner2 = ruleTrans (ax_C pi mkFrmM_sk rRest c)
                  (ruleTrans (congL pi (ap1 rRest c) eFrm) (congR pi (frmM gc (ap1 s k)) eRest))
      eKons : Deriv (eqF (ap1 (konsF mkFrmM_sk rRest) c) (kons (frmM gc (ap1 s k)) rest))
      eKons = ruleTrans (ax_C pi (constN 1) (C pi mkFrmM_sk rRest) c)
                (ruleTrans (congL pi (ap1 (C pi mkFrmM_sk rRest) c) (constN_eq 1 c))
                           (congR pi (natCode 1) eInner2))
      eBody : Deriv (eqF (ap1 (C pi (C pi d1 (compose1U s d2)) (konsF mkFrmM_sk rRest)) c)
                         (ap2 pi (ap2 pi gc (ap1 s k)) (kons (frmM gc (ap1 s k)) rest)))
      eBody = ruleTrans (ax_C pi (C pi d1 (compose1U s d2)) (konsF mkFrmM_sk rRest) c)
                (ruleTrans (congL pi (ap1 (konsF mkFrmM_sk rRest) c) eGcSk)
                           (congR pi (ap2 pi gc (ap1 s k)) eKons))
      e1 = ax_C pi (constN tagEV) (C pi (C pi d1 (compose1U s d2)) (konsF mkFrmM_sk rRest)) c
  in ruleTrans e1
       (ruleTrans (congL pi (ap1 (C pi (C pi d1 (compose1U s d2)) (konsF mkFrmM_sk rRest)) c)
                            (constN_eq tagEV c))
                  (congR pi (natCode tagEV) eBody))

stepU_at_rtMstep : (w gc k rest : Term) ->
  Deriv (eqF (ap1 stepU (cfgRT (ap1 s w) (kons (frmM gc k) rest)))
              (cfgEV gc (ap1 s k) (kons (frmM gc (ap1 s k)) rest)))
stepU_at_rtMstep w gc k rest =
  let frame : Term
      frame = frmM gc k
      c : Term
      c = cfgRT (ap1 s w) (kons frame rest)
      reach = reach_rtBody_M (ap1 s w) gc k rest
      mstep = fireT_s rtBody_Mstep rtBody_Mbase rVal c w (rVal_ev (ap1 s w) (kons frame rest))
      val_eq = rtBody_Mstep_value (ap1 s w) frame rest gc k
                 (d1_M (ap1 s w) gc k rest) (d2_M (ap1 s w) gc k rest)
  in ruleTrans reach (ruleTrans mstep val_eq)
