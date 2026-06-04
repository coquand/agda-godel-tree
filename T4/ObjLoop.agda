{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.ObjLoop -- PART B of P1 (T4/CHAITIN-G1-P1-DESIGN.md), SIMPLIFIED per the
-- surprise.pdf reading: the FIRST hit  w  and its firstness are HYPOTHESES (the
-- paper's "let w be the first proof"), NOT computed.  So no freeze recursor: the
-- mu-loop, run for a simple accumulator fuel  traceFuel w  (the loop tries
-- p(0),p(1),...,p(w) -- w+1 iterations), reaches the return-config holding w.
--
--   * traceFuel : a plain accumulator (no freeze) over the GIVEN w.
--   * the trace : ONE ruleIndNat over the scan position r, invariant
--       Inv r = imp (leq r w) (iter start (traceFuel r) = Cfg r) ,
--     using the given firstness dFirst for each miss (Mstep).
--   * the hit  : at r := w, predRun w + Mbase (the given dHit) -> cfgRT w K.
--
-- The per-position predicate run  predRun  is the one interpreter black box
-- (object position; the honest soft spot).  Fuel and positions are object Terms.

module T4.ObjLoop where

open import T4.Base
open import T4.EvalU
  using ( mcodeMu ; cfgEV ; cfgRT ; kons ; frmM ; tagRT )
open import T4.EvalU using ( cfgHALT ; konEmpty ; frmC1 ; frmApp2 ; mcode1 )
open import T4.EvalUStep
  using ( stepU ; stepU_at_evMu ; stepU_at_rtMstep ; stepU_at_rtMbase
        ; stepU_at_evC_code ; stepU_at_rtC1 ; stepU_at_evU ; stepU_at_rtApp2
        ; stepU_at_rtEmpty )
open import T4.EvalUEval
  using ( evalU ; evalU_unfold ; initF ; initF_eq ; readout ; readout_halt )
open import T4.IterComp using ( iterComp ; iterStepO )
open import T4.Tags using ( tag_C )

open import BRA3.Church          using ( pi ; sigma ; sub ; T33 ; T34 )
open import BRA3.ChurchLeq       using ( leq )
open import BRA3.ChurchT84       using ( T84 )
open import BRA3.ChurchT85       using ( T85 )
open import BRA3.CourseOfValues  using ( iter )
open import BRA3.RuleInst2       using ( ruleInst2 )
open import BRA3.PairAlgebra     using ( axFst ; axSnd ; compose1U ; compose1U_eq
                                       ; Fan ; Lift1 ; axFan ; axLift ; axComp )
open import BRA3.Dispatch        using ( constN ; constN_eq )
open import BRA3.RecBRA3AtPairUniv using ( iter_step_univ )
open import BRA3.Logic           using ( prependEqLeft ; appendEqRight )
open import BRA3.Contrapositive  using ( liftP ; compI ; bCombTwo )
open import T4.Counting        using ( ruleInst3v ; mapUnder2 )
open import T4.CountingObj     using ( closeCoe ; trans2 ; leqNN )

------------------------------------------------------------------------
-- SECTION 0.  leq helpers:  n <= s n  and the weakening  s n <= w -> n <= w .

n_le_sn : (n : Term) -> Deriv (leq n (ap1 s n))
n_le_sn n =
  let sigma_n_sO : Deriv (eqF (ap2 sigma n (ap1 s O)) (ap1 s n))
      sigma_n_sO = ruleTrans (ruleInst2 0 n 1 O refl T34) (cong1 s (T33 n))
      T85inst : Deriv (eqF (ap2 sub n (ap2 sigma n (ap1 s O))) O)
      T85inst = ruleInst2 0 n 1 (ap1 s O) refl T85
  in ruleTrans (ruleSym (congR sub n sigma_n_sO)) T85inst

succ_leq_weaken : (n w : Term) -> Deriv (imp (leq (ap1 s n) w) (leq n w))
succ_leq_weaken n w =
  let T84inst : Deriv (imp (leq n (ap1 s n)) (imp (leq (ap1 s n) w) (leq n w)))
      T84inst = ruleInst3v n (ap1 s n) w T84
  in mp T84inst (n_le_sn n)

-- sigma a (s O) = s a .
sigma_x_sO : (a : Term) -> Deriv (eqF (ap2 sigma a (ap1 s O)) (ap1 s a))
sigma_x_sO a = ruleTrans (ruleInst2 0 a 1 O refl T34) (cong1 s (T33 a))

-- object single step:  iter c (s O) = c'  from  stepU c = c' .
oStep : (c c' : Term) -> Deriv (eqF (ap1 stepU c) c') ->
        Deriv (eqF (ap2 (iter stepU) c (ap1 s O)) c')
oStep c c' red = ruleTrans (iterStepO c) red

-- object composition of two reaches:  iter c1 f1 = c2 , iter c2 f2 = c3
--   =>  iter c1 (sigma f1 f2) = c3 .
oCompose : (c1 c2 c3 f1 f2 : Term) ->
  Deriv (eqF (ap2 (iter stepU) c1 f1) c2) ->
  Deriv (eqF (ap2 (iter stepU) c2 f2) c3) ->
  Deriv (eqF (ap2 (iter stepU) c1 (ap2 sigma f1 f2)) c3)
oCompose c1 c2 c3 f1 f2 r1 r2 =
  ruleTrans (iterComp c1 f1 f2)
            (ruleTrans (congL (iter stepU) f2 r1) r2)

------------------------------------------------------------------------
-- The loop, parametric in the predicate code  gc , its per-position value
-- pval , the per-position run fuel  pfuelF , and the interpreter black box
-- predRun .

module Loop
  (gc      : Term)
  (clGc    : Closed gc)
  (pval    : Term -> Term)
  (pfuelF  : Fun1)
  (predRun : (r K : Term) ->
     Deriv (eqF (ap2 (iter stepU) (cfgEV gc r (kons (frmM gc r) K)) (ap1 pfuelF r))
                (cfgRT (pval r) (kons (frmM gc r) K))))
  where

  ----------------------------------------------------------------------
  -- SECTION 1.  The accumulator fuel recursor (NO freeze).
  --   traceFuel O     = s O                                  (the evMu step)
  --   traceFuel (s n) = sigma (traceFuel n) (sigma (pfuelF n) (s O))

  chunkF : Fun2                     -- ap2 chunkF (pi x n) prev = sigma (pfuelF n) (s O)
  chunkF = Fan (Lift1 (compose1U pfuelF Snd)) (Lift1 (constN 1)) sigma

  stepFuelF : Fun2                  -- ap2 stepFuelF (pi x n) prev = sigma prev (sigma (pfuelF n)(sO))
  stepFuelF = Fan v chunkF sigma

  traceFuelF : Fun2
  traceFuelF = R (constN 1) stepFuelF pi

  traceFuel : Term -> Term
  traceFuel r = ap2 traceFuelF O r

  chunkF_eq :
    (x n prev : Term) ->
    Deriv (eqF (ap2 chunkF (ap2 pi x n) prev)
               (ap2 sigma (ap1 pfuelF n) (ap1 s O)))
  chunkF_eq x n prev =
    let pkg : Term
        pkg = ap2 pi x n
        eL : Deriv (eqF (ap2 (Lift1 (compose1U pfuelF Snd)) pkg prev) (ap1 pfuelF n))
        eL = ruleTrans (axLift (compose1U pfuelF Snd) pkg prev)
               (ruleTrans (axComp pfuelF Snd pkg) (cong1 pfuelF (axSnd x n)))
        eR : Deriv (eqF (ap2 (Lift1 (constN 1)) pkg prev) (ap1 s O))
        eR = ruleTrans (axLift (constN 1) pkg prev) (constN_eq 1 pkg)
    in ruleTrans (axFan (Lift1 (compose1U pfuelF Snd)) (Lift1 (constN 1)) sigma pkg prev)
         (ruleTrans (congL sigma (ap2 (Lift1 (constN 1)) pkg prev) eL)
                    (congR sigma (ap1 pfuelF n) eR))

  stepFuelF_eq :
    (x n prev : Term) ->
    Deriv (eqF (ap2 stepFuelF (ap2 pi x n) prev)
               (ap2 sigma prev (ap2 sigma (ap1 pfuelF n) (ap1 s O))))
  stepFuelF_eq x n prev =
    let pkg : Term
        pkg = ap2 pi x n
    in ruleTrans (axFan v chunkF sigma pkg prev)
         (ruleTrans (congL sigma (ap2 chunkF pkg prev) (ax_v pkg prev))
                    (congR sigma prev (chunkF_eq x n prev)))

  traceFuel_at_O : Deriv (eqF (traceFuel O) (ap1 s O))
  traceFuel_at_O =
    ruleTrans (ax_R_base (constN 1) stepFuelF pi O) (constN_eq 1 O)

  traceFuel_at_succ :
    (n : Term) ->
    Deriv (eqF (traceFuel (ap1 s n))
               (ap2 sigma (traceFuel n) (ap2 sigma (ap1 pfuelF n) (ap1 s O))))
  traceFuel_at_succ n =
    ruleTrans (ax_R_step (constN 1) stepFuelF pi O n) (stepFuelF_eq O n (traceFuel n))

  ----------------------------------------------------------------------
  -- SECTION 2.  Config shorthands.

  startK : Term -> Term
  startK K = cfgEV (mcodeMu gc) O K

  cfgAt : Term -> Term -> Term
  cfgAt r K = cfgEV gc r (kons (frmM gc r) K)

  chunk : Term -> Term
  chunk n = ap2 sigma (ap1 pfuelF n) (ap1 s O)

  -- rewrite the value slot of a cfgRT under an equation (as an implication).
  cfgRTvalImpl : (va vb K' : Term) ->
    Deriv (imp (eqF va vb) (eqF (cfgRT va K') (cfgRT vb K')))
  cfgRTvalImpl va vb K' =
    compI (ax_eqCongL pi va vb K')
          (ax_eqCongR pi (ap2 pi va K') (ap2 pi vb K') (natCode tagRT))

  ----------------------------------------------------------------------
  -- SECTION 3.  muLoopReach -- the mu-loop, run for the accumulator fuel over
  -- the GIVEN first hit w, reaches the return-config holding w.

  muLoopReach :
    (w K : Term) -> Closed w -> Closed K ->
    ((x : Term) -> Deriv (imp (leq (ap1 s x) w) (eqF (pval x) (ap1 s O)))) ->
    Deriv (eqF (pval w) O) ->
    Deriv (eqF (ap2 (iter stepU) (startK K)
                    (ap2 sigma (traceFuel w) (chunk w)))
               (cfgRT w K))
  muLoopReach w K clW clK dFirst dHit = final
    where
      Inv : Term -> Formula
      Inv r = imp (leq r w)
                  (eqF (ap2 (iter stepU) (startK K) (traceFuel r)) (cfgAt r K))

      n0 : Term
      n0 = var zero
      sn : Term
      sn = ap1 s n0

      -- base.
      reachO : Deriv (eqF (ap2 (iter stepU) (startK K) (traceFuel O)) (cfgAt O K))
      reachO = ruleTrans (congR (iter stepU) (startK K) traceFuel_at_O)
                 (ruleTrans (iterStepO (startK K)) (stepU_at_evMu gc O K))

      baseReal : Deriv (Inv O)
      baseReal = liftP (leq O w) reachO

      base : Deriv (substF zero O (Inv n0))
      base =
        closeCoe clK zero O
          (\ X -> imp (leq O (substT zero O w))
             (eqF (ap2 (iter stepU) (cfgEV (mcodeMu (substT zero O gc)) O X) (traceFuel O))
                  (cfgEV (substT zero O gc) O (kons (frmM (substT zero O gc) O) X))))
        (closeCoe clGc zero O
          (\ X -> imp (leq O (substT zero O w))
             (eqF (ap2 (iter stepU) (cfgEV (mcodeMu X) O K) (traceFuel O))
                  (cfgEV X O (kons (frmM X O) K))))
        (closeCoe clW zero O
          (\ X -> imp (leq O X)
             (eqF (ap2 (iter stepU) (cfgEV (mcodeMu gc) O K) (traceFuel O))
                  (cfgEV gc O (kons (frmM gc O) K))))
          baseReal))

      -- step.
      phi1 : Formula
      phi1 = Inv n0
      phi2 : Formula
      phi2 = leq sn w
      Rn : Formula
      Rn = eqF (ap2 (iter stepU) (startK K) (traceFuel n0)) (cfgAt n0 K)
      Rsn : Formula
      Rsn = eqF (ap2 (iter stepU) (startK K) (traceFuel sn)) (cfgAt sn K)

      P0 : Term
      P0 = ap2 (iter stepU) (startK K) (traceFuel n0)
      Q0 : Term
      Q0 = cfgAt n0 K
      M0 : Term
      M0 = ap2 (iter stepU) (ap2 (iter stepU) (startK K) (traceFuel n0)) (chunk n0)
      Mq : Term
      Mq = ap2 (iter stepU) (cfgAt n0 K) (chunk n0)

      -- Rn available under (phi1, phi2):
      Rn2 : Deriv (imp phi1 (imp phi2 Rn))
      Rn2 = bCombTwo (axK phi1 phi2) (liftP phi1 (succ_leq_weaken n0 w))

      -- pval n0 = s O under (phi1, phi2):
      pn2 : Deriv (imp phi1 (imp phi2 (eqF (pval n0) (ap1 s O))))
      pn2 = liftP phi1 (dFirst n0)

      -- A : iter start (traceFuel sn) = M0     (closed)
      A : Deriv (eqF (ap2 (iter stepU) (startK K) (traceFuel sn)) M0)
      A = ruleTrans (congR (iter stepU) (startK K) (traceFuel_at_succ n0))
                    (iterComp (startK K) (traceFuel n0) (chunk n0))

      -- f1 : Rn -> (iter start (traceFuel sn) = Mq)
      f1 : Deriv (imp Rn (eqF (ap2 (iter stepU) (startK K) (traceFuel sn)) Mq))
      f1 = compI (ax_eqCongL (iter stepU) P0 Q0 (chunk n0))
                 (prependEqLeft (ap2 (iter stepU) (startK K) (traceFuel sn)) M0 Mq A)

      leg1 : Deriv (imp phi1 (imp phi2 (eqF (ap2 (iter stepU) (startK K) (traceFuel sn)) Mq)))
      leg1 = mapUnder2 phi1 phi2 f1 Rn2

      -- D : the closed chain  Mq = stepU (cfgRT (pval n0) (kons (frmM gc n0) K))
      Dclosed : Deriv (eqF Mq (ap1 stepU (cfgRT (pval n0) (kons (frmM gc n0) K))))
      Dclosed = ruleTrans (congR (iter stepU) (cfgAt n0 K) (sigma_x_sO (ap1 pfuelF n0)))
                  (ruleTrans (iter_step_univ stepU (cfgAt n0 K) (ap1 pfuelF n0))
                             (cong1 stepU (predRun n0 K)))

      -- G : stepU (cfgRT (s O) (kons (frmM gc n0) K)) = cfgAt sn K   (closed; rtMstep)
      G : Deriv (eqF (ap1 stepU (cfgRT (ap1 s O) (kons (frmM gc n0) K))) (cfgAt sn K))
      G = stepU_at_rtMstep O gc n0 K

      -- f2 : (pval n0 = s O) -> (Mq = cfgAt sn K)
      f2 : Deriv (imp (eqF (pval n0) (ap1 s O)) (eqF Mq (cfgAt sn K)))
      f2 =
        let frmK0 : Term
            frmK0 = kons (frmM gc n0) K
            spv : Term
            spv = ap1 stepU (cfgRT (pval n0) frmK0)
            ssO : Term
            ssO = ap1 stepU (cfgRT (ap1 s O) frmK0)
            middle : Deriv (imp (eqF (pval n0) (ap1 s O)) (eqF spv ssO))
            middle = compI (cfgRTvalImpl (pval n0) (ap1 s O) frmK0)
                           (ax_eqCong1 stepU (cfgRT (pval n0) frmK0) (cfgRT (ap1 s O) frmK0))
            pre : Deriv (imp (eqF spv ssO) (eqF Mq ssO))
            pre = prependEqLeft Mq spv ssO Dclosed
            post : Deriv (imp (eqF Mq ssO) (eqF Mq (cfgAt sn K)))
            post = appendEqRight Mq ssO (cfgAt sn K) G
        in compI (compI middle pre) post

      leg2 : Deriv (imp phi1 (imp phi2 (eqF Mq (cfgAt sn K))))
      leg2 = mapUnder2 phi1 phi2 f2 pn2

      stepReal : Deriv (imp phi1 (imp phi2 Rsn))
      stepReal = trans2 phi1 phi2
                   (ap2 (iter stepU) (startK K) (traceFuel sn)) Mq (cfgAt sn K)
                   leg1 leg2

      step : Deriv (imp (Inv n0) (substF zero sn (Inv n0)))
      step =
        closeCoe clK zero sn
          (\ X -> imp (Inv n0)
             (imp (leq sn (substT zero sn w))
                (eqF (ap2 (iter stepU) (cfgEV (mcodeMu (substT zero sn gc)) O X) (traceFuel sn))
                     (cfgEV (substT zero sn gc) sn (kons (frmM (substT zero sn gc) sn) X)))))
        (closeCoe clGc zero sn
          (\ X -> imp (Inv n0)
             (imp (leq sn (substT zero sn w))
                (eqF (ap2 (iter stepU) (cfgEV (mcodeMu X) O K) (traceFuel sn))
                     (cfgEV X sn (kons (frmM X sn) K)))))
        (closeCoe clW zero sn
          (\ X -> imp (Inv n0)
             (imp (leq sn X)
                (eqF (ap2 (iter stepU) (cfgEV (mcodeMu gc) O K) (traceFuel sn))
                     (cfgEV gc sn (kons (frmM gc sn) K)))))
          stepReal))

      ind : Deriv (Inv n0)
      ind = ruleIndNat zero {P = Inv n0} base step

      indAtW : Deriv (substF zero w (Inv n0))
      indAtW = ruleInst zero w ind

      invW : Deriv (Inv w)
      invW =
        eqSubst (\ X -> Deriv (imp (leq w w)
                  (eqF (ap2 (iter stepU) (cfgEV (mcodeMu gc) O X) (traceFuel w))
                       (cfgEV gc w (kons (frmM gc w) X)))))
                (Closed.closedAt clK zero w)
        (eqSubst (\ X -> Deriv (imp (leq w w)
                  (eqF (ap2 (iter stepU) (cfgEV (mcodeMu X) O (substT zero w K)) (traceFuel w))
                       (cfgEV X w (kons (frmM X w) (substT zero w K))))))
                (Closed.closedAt clGc zero w)
        (eqSubst (\ X -> Deriv (imp (leq w X)
                  (eqF (ap2 (iter stepU) (cfgEV (mcodeMu (substT zero w gc)) O (substT zero w K)) (traceFuel w))
                       (cfgEV (substT zero w gc) w (kons (frmM (substT zero w gc) w) (substT zero w K))))))
                (Closed.closedAt clW zero w)
                indAtW))

      traceReach : Deriv (eqF (ap2 (iter stepU) (startK K) (traceFuel w)) (cfgAt w K))
      traceReach = mp invW (leqNN w)

      -- the hit step at w.
      final : Deriv (eqF (ap2 (iter stepU) (startK K)
                              (ap2 sigma (traceFuel w) (chunk w)))
                         (cfgRT w K))
      final =
        ruleTrans (iterComp (startK K) (traceFuel w) (chunk w))
          (ruleTrans (congL (iter stepU) (chunk w) traceReach)
            (ruleTrans (congR (iter stepU) (cfgAt w K) (sigma_x_sO (ap1 pfuelF w)))
              (ruleTrans (iter_step_univ stepU (cfgAt w K) (ap1 pfuelF w))
                (ruleTrans (cong1 stepU (predRun w K))
                  (ruleTrans (cong1 stepU cfgRTvalImplApp)
                             (stepU_at_rtMbase gc w K))))))
        where
          cfgRTvalImplApp : Deriv (eqF (cfgRT (pval w) (kons (frmM gc w) K))
                                       (cfgRT O (kons (frmM gc w) K)))
          cfgRTvalImplApp = mp (cfgRTvalImpl (pval w) O (kons (frmM gc w) K)) dHit

  ----------------------------------------------------------------------
  -- SECTION 4.  PART C -- the  out_L  C-wrapper.  gLcode = C-wrapper around the
  -- mu-program; running it outputs  out_L w  (the OBJECT subject, no z0 : Nat).
  --   evC -> mu-loop -> rtC1 -> evU -> rtApp2 -> out_L (black box) -> halt -> readout.

  gLcodeOf : Term -> Term
  gLcodeOf gCode =
    ap2 pi (natCode tag_C) (ap2 pi gCode (ap2 pi (mcodeMu gc) (mcode1 u)))

  gLEvalObj :
    (gCode w : Term) -> Closed w ->
    Closed (kons (frmC1 gCode (mcode1 u) O) konEmpty) ->
    ((x : Term) -> Deriv (imp (leq (ap1 s x) w) (eqF (pval x) (ap1 s O)))) ->
    Deriv (eqF (pval w) O) ->
    (outVal outFuel : Term) ->
    Deriv (eqF (ap2 (iter stepU) (cfgEV gCode (ap2 pi w O) konEmpty) outFuel)
               (cfgRT outVal konEmpty)) ->
    Deriv (eqF (ap2 evalU (gLcodeOf gCode)
                    (ap2 sigma (ap1 s O)
                      (ap2 sigma (ap2 sigma (traceFuel w) (chunk w))
                        (ap2 sigma (ap1 s O)
                          (ap2 sigma (ap1 s O)
                            (ap2 sigma (ap1 s O)
                              (ap2 sigma outFuel (ap1 s O))))))))
               (ap1 s outVal))
  gLEvalObj gCode w clW clKC1 dFirst dHit outVal outFuel outLRunD = dEval0
    where
      kC1 : Term
      kC1 = kons (frmC1 gCode (mcode1 u) O) konEmpty
      c1 : Term
      c1 = cfgEV (gLcodeOf gCode) O konEmpty
      c2 : Term
      c2 = cfgEV (mcodeMu gc) O kC1
      c3 : Term
      c3 = cfgRT w kC1
      c4 : Term
      c4 = cfgEV (mcode1 u) O (kons (frmApp2 gCode w) konEmpty)
      c5 : Term
      c5 = cfgRT O (kons (frmApp2 gCode w) konEmpty)
      c6 : Term
      c6 = cfgEV gCode (ap2 pi w O) konEmpty
      cRT : Term
      cRT = cfgRT outVal konEmpty
      cHALT : Term
      cHALT = cfgHALT outVal

      r1 : Deriv (eqF (ap2 (iter stepU) c1 (ap1 s O)) c2)
      r1 = oStep c1 c2 (stepU_at_evC_code gCode (mcodeMu gc) (mcode1 u) O konEmpty)
      r2 : Deriv (eqF (ap2 (iter stepU) c2 (ap2 sigma (traceFuel w) (chunk w))) c3)
      r2 = muLoopReach w kC1 clW clKC1 dFirst dHit
      r3 : Deriv (eqF (ap2 (iter stepU) c3 (ap1 s O)) c4)
      r3 = oStep c3 c4 (stepU_at_rtC1 w gCode (mcode1 u) O konEmpty)
      r4 : Deriv (eqF (ap2 (iter stepU) c4 (ap1 s O)) c5)
      r4 = oStep c4 c5 (stepU_at_evU O (kons (frmApp2 gCode w) konEmpty))
      r5 : Deriv (eqF (ap2 (iter stepU) c5 (ap1 s O)) c6)
      r5 = oStep c5 c6 (stepU_at_rtApp2 O gCode w konEmpty)
      r6 : Deriv (eqF (ap2 (iter stepU) c6 outFuel) cRT)
      r6 = outLRunD
      r7 : Deriv (eqF (ap2 (iter stepU) cRT (ap1 s O)) cHALT)
      r7 = oStep cRT cHALT (stepU_at_rtEmpty outVal)

      wholeReach :
        Deriv (eqF (ap2 (iter stepU) c1
                     (ap2 sigma (ap1 s O)
                       (ap2 sigma (ap2 sigma (traceFuel w) (chunk w))
                         (ap2 sigma (ap1 s O)
                           (ap2 sigma (ap1 s O)
                             (ap2 sigma (ap1 s O)
                               (ap2 sigma outFuel (ap1 s O))))))))
                   cHALT)
      wholeReach =
        oCompose c1 c2 cHALT (ap1 s O) _ r1
          (oCompose c2 c3 cHALT (ap2 sigma (traceFuel w) (chunk w)) _ r2
            (oCompose c3 c4 cHALT (ap1 s O) _ r3
              (oCompose c4 c5 cHALT (ap1 s O) _ r4
                (oCompose c5 c6 cHALT (ap1 s O) _ r5
                  (oCompose c6 cRT cHALT outFuel (ap1 s O) r6 r7)))))

      total : Term
      total = ap2 sigma (ap1 s O)
                (ap2 sigma (ap2 sigma (traceFuel w) (chunk w))
                  (ap2 sigma (ap1 s O)
                    (ap2 sigma (ap1 s O)
                      (ap2 sigma (ap1 s O)
                        (ap2 sigma outFuel (ap1 s O))))))

      dEval0 : Deriv (eqF (ap2 evalU (gLcodeOf gCode) total) (ap1 s outVal))
      dEval0 =
        ruleTrans (evalU_unfold (gLcodeOf gCode) total)
          (ruleTrans (cong1 readout
                        (ruleTrans (congL (iter stepU) total (initF_eq (gLcodeOf gCode)))
                                   wholeReach))
                     (readout_halt outVal))
