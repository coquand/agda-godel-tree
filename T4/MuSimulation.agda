{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.MuSimulation -- mu-program simulation correctness via evalU + enc.
--
-- The general meta-theorem: BRA's universal interpreter  evalU  faithfully
-- simulates C-wrapped mu-programs.  Given a hit detector  p , a first hit
-- z , firstness  (dHit, dBelow) , a post-transform Fun2  g , and the
-- evalU-correctness obligations  peval  (for p ) and  gval  (for g , both
-- Term-fueled = TReaches), there is a Term fuel  n0  such that
--
--   evalU (parse (enc (muProg p g))) n0  =  s (g(z, O))
--
-- where  muProg p g = C (mcode2 g) (mcodeMu (mcode1 (compose1U isZero p))) u .
-- The Term fuel  n0  is a DETERMINED Term function of  z  (Sigma m(i) for
-- i = 0..z, the analog of thm12's internal computation-step counter).
--
-- See  T4/CGI-NEXT-SESSION-HANDOFF.md  for the build plan.

module T4.MuSimulation where

open import T4.Base
open import T4.Tags        using ( tag_C ; tag_s ; tag_o ; tag_u ; tag_v ; tag_R )
open import T4.EvalU
  using ( mcode1 ; mcode2 ; mcodeMu ; cfgEV ; cfgRT ; cfgHALT ; kons ; konEmpty
        ; frmM ; frmC1 ; frmApp2
        ; tag_mu ; tagEV ; tagRT ; tagC1 ; tagM ; tagApp2 )
open import T4.EvalUStep
  using ( stepU ; stepU_at_evC_code ; stepU_at_evMu
        ; stepU_at_rtMstep ; stepU_at_rtMbase
        ; stepU_at_rtC1 ; stepU_at_evU ; stepU_at_rtApp2 ; stepU_at_rtEmpty )
open import BRA3.CourseOfValues using ( iter )
open import T4.LoopReaches
  using ( module Loop
        ; ClosedAtVar ; mkCAV ; cavSubst
        ; cav_O ; cav_ap1 ; cav_ap2 ; cav_var ; cav_natCode
        ; TReaches ; mkTReach ; tsteps ; tstepsCAV5 ; truns
        ; treach_refl ; treach_step1 ; treach_eq_target
        ; treach_from_reach ; treach_trans )

open import BRA3.Church      using ( pi ; sigma )
open import BRA3.ChurchLeq   using ( leq )
open import T4.CountingObj using ( leqNN )
open import BRA3.Dispatch using ( Closed )
open import T4.EvalUEval using ( evalU )
import T4.ObjLoop as OL
open import T4.Thm12.All using ( Sigma ; mkSigma )

------------------------------------------------------------------------
-- Closure helpers : ClosedAtVar k for the EvalU configuration / encoding
-- Terms.  All EvalU constructors are built from  ap2 pi ,  natCode ,  O ,
-- (ap1 s O) , and recursive  mcode1 / mcode2 .  Each helper is a one-line
-- composition of  cav_ap2 ,  cav_natCode ,  cav_O ,  cav_ap1 .

cav_mcode1 : (k : Nat) (f : Fun1) -> ClosedAtVar k (mcode1 f)
cav_mcode2 : (k : Nat) (g : Fun2) -> ClosedAtVar k (mcode2 g)

cav_mcode1 k s = cav_ap2 k pi (natCode tag_s) O (cav_natCode k tag_s) (cav_O k)
cav_mcode1 k o = cav_ap2 k pi (natCode tag_o) O (cav_natCode k tag_o) (cav_O k)
cav_mcode1 k u = cav_ap2 k pi (natCode tag_u) O (cav_natCode k tag_u) (cav_O k)
cav_mcode1 k (C g h1 h2) =
  cav_ap2 k pi (natCode tag_C)
    (ap2 pi (mcode2 g) (ap2 pi (mcode1 h1) (mcode1 h2)))
    (cav_natCode k tag_C)
    (cav_ap2 k pi (mcode2 g) (ap2 pi (mcode1 h1) (mcode1 h2))
      (cav_mcode2 k g)
      (cav_ap2 k pi (mcode1 h1) (mcode1 h2)
        (cav_mcode1 k h1) (cav_mcode1 k h2)))

cav_mcode2 k v = cav_ap2 k pi (natCode tag_v) O (cav_natCode k tag_v) (cav_O k)
cav_mcode2 k (R g h1 h2) =
  cav_ap2 k pi (natCode tag_R)
    (ap2 pi (mcode1 g) (ap2 pi (mcode2 h1) (mcode2 h2)))
    (cav_natCode k tag_R)
    (cav_ap2 k pi (mcode1 g) (ap2 pi (mcode2 h1) (mcode2 h2))
      (cav_mcode1 k g)
      (cav_ap2 k pi (mcode2 h1) (mcode2 h2)
        (cav_mcode2 k h1) (cav_mcode2 k h2)))

cav_mcodeMu : (k : Nat) (gc : Term) -> ClosedAtVar k gc -> ClosedAtVar k (mcodeMu gc)
cav_mcodeMu k gc cgc =
  cav_ap2 k pi (natCode tag_mu) gc (cav_natCode k tag_mu) cgc

cav_konEmpty : (k : Nat) -> ClosedAtVar k konEmpty
cav_konEmpty k = cav_ap2 k pi O O (cav_O k) (cav_O k)

cav_kons : (k : Nat) (frame rest : Term) ->
           ClosedAtVar k frame -> ClosedAtVar k rest -> ClosedAtVar k (kons frame rest)
cav_kons k frame rest cf cr =
  cav_ap2 k pi (ap1 s O) (ap2 pi frame rest)
    (cav_ap1 k s O (cav_O k))
    (cav_ap2 k pi frame rest cf cr)

cav_frmM : (k : Nat) (gc kk : Term) ->
           ClosedAtVar k gc -> ClosedAtVar k kk -> ClosedAtVar k (frmM gc kk)
cav_frmM k gc kk cgc ckk =
  cav_ap2 k pi (natCode tagM) (ap2 pi gc kk)
    (cav_natCode k tagM)
    (cav_ap2 k pi gc kk cgc ckk)

cav_frmC1 : (k : Nat) (gc h2c a : Term) ->
            ClosedAtVar k gc -> ClosedAtVar k h2c -> ClosedAtVar k a ->
            ClosedAtVar k (frmC1 gc h2c a)
cav_frmC1 k gc h2c a cgc ch2c ca =
  cav_ap2 k pi (natCode tagC1) (ap2 pi gc (ap2 pi h2c a))
    (cav_natCode k tagC1)
    (cav_ap2 k pi gc (ap2 pi h2c a) cgc
      (cav_ap2 k pi h2c a ch2c ca))

cav_cfgEV : (k : Nat) (fc a kk : Term) ->
            ClosedAtVar k fc -> ClosedAtVar k a -> ClosedAtVar k kk ->
            ClosedAtVar k (cfgEV fc a kk)
cav_cfgEV k fc a kk cfc ca ckk =
  cav_ap2 k pi (natCode tagEV) (ap2 pi (ap2 pi fc a) kk)
    (cav_natCode k tagEV)
    (cav_ap2 k pi (ap2 pi fc a) kk
      (cav_ap2 k pi fc a cfc ca) ckk)

cav_cfgRT : (k : Nat) (val kk : Term) ->
            ClosedAtVar k val -> ClosedAtVar k kk -> ClosedAtVar k (cfgRT val kk)
cav_cfgRT k val kk cv ck =
  cav_ap2 k pi (natCode tagRT) (ap2 pi val kk)
    (cav_natCode k tagRT)
    (cav_ap2 k pi val kk cv ck)

------------------------------------------------------------------------
-- The abstract simulation module.

module MuSim
  (p : Fun1)                                                       -- the hit detector
  (p_le_one : (r : Term) -> Deriv (leq (ap1 p r) (ap1 s O)))
  (z : Term)                                                       -- the first hit
  (cav_z_at : (k : Nat) -> ClosedAtVar k z)                        -- z is closed at every var
  (dHit : Deriv (eqF (ap1 p z) (ap1 s O)))
  (dBelow : (x : Term) ->
            Deriv (imp (leq (ap1 s x) z) (eqF (ap1 p x) O)))
  (gPost : Fun2)                                                       -- the post-transform
  where

  cav_z : ClosedAtVar 5 z
  cav_z = cav_z_at 5

  ----------------------------------------------------------------------
  -- SECTION A.  Re-open LoopReaches.Loop at  p  to inherit  pFlip ,
  -- pFlip_at_hit , pFlip_below , and FirstHit.Search at  p  (g , compInv ,
  -- firstnessU , leastNumber).

  open Loop p p_le_one z dHit dBelow public

  ----------------------------------------------------------------------
  -- SECTION B.  The mu-program code.
  --
  -- muProg = C (mcode2 g) (mcodeMu (mcode1 pFlip)) (mcode1 u)  at the
  -- encoded level (the surprise.pdf g_L0's BRA encoding).  When evalU runs
  -- on  muProg  starting from input  O , it:
  --   1. (C-dispatch) Enters the middle child = the mu-loop.
  --   2. (mu-loop) Scans for the first k with pFlip(k) = O ; halts at  z .
  --   3. (C-cleanup) Applies  g  to the pair  (z, O)  via the third child u
  --      passing the input  O  through.
  --   4. Output:  g(z, O) .

  muProg : Term
  muProg = ap2 pi (natCode tag_C)
             (ap2 pi (mcode2 gPost)
                (ap2 pi (mcodeMu (mcode1 pFlip)) (mcode1 u)))

  ----------------------------------------------------------------------
  -- SECTION C.  Setup chain -- 2 stepUs from the initial cfg to muStart.
  --
  -- From  cfgEV muProg O konEmpty :
  --   1. stepU_at_evC_code:   enter the C-wrapper, push  frmC1 , evaluate
  --      the middle child (the mu-loop primitive).
  --   2. stepU_at_evMu:       enter the mu-loop, push  frmM , evaluate
  --      the predicate  pFlip  at scan position 0.

  muStart : Term
  muStart = cfgEV (mcode1 pFlip) O
              (kons (frmM (mcode1 pFlip) O)
                (kons (frmC1 (mcode2 gPost) (mcode1 u) O) konEmpty))

  ----------------------------------------------------------------------
  -- Closure facts (ClosedAtVar 5) for the configs in the setup chain.
  -- var 5 is the internal iter_add_term variable; everything we build is
  -- closed at it.

  cav_muProg : ClosedAtVar 5 muProg
  cav_muProg =
    cav_ap2 5 pi (natCode tag_C)
      (ap2 pi (mcode2 gPost) (ap2 pi (mcodeMu (mcode1 pFlip)) (mcode1 u)))
      (cav_natCode 5 tag_C)
      (cav_ap2 5 pi (mcode2 gPost)
                  (ap2 pi (mcodeMu (mcode1 pFlip)) (mcode1 u))
        (cav_mcode2 5 gPost)
        (cav_ap2 5 pi (mcodeMu (mcode1 pFlip)) (mcode1 u)
          (cav_mcodeMu 5 (mcode1 pFlip) (cav_mcode1 5 pFlip))
          (cav_mcode1 5 u)))

  cav_after1 : ClosedAtVar 5
    (cfgEV (mcodeMu (mcode1 pFlip)) O
       (kons (frmC1 (mcode2 gPost) (mcode1 u) O) konEmpty))
  cav_after1 =
    cav_cfgEV 5 (mcodeMu (mcode1 pFlip)) O
      (kons (frmC1 (mcode2 gPost) (mcode1 u) O) konEmpty)
      (cav_mcodeMu 5 (mcode1 pFlip) (cav_mcode1 5 pFlip))
      (cav_O 5)
      (cav_kons 5 (frmC1 (mcode2 gPost) (mcode1 u) O) konEmpty
        (cav_frmC1 5 (mcode2 gPost) (mcode1 u) O
          (cav_mcode2 5 gPost) (cav_mcode1 5 u) (cav_O 5))
        (cav_konEmpty 5))

  cav_cfgInit : ClosedAtVar 5 (cfgEV muProg O konEmpty)
  cav_cfgInit =
    cav_cfgEV 5 muProg O konEmpty cav_muProg (cav_O 5) (cav_konEmpty 5)

  setupReach : TReaches (cfgEV muProg O konEmpty) muStart
  setupReach =
    let after1 : Term
        after1 = cfgEV (mcodeMu (mcode1 pFlip)) O
                   (kons (frmC1 (mcode2 gPost) (mcode1 u) O) konEmpty)
        step1 : TReaches (cfgEV muProg O konEmpty) after1
        step1 = treach_step1
          (stepU_at_evC_code (mcode2 gPost) (mcodeMu (mcode1 pFlip))
                              (mcode1 u) O konEmpty)
        step2 : TReaches after1 muStart
        step2 = treach_step1
          (stepU_at_evMu (mcode1 pFlip) O
            (kons (frmC1 (mcode2 gPost) (mcode1 u) O) konEmpty))
    in treach_trans cav_cfgInit step1 step2

  ----------------------------------------------------------------------
  -- Named substacks for the configs in Sections D-G.

  KCleanup : Term
  KCleanup = kons (frmC1 (mcode2 gPost) (mcode1 u) O) konEmpty

  KFull : Term -> Term
  KFull k = kons (frmM (mcode1 pFlip) k) KCleanup

  cfgAt : Term -> Term
  cfgAt k = cfgEV (mcode1 pFlip) k (KFull k)

  cav_KCleanup : ClosedAtVar 5 KCleanup
  cav_KCleanup =
    cav_kons 5 (frmC1 (mcode2 gPost) (mcode1 u) O) konEmpty
      (cav_frmC1 5 (mcode2 gPost) (mcode1 u) O
        (cav_mcode2 5 gPost) (cav_mcode1 5 u) (cav_O 5))
      (cav_konEmpty 5)

  cav_KFull : (k : Term) -> ClosedAtVar 5 k -> ClosedAtVar 5 (KFull k)
  cav_KFull k ck =
    cav_kons 5 (frmM (mcode1 pFlip) k) KCleanup
      (cav_frmM 5 (mcode1 pFlip) k (cav_mcode1 5 pFlip) ck)
      cav_KCleanup

  cav_cfgAt : (k : Term) -> ClosedAtVar 5 k -> ClosedAtVar 5 (cfgAt k)
  cav_cfgAt k ck =
    cav_cfgEV 5 (mcode1 pFlip) k (KFull k)
      (cav_mcode1 5 pFlip) ck (cav_KFull k ck)


  ----------------------------------------------------------------------
  -- Closed instances (= for-all-vars closure) needed by ObjLoop.

  cl_z : Closed z
  cl_z = record { closedAt = \ k b -> cavSubst (cav_z_at k) b }

  cl_mcode1_pFlip : Closed (mcode1 pFlip)
  cl_mcode1_pFlip =
    record { closedAt = \ k b -> cavSubst (cav_mcode1 k pFlip) b }

  cl_KCleanup : Closed KCleanup
  cl_KCleanup =
    record { closedAt = \ k b -> cavSubst (cav_KCleanup_at k) b }
    where
      cav_KCleanup_at : (k : Nat) -> ClosedAtVar k KCleanup
      cav_KCleanup_at k =
        cav_kons k (frmC1 (mcode2 gPost) (mcode1 u) O) konEmpty
          (cav_frmC1 k (mcode2 gPost) (mcode1 u) O
            (cav_mcode2 k gPost) (cav_mcode1 k u) (cav_O k))
          (cav_konEmpty k)

  ----------------------------------------------------------------------
  -- The nested module  WithEvals  takes the per-call evalU-fuel functions
  -- and corresponding Deriv-equations (the "running" content, analog of
  -- thm12's encoded computation-step counter), and packages the simulation
  -- theorem.  Internals are ObjLoop.Loop + ObjLoop.gLEvalObj.

  module WithEvals
    -- Per-iteration eval fuel as a Fun1 of the scan counter (analog of
    -- thm12's internal Sigma m(i) counter).
    (mPFlip : Fun1)
    -- The per-call evalU-fuel correctness witness.
    (pFlipRun :
       (r K : Term) ->
       Deriv (eqF (ap2 (iter stepU)
                    (cfgEV (mcode1 pFlip) r (kons (frmM (mcode1 pFlip) r) K))
                    (ap1 mPFlip r))
                  (cfgRT (ap1 pFlip r) (kons (frmM (mcode1 pFlip) r) K))))
    -- gPost's evalU-correctness:  evaluates  mcode2 gPost  at  (pi z O)
    -- to  ap2 gPost z O  in some fuel.
    (gPostFuel : Term)
    (gPostRun :
       Deriv (eqF (ap2 (iter stepU)
                    (cfgEV (mcode2 gPost) (ap2 pi z O) konEmpty)
                    gPostFuel)
                  (cfgRT (ap2 gPost z O) konEmpty)))
    where

    ----------------------------------------------------------------------
    -- Open ObjLoop.Loop at our parameters.

    open OL.Loop (mcode1 pFlip) cl_mcode1_pFlip
                 (\ r -> ap1 pFlip r)
                 mPFlip
                 pFlipRun
      using ( gLcodeOf ; gLEvalObj )

    ----------------------------------------------------------------------
    -- The main simulation theorem.
    --
    -- evalU  on the encoded mu-program (the muProg) reaches the post-
    -- transform's value  ap2 gPost z O  in a Term-determined fuel.

    muSimulation_correct :
      Sigma Term (\ n0 ->
        Deriv (eqF (ap2 evalU muProg n0) (ap1 s (ap2 gPost z O))))
    muSimulation_correct =
      let dEq : Deriv (eqF (ap2 evalU (gLcodeOf (mcode2 gPost)) _)
                            (ap1 s (ap2 gPost z O)))
          dEq = gLEvalObj (mcode2 gPost) z cl_z cl_KCleanup
                  pFlip_below pFlip_at_hit
                  (ap2 gPost z O) gPostFuel gPostRun
      in mkSigma _ dEq
