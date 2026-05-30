{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.StepU2CorrectRPeter -- R-case completeness for the Layer-1
-- universal interpreter, via the BRA4.PeterRec abstract induction
-- principle.
--
-- This file SUPERSEDES the Stack-motive specialisation in
-- BRA4/StepU2CorrectR.agda Sections 3-5.  Instead of building a custom
-- continuation Stack : Fun2 and proving a ruleIndNat 2 universal
-- theorem, we invoke PeterRec at a Fun2 combinator g_R_kons whose
-- recurrence g_R_kons (n, V) = pi (kons (frmApp2 h1c (h2 (Snd V) n)) (Fst V)) (Snd V)
-- preserves the user's x in V's Snd-position while building the
-- continuation in V's Fst-position.
--
-- Architecture (USER-FROZEN 2026-05-29):
--
--   * PeterRec saves the INDUCTION ARCHITECTURE, not the machine
--     algebra: the 7-segment R-step proof is still the same, but the
--     induction is now via PeterRec.PeterRec g_R_kons -- no Stack
--     bridge, no kappend, no continuation equivariance.
--
--   * x is packed into V via V := pi K x (var 1 := pi K x at bundle
--     time).  Inside the motive P, every reference to "x" is
--     ap1 Snd (var 1), and every reference to "K" is ap1 Fst (var 1).
--     At the bundle endpoint, ruleInst (var 1 := pi K x) and bridging
--     via axFst, axSnd recovers the standard Correct2 shape.
--
-- Construction of g_R_kons : Fun2  (12-layer Fan composition):
--
--   P_SndV         := Lift2 Snd                       -- (n, V) -> Snd V
--   P_FstV         := Lift2 Fst                       -- (n, V) -> Fst V
--   P_N            := Lift1 u                         -- (n, V) -> n
--   H2_call        := Fan P_SndV P_N h2               -- (n, V) -> h2 (Snd V) n
--   P_TAG          := Lift1 (constN tagApp2)          -- (n, V) -> natCode tagApp2
--   P_H1C          := Lift1 (constTermFun1 h1c)       -- (n, V) -> h1c
--   Inner          := Fan P_H1C H2_call pi            -- (n, V) -> pi h1c h2_call
--   Frame          := Fan P_TAG Inner pi              -- (n, V) -> frmApp2 h1c h2_call
--   FrameAndK      := Fan Frame P_FstV pi             -- (n, V) -> pi Frame (Fst V)
--   P_ONE          := Lift1 (constN 1)                -- (n, V) -> s O
--   NewK           := Fan P_ONE FrameAndK pi          -- (n, V) -> kons Frame (Fst V)
--   g_R_kons       := Fan NewK P_SndV pi              -- (n, V) -> pi NewK (Snd V)
--
-- The closed-form law g_R_kons-eq follows by chaining the Fan_eq /
-- Lift1_eq / Lift2_eq laws together with constN_eq, constTermFun1_eq
-- (using NoVar_h1c), and ax_u.

module BRA4.StepU2CorrectRPeter where

open import BRA4.Base
open import BRA4.StepU2
  using ( step
        ; stepU_at_evRbase ; stepU_at_evRstep
        ; stepU_at_rtR1 ; stepU_at_rtApp2
        ; cfgEV ; cfgRT ; kons ; frmApp2 ; frmR1
        ; mcode1 ; mcode2
        ; tagApp2 ; tagRT ; tagEV )
open import BRA4.StepU2Reach
  using ( iter_add_T )
open import BRA4.StepU2CorrectAPI
  using ( Correct1 ; Correct2 ; mkC1 ; mkC2
        ; fuelF ; fuelG ; runs1 ; runs2 )
open import BRA4.StepU2RStack
  using ( NoVar_mcode1 ; NoVar_mcode2 )
open import BRA4.StepU2PairFuelR using ()
open import BRA4.PeterRec using ( PeterRec )
open import BRA4.LoopReaches
  using ( ClosedAtVar ; mkCAV ; cavSubst
        ; cav_O ; cav_ap1 ; cav_ap2 ; cav_natCode )
open import BRA4.Tags
  using ( tag_s ; tag_o ; tag_u ; tag_C ; tag_v ; tag_R )

open import BRA4.Thm12.ConstTermFun1
  using ( NoVar ; constTermFun1 ; constTermFun1_eq )

open import BRA3.CourseOfValues
  using ( iter )

open import BRA3.Church
  using ( pi ; sub ; sigma )
open import BRA3.ChurchT117 using ( Fst )
open import BRA3.ChurchT116 using ( Snd )
open import BRA3.PairAlgebra
  using ( axFst ; axSnd ; Post ; axPost )
open import BRA3.Fan
  using ( Lift1 ; Lift1_eq ; Lift2 ; Lift2_eq ; Fan ; Fan_eq )
open import BRA3.Equational
  using ( axRefl ; ruleSym ; ruleTrans ; cong1 ; congL ; congR )
open import BRA3.RuleInst2  using ( ruleInst2 ; simSubstT ; simSubstF )
open import BRA3.Contrapositive
  using ( identP ; liftP ; bComb ; bCombTwo )
open import BRA3.Logic
  using ( impTrans ; prependEqLeft ; appendEqRight ; eqSymImp )
open import BRA3.RecBRA3AtPairUniv
  using ( iter_base_univ ; iter_step_univ )

------------------------------------------------------------------------
-- Section 1.  g_R_kons : Fun2  parametric in (h1, h2).
--
-- ap2 g_R_kons n V = pi (kons (frmApp2 h1c (h2 (Snd V) n)) (Fst V)) (Snd V)
-- where h1c = mcode2 h1.

module RKonsOf (h1 h2 : Fun2) where

  h1c : Term
  h1c = mcode2 h1

  NoVar_h1c : NoVar h1c
  NoVar_h1c = NoVar_mcode2 h1

  ----------------------------------------------------------------------
  -- Layer 1.  Projectors.

  P_SndV : Fun2
  P_SndV = Lift2 Snd

  P_FstV : Fun2
  P_FstV = Lift2 Fst

  P_N : Fun2
  P_N = Lift1 u

  P_TAG : Fun2
  P_TAG = Lift1 (constN tagApp2)

  P_H1C : Fun2
  P_H1C = Lift1 (constTermFun1 h1c)

  P_ONE : Fun2
  P_ONE = Lift1 (constN 1)

  ----------------------------------------------------------------------
  -- Layer 2.  H2_call.

  H2_call : Fun2
  H2_call = Fan P_SndV P_N h2

  ----------------------------------------------------------------------
  -- Layer 3.  Inner pi.

  Inner : Fun2
  Inner = Fan P_H1C H2_call pi

  ----------------------------------------------------------------------
  -- Layer 4.  Frame.

  Frame : Fun2
  Frame = Fan P_TAG Inner pi

  ----------------------------------------------------------------------
  -- Layer 5.  FrameAndK.

  FrameAndK : Fun2
  FrameAndK = Fan Frame P_FstV pi

  ----------------------------------------------------------------------
  -- Layer 6.  NewK.

  NewK : Fun2
  NewK = Fan P_ONE FrameAndK pi

  ----------------------------------------------------------------------
  -- Layer 7.  g_R_kons.

  g_R_kons : Fun2
  g_R_kons = Fan NewK P_SndV pi

  ----------------------------------------------------------------------
  -- Section 1b.  Equational laws for each layer.

  P_SndV-eq : (n V : Term) -> Deriv (eqF (ap2 P_SndV n V) (ap1 Snd V))
  P_SndV-eq n V = Lift2_eq Snd n V

  P_FstV-eq : (n V : Term) -> Deriv (eqF (ap2 P_FstV n V) (ap1 Fst V))
  P_FstV-eq n V = Lift2_eq Fst n V

  P_N-eq : (n V : Term) -> Deriv (eqF (ap2 P_N n V) n)
  P_N-eq n V = ruleTrans (Lift1_eq u n V) (ax_u n)

  P_TAG-eq : (n V : Term) -> Deriv (eqF (ap2 P_TAG n V) (natCode tagApp2))
  P_TAG-eq n V = ruleTrans (Lift1_eq (constN tagApp2) n V) (constN_eq tagApp2 n)

  P_H1C-eq : (n V : Term) -> Deriv (eqF (ap2 P_H1C n V) h1c)
  P_H1C-eq n V =
    ruleTrans (Lift1_eq (constTermFun1 h1c) n V)
               (constTermFun1_eq h1c NoVar_h1c n)

  P_ONE-eq : (n V : Term) -> Deriv (eqF (ap2 P_ONE n V) (ap1 s O))
  P_ONE-eq n V = ruleTrans (Lift1_eq (constN 1) n V) (constN_eq 1 n)

  ----------------------------------------------------------------------

  H2_call-eq : (n V : Term) ->
    Deriv (eqF (ap2 H2_call n V) (ap2 h2 (ap1 Snd V) n))
  H2_call-eq n V =
    let e1 : Deriv (eqF (ap2 H2_call n V)
                         (ap2 h2 (ap2 P_SndV n V) (ap2 P_N n V)))
        e1 = Fan_eq P_SndV P_N h2 n V
        e2 : Deriv (eqF (ap2 h2 (ap2 P_SndV n V) (ap2 P_N n V))
                         (ap2 h2 (ap1 Snd V) n))
        e2 = ruleTrans (congL h2 (ap2 P_N n V) (P_SndV-eq n V))
                        (congR h2 (ap1 Snd V) (P_N-eq n V))
    in ruleTrans e1 e2

  Inner-eq : (n V : Term) ->
    Deriv (eqF (ap2 Inner n V)
                (ap2 pi h1c (ap2 h2 (ap1 Snd V) n)))
  Inner-eq n V =
    let e1 : Deriv (eqF (ap2 Inner n V)
                         (ap2 pi (ap2 P_H1C n V) (ap2 H2_call n V)))
        e1 = Fan_eq P_H1C H2_call pi n V
        e2 : Deriv (eqF (ap2 pi (ap2 P_H1C n V) (ap2 H2_call n V))
                         (ap2 pi h1c (ap2 h2 (ap1 Snd V) n)))
        e2 = ruleTrans (congL pi (ap2 H2_call n V) (P_H1C-eq n V))
                        (congR pi h1c (H2_call-eq n V))
    in ruleTrans e1 e2

  Frame-eq : (n V : Term) ->
    Deriv (eqF (ap2 Frame n V)
                (frmApp2 h1c (ap2 h2 (ap1 Snd V) n)))
  Frame-eq n V =
    let e1 : Deriv (eqF (ap2 Frame n V)
                         (ap2 pi (ap2 P_TAG n V) (ap2 Inner n V)))
        e1 = Fan_eq P_TAG Inner pi n V
        e2 : Deriv (eqF (ap2 pi (ap2 P_TAG n V) (ap2 Inner n V))
                         (ap2 pi (natCode tagApp2) (ap2 pi h1c (ap2 h2 (ap1 Snd V) n))))
        e2 = ruleTrans (congL pi (ap2 Inner n V) (P_TAG-eq n V))
                        (congR pi (natCode tagApp2) (Inner-eq n V))
    in ruleTrans e1 e2

  FrameAndK-eq : (n V : Term) ->
    Deriv (eqF (ap2 FrameAndK n V)
                (ap2 pi (frmApp2 h1c (ap2 h2 (ap1 Snd V) n)) (ap1 Fst V)))
  FrameAndK-eq n V =
    let e1 : Deriv (eqF (ap2 FrameAndK n V)
                         (ap2 pi (ap2 Frame n V) (ap2 P_FstV n V)))
        e1 = Fan_eq Frame P_FstV pi n V
        e2 : Deriv (eqF (ap2 pi (ap2 Frame n V) (ap2 P_FstV n V))
                         (ap2 pi (frmApp2 h1c (ap2 h2 (ap1 Snd V) n)) (ap1 Fst V)))
        e2 = ruleTrans (congL pi (ap2 P_FstV n V) (Frame-eq n V))
                        (congR pi (frmApp2 h1c (ap2 h2 (ap1 Snd V) n)) (P_FstV-eq n V))
    in ruleTrans e1 e2

  NewK-eq : (n V : Term) ->
    Deriv (eqF (ap2 NewK n V)
                (kons (frmApp2 h1c (ap2 h2 (ap1 Snd V) n)) (ap1 Fst V)))
  NewK-eq n V =
    let e1 : Deriv (eqF (ap2 NewK n V)
                         (ap2 pi (ap2 P_ONE n V) (ap2 FrameAndK n V)))
        e1 = Fan_eq P_ONE FrameAndK pi n V
        e2 : Deriv (eqF (ap2 pi (ap2 P_ONE n V) (ap2 FrameAndK n V))
                         (ap2 pi (ap1 s O)
                                  (ap2 pi (frmApp2 h1c (ap2 h2 (ap1 Snd V) n)) (ap1 Fst V))))
        e2 = ruleTrans (congL pi (ap2 FrameAndK n V) (P_ONE-eq n V))
                        (congR pi (ap1 s O) (FrameAndK-eq n V))
    in ruleTrans e1 e2

  g_R_kons-eq : (n V : Term) ->
    Deriv (eqF (ap2 g_R_kons n V)
                (ap2 pi (kons (frmApp2 h1c (ap2 h2 (ap1 Snd V) n)) (ap1 Fst V))
                         (ap1 Snd V)))
  g_R_kons-eq n V =
    let e1 : Deriv (eqF (ap2 g_R_kons n V)
                         (ap2 pi (ap2 NewK n V) (ap2 P_SndV n V)))
        e1 = Fan_eq NewK P_SndV pi n V
        e2 : Deriv (eqF (ap2 pi (ap2 NewK n V) (ap2 P_SndV n V))
                         (ap2 pi (kons (frmApp2 h1c (ap2 h2 (ap1 Snd V) n)) (ap1 Fst V))
                                  (ap1 Snd V)))
        e2 = ruleTrans (congL pi (ap2 P_SndV n V) (NewK-eq n V))
                        (congR pi (kons (frmApp2 h1c (ap2 h2 (ap1 Snd V) n)) (ap1 Fst V))
                                 (P_SndV-eq n V))
    in ruleTrans e1 e2

  ----------------------------------------------------------------------
  -- Section 1c.  Derived projection-of-g_R_kons laws.
  --
  --   Snd (g_R_kons n V) = Snd V                                    (eq_Snd_g)
  --   Fst (g_R_kons n V) = kons (frmApp2 h1c (h2 (Snd V) n)) (Fst V) (eq_Fst_g)

  eq_Snd_g : (n V : Term) ->
    Deriv (eqF (ap1 Snd (ap2 g_R_kons n V)) (ap1 Snd V))
  eq_Snd_g n V =
    ruleTrans (cong1 Snd (g_R_kons-eq n V))
               (axSnd (kons (frmApp2 h1c (ap2 h2 (ap1 Snd V) n)) (ap1 Fst V))
                       (ap1 Snd V))

  eq_Fst_g : (n V : Term) ->
    Deriv (eqF (ap1 Fst (ap2 g_R_kons n V))
                (kons (frmApp2 h1c (ap2 h2 (ap1 Snd V) n)) (ap1 Fst V)))
  eq_Fst_g n V =
    ruleTrans (cong1 Fst (g_R_kons-eq n V))
               (axFst (kons (frmApp2 h1c (ap2 h2 (ap1 Snd V) n)) (ap1 Fst V))
                       (ap1 Snd V))

------------------------------------------------------------------------
-- Section 2.  The R-case proof via PeterRec.

module Construct
  (g : Fun1) (h1 h2 : Fun2)
  (bG : Correct1 g) (bH1 : Correct2 h1) (bH2 : Correct2 h2)
  where

  open RKonsOf h1 h2
    using ( h1c ; NoVar_h1c ; g_R_kons ; g_R_kons-eq ; eq_Snd_g ; eq_Fst_g )

  open BRA4.StepU2PairFuelR.Construct g h1 h2 bG bH1 bH2
    using ( paired_R ; fuelR_combinator ; fG ; fH1 ; fH2
          ; F3 ; fuel_next_Fun2
          ; Snd_paired_R_eq ; Fst_paired_R_eq
          ; Snd_paired_R_at_O ; Snd_paired_R_at_s )

  ----------------------------------------------------------------------
  -- Section 2a.  Local helpers.

  -- Equational transitivity under one implication layer.
  transUnderOne :
    {P : Formula} {a b c : Term} ->
    Deriv (imp P (eqF a b)) ->
    Deriv (imp P (eqF b c)) ->
    Deriv (imp P (eqF a c))
  transUnderOne {P} {a} {b} {c} D1 D2 =
    let lift_trans : Deriv (imp P (imp (eqF b a) (imp (eqF b c) (eqF a c))))
        lift_trans = liftP P (ax_eqTrans b a c)
        lift_eqSym : Deriv (imp P (imp (eqF a b) (eqF b a)))
        lift_eqSym = liftP P (eqSymImp a b)
        symD1 : Deriv (imp P (eqF b a))
        symD1 = bComb lift_eqSym D1
        step1 : Deriv (imp P (imp (eqF b c) (eqF a c)))
        step1 = bComb lift_trans symD1
    in bComb step1 D2

  cfgRT-val-rw : (val val' K : Term) ->
                  Deriv (eqF val val') ->
                  Deriv (eqF (cfgRT val K) (cfgRT val' K))
  cfgRT-val-rw val val' K e = congR pi (natCode tagRT) (congL pi K e)

  cfgRT-kont-rw : (val K K' : Term) ->
                   Deriv (eqF K K') ->
                   Deriv (eqF (cfgRT val K) (cfgRT val K'))
  cfgRT-kont-rw val K K' e = congR pi (natCode tagRT) (congR pi val e)

  cfgEV-kont-rw : (fc a K K' : Term) ->
                   Deriv (eqF K K') ->
                   Deriv (eqF (cfgEV fc a K) (cfgEV fc a K'))
  cfgEV-kont-rw fc a K K' e =
    congR pi (natCode tagEV) (congR pi (ap2 pi fc a) e)

  cfgEV-arg-rw : (fc a a' K : Term) ->
                  Deriv (eqF a a') ->
                  Deriv (eqF (cfgEV fc a K) (cfgEV fc a' K))
  cfgEV-arg-rw fc a a' K e =
    congR pi (natCode tagEV) (congL pi K (congR pi fc e))

  -- One step of iter: from "step c = c'" derive "iter step c (s O) = c'".
  iter-step1 : (c c' : Term) ->
                Deriv (eqF (ap1 step c) c') ->
                Deriv (eqF (ap2 (iter step) c (ap1 s O)) c')
  iter-step1 c c' e =
    let e1 = iter_step_univ step c O
        e2 = cong1 step (iter_base_univ step c)
    in ruleTrans e1 (ruleTrans e2 e)

  ----------------------------------------------------------------------
  -- Section 2b.  ClosedAtVar witnesses for mcode1 / mcode2 and Rc.

  cav-mcode1 : (k : Nat) (f : Fun1) -> ClosedAtVar k (mcode1 f)
  cav-mcode2 : (k : Nat) (g' : Fun2) -> ClosedAtVar k (mcode2 g')

  cav-mcode1 k s =
    cav_ap2 k pi (natCode tag_s) O (cav_natCode k tag_s) (cav_O k)
  cav-mcode1 k o =
    cav_ap2 k pi (natCode tag_o) O (cav_natCode k tag_o) (cav_O k)
  cav-mcode1 k u =
    cav_ap2 k pi (natCode tag_u) O (cav_natCode k tag_u) (cav_O k)
  cav-mcode1 k (C g' h1' h2') =
    cav_ap2 k pi (natCode tag_C)
      (ap2 pi (mcode2 g') (ap2 pi (mcode1 h1') (mcode1 h2')))
      (cav_natCode k tag_C)
      (cav_ap2 k pi (mcode2 g') (ap2 pi (mcode1 h1') (mcode1 h2'))
        (cav-mcode2 k g')
        (cav_ap2 k pi (mcode1 h1') (mcode1 h2')
          (cav-mcode1 k h1') (cav-mcode1 k h2')))

  cav-mcode2 k v =
    cav_ap2 k pi (natCode tag_v) O (cav_natCode k tag_v) (cav_O k)
  cav-mcode2 k (R g' h1' h2') =
    cav_ap2 k pi (natCode tag_R)
      (ap2 pi (mcode1 g') (ap2 pi (mcode2 h1') (mcode2 h2')))
      (cav_natCode k tag_R)
      (cav_ap2 k pi (mcode1 g') (ap2 pi (mcode2 h1') (mcode2 h2'))
        (cav-mcode1 k g')
        (cav_ap2 k pi (mcode2 h1') (mcode2 h2')
          (cav-mcode2 k h1') (cav-mcode2 k h2')))

  Rc : Term
  Rc = mcode2 (R g h1 h2)

  cav-Rc-0 : ClosedAtVar zero Rc
  cav-Rc-0 = cav-mcode2 zero (R g h1 h2)

  cav-Rc-1 : ClosedAtVar (suc zero) Rc
  cav-Rc-1 = cav-mcode2 (suc zero) (R g h1 h2)

  eq-Rc-0 : Eq (substT zero O Rc) Rc
  eq-Rc-0 = cavSubst cav-Rc-0 O

  eq-Rc-1 : (a : Term) -> Eq (substT (suc zero) a Rc) Rc
  eq-Rc-1 a = cavSubst cav-Rc-1 a

  ----------------------------------------------------------------------
  -- Section 2b'.  simSubstT closedness lemmas for mcode1 / mcode2.
  --
  -- For any (y, Vxy), simSubstT 0 y 1 Vxy (mcode2 (R g h1 h2)) = mcode2 (R g h1 h2)
  -- since mcode2 produces a closed Term (no var occurrences).
  --
  -- Built by mirroring cav-mcode1/cav-mcode2 with simSubstT instead of
  -- substT.

  sim-natCode : (a b : Term) (k : Nat) ->
    Eq (simSubstT zero a (suc zero) b (natCode k)) (natCode k)
  sim-natCode a b zero    = refl
  sim-natCode a b (suc k) = eqCong (ap1 s) (sim-natCode a b k)

  sim-mcode1 : (a b : Term) (f : Fun1) ->
    Eq (simSubstT zero a (suc zero) b (mcode1 f)) (mcode1 f)
  sim-mcode2 : (a b : Term) (g' : Fun2) ->
    Eq (simSubstT zero a (suc zero) b (mcode2 g')) (mcode2 g')

  sim-mcode1 a b s =
    eqCong (\ t -> ap2 pi t O) (sim-natCode a b tag_s)
  sim-mcode1 a b o =
    eqCong (\ t -> ap2 pi t O) (sim-natCode a b tag_o)
  sim-mcode1 a b u =
    eqCong (\ t -> ap2 pi t O) (sim-natCode a b tag_u)
  sim-mcode1 a b (C g' h1' h2') =
    eqTrans
      (eqCong (\ t -> ap2 pi t
                          (ap2 pi (simSubstT zero a (suc zero) b (mcode2 g'))
                                   (ap2 pi (simSubstT zero a (suc zero) b (mcode1 h1'))
                                            (simSubstT zero a (suc zero) b (mcode1 h2')))))
              (sim-natCode a b tag_C))
      (eqTrans
        (eqCong (\ t -> ap2 pi (natCode tag_C)
                                (ap2 pi t
                                        (ap2 pi (simSubstT zero a (suc zero) b (mcode1 h1'))
                                                (simSubstT zero a (suc zero) b (mcode1 h2')))))
                (sim-mcode2 a b g'))
        (eqTrans
          (eqCong (\ t -> ap2 pi (natCode tag_C)
                                  (ap2 pi (mcode2 g')
                                          (ap2 pi t
                                                  (simSubstT zero a (suc zero) b (mcode1 h2')))))
                  (sim-mcode1 a b h1'))
          (eqCong (\ t -> ap2 pi (natCode tag_C)
                                  (ap2 pi (mcode2 g')
                                          (ap2 pi (mcode1 h1') t)))
                  (sim-mcode1 a b h2'))))

  sim-mcode2 a b v =
    eqCong (\ t -> ap2 pi t O) (sim-natCode a b tag_v)
  sim-mcode2 a b (R g' h1' h2') =
    eqTrans
      (eqCong (\ t -> ap2 pi t
                          (ap2 pi (simSubstT zero a (suc zero) b (mcode1 g'))
                                   (ap2 pi (simSubstT zero a (suc zero) b (mcode2 h1'))
                                            (simSubstT zero a (suc zero) b (mcode2 h2')))))
              (sim-natCode a b tag_R))
      (eqTrans
        (eqCong (\ t -> ap2 pi (natCode tag_R)
                                (ap2 pi t
                                        (ap2 pi (simSubstT zero a (suc zero) b (mcode2 h1'))
                                                (simSubstT zero a (suc zero) b (mcode2 h2')))))
                (sim-mcode1 a b g'))
        (eqTrans
          (eqCong (\ t -> ap2 pi (natCode tag_R)
                                  (ap2 pi (mcode1 g')
                                          (ap2 pi t
                                                  (simSubstT zero a (suc zero) b (mcode2 h2')))))
                  (sim-mcode2 a b h1'))
          (eqCong (\ t -> ap2 pi (natCode tag_R)
                                  (ap2 pi (mcode1 g')
                                          (ap2 pi (mcode2 h1') t)))
                  (sim-mcode2 a b h2'))))

  sim-Rc : (a b : Term) ->
    Eq (simSubstT zero a (suc zero) b Rc) Rc
  sim-Rc a b = sim-mcode2 a b (R g h1 h2)

  ----------------------------------------------------------------------
  -- Section 2c.  fuel_next_Fun2 unfolding -- copied from
  -- BRA4.StepU2CorrectR Section 4c (parametric in X = "x", N = "y", so we
  -- use X, N instead of x, y to avoid name collisions).
  --
  -- ap2 fuel_next_Fun2 (F3 X N) (paired_R X N)
  --   = sigma (sigma (sigma (sigma (sigma (s O) (fH2 X N)) (s O))
  --                          (fuelR_combinator X N)) (s O))
  --           (fH1 (h2 X N) (R g h1 h2 X N))

  fuel-next-unfold : (X N : Term) ->
    Deriv (eqF (ap2 fuel_next_Fun2 (ap2 F3 X N) (ap2 paired_R X N))
                (ap2 sigma
                    (ap2 sigma
                      (ap2 sigma
                        (ap2 sigma
                          (ap2 sigma (ap1 s O) (ap2 fH2 X N))
                          (ap1 s O))
                        (ap2 fuelR_combinator X N))
                      (ap1 s O))
                    (ap2 fH1 (ap2 h2 X N) (ap2 (R g h1 h2) X N))))
  fuel-next-unfold X N =
    let A : Term
        A = ap2 F3 X N
        B : Term
        B = ap2 paired_R X N
        oneT : Term
        oneT = ap1 s O
        fh2v : Term
        fh2v = ap2 fH2 X N
        fuelR_xy : Term
        fuelR_xy = ap2 fuelR_combinator X N
        h2v : Term
        h2v = ap2 h2 X N
        Rxy : Term
        Rxy = ap2 (R g h1 h2) X N
        fh1v : Term
        fh1v = ap2 fH1 h2v Rxy

        A_pi : Deriv (eqF A (ap2 pi h2v fh2v))
        A_pi = Fan_eq h2 fH2 pi X N

        SndA : Deriv (eqF (ap1 Snd A) fh2v)
        SndA = ruleTrans (cong1 Snd A_pi) (axSnd h2v fh2v)

        FstA : Deriv (eqF (ap1 Fst A) h2v)
        FstA = ruleTrans (cong1 Fst A_pi) (axFst h2v fh2v)

        SndB : Deriv (eqF (ap1 Snd B) fuelR_xy)
        SndB = Snd_paired_R_eq X N

        FstB : Deriv (eqF (ap1 Fst B) Rxy)
        FstB = Fst_paired_R_eq X N

        eOne : Deriv (eqF (ap2 (Lift2 (constN 1)) A B) oneT)
        eOne = ruleTrans (Lift2_eq (constN 1) A B) (constN_eq 1 B)

        eFH2 : Deriv (eqF (ap2 (Lift1 Snd) A B) fh2v)
        eFH2 = ruleTrans (Lift1_eq Snd A B) SndA

        eFP : Deriv (eqF (ap2 (Lift2 Snd) A B) fuelR_xy)
        eFP = ruleTrans (Lift2_eq Snd A B) SndB

        eFH1 : Deriv (eqF (ap2 (Fan (Lift1 Fst) (Lift2 Fst) fH1) A B) fh1v)
        eFH1 =
          let e1 : Deriv (eqF (ap2 (Fan (Lift1 Fst) (Lift2 Fst) fH1) A B)
                                (ap2 fH1 (ap2 (Lift1 Fst) A B) (ap2 (Lift2 Fst) A B)))
              e1 = Fan_eq (Lift1 Fst) (Lift2 Fst) fH1 A B
              eL1 : Deriv (eqF (ap2 (Lift1 Fst) A B) h2v)
              eL1 = ruleTrans (Lift1_eq Fst A B) FstA
              eL2 : Deriv (eqF (ap2 (Lift2 Fst) A B) Rxy)
              eL2 = ruleTrans (Lift2_eq Fst A B) FstB
              e2 : Deriv (eqF (ap2 fH1 (ap2 (Lift1 Fst) A B) (ap2 (Lift2 Fst) A B))
                                fh1v)
              e2 = ruleTrans (congL fH1 (ap2 (Lift2 Fst) A B) eL1)
                              (congR fH1 h2v eL2)
          in ruleTrans e1 e2

        L1_target : Term
        L1_target = ap2 sigma oneT fh2v

        eL1 :
          Deriv (eqF (ap2 (Fan (Lift2 (constN 1)) (Lift1 Snd) sigma) A B)
                      L1_target)
        eL1 =
          let e1 = Fan_eq (Lift2 (constN 1)) (Lift1 Snd) sigma A B
              e2 = ruleTrans (congL sigma (ap2 (Lift1 Snd) A B) eOne)
                              (congR sigma oneT eFH2)
          in ruleTrans e1 e2

        L2_target : Term
        L2_target = ap2 sigma L1_target oneT

        eL2 :
          Deriv (eqF (ap2 (Fan (Fan (Lift2 (constN 1)) (Lift1 Snd) sigma)
                                 (Lift2 (constN 1)) sigma) A B)
                      L2_target)
        eL2 =
          let e1 = Fan_eq (Fan (Lift2 (constN 1)) (Lift1 Snd) sigma)
                            (Lift2 (constN 1)) sigma A B
              e2 = ruleTrans (congL sigma (ap2 (Lift2 (constN 1)) A B) eL1)
                              (congR sigma L1_target eOne)
          in ruleTrans e1 e2

        L3_target : Term
        L3_target = ap2 sigma L2_target fuelR_xy

        eL3 :
          Deriv (eqF (ap2 (Fan (Fan (Fan (Lift2 (constN 1)) (Lift1 Snd) sigma)
                                       (Lift2 (constN 1)) sigma)
                                 (Lift2 Snd) sigma) A B)
                      L3_target)
        eL3 =
          let e1 = Fan_eq (Fan (Fan (Lift2 (constN 1)) (Lift1 Snd) sigma)
                                 (Lift2 (constN 1)) sigma)
                            (Lift2 Snd) sigma A B
              e2 = ruleTrans (congL sigma (ap2 (Lift2 Snd) A B) eL2)
                              (congR sigma L2_target eFP)
          in ruleTrans e1 e2

        L4_target : Term
        L4_target = ap2 sigma L3_target oneT

        eL4 :
          Deriv (eqF (ap2 (Fan
                              (Fan (Fan (Fan (Lift2 (constN 1)) (Lift1 Snd) sigma)
                                        (Lift2 (constN 1)) sigma)
                                   (Lift2 Snd) sigma)
                              (Lift2 (constN 1)) sigma) A B)
                      L4_target)
        eL4 =
          let e1 = Fan_eq (Fan (Fan (Fan (Lift2 (constN 1)) (Lift1 Snd) sigma)
                                        (Lift2 (constN 1)) sigma)
                                 (Lift2 Snd) sigma)
                            (Lift2 (constN 1)) sigma A B
              e2 = ruleTrans (congL sigma (ap2 (Lift2 (constN 1)) A B) eL3)
                              (congR sigma L3_target eOne)
          in ruleTrans e1 e2

        L5_target : Term
        L5_target = ap2 sigma L4_target fh1v

        eL5 :
          Deriv (eqF (ap2 fuel_next_Fun2 A B) L5_target)
        eL5 =
          let e1 = Fan_eq (Fan
                              (Fan (Fan (Fan (Lift2 (constN 1)) (Lift1 Snd) sigma)
                                        (Lift2 (constN 1)) sigma)
                                   (Lift2 Snd) sigma)
                              (Lift2 (constN 1)) sigma)
                            (Fan (Lift1 Fst) (Lift2 Fst) fH1)
                            sigma A B
              e2 = ruleTrans (congL sigma (ap2 (Fan (Lift1 Fst) (Lift2 Fst) fH1) A B)
                                       eL4)
                              (congR sigma L4_target eFH1)
          in ruleTrans e1 e2

    in eL5

  ----------------------------------------------------------------------
  -- Section 2d.  The motive P (with var 0 = y_current, var 1 = V).
  --
  -- V := var 1 packages (K_outer, x_param):  Fst V = K_outer, Snd V = x_param.
  -- At bundle time, ruleInst (var 1 := pi K x) recovers the user-supplied
  -- (x, K) pair.

  N : Term
  N = var zero

  V : Term
  V = var (suc zero)

  X : Term
  X = ap1 Snd V

  K : Term
  K = ap1 Fst V

  P : Formula
  P =
    eqF (ap2 (iter step) (cfgEV Rc (ap2 pi X N) K)
              (ap2 fuelR_combinator X N))
        (cfgRT (ap2 (R g h1 h2) X N) K)

  ----------------------------------------------------------------------
  -- Section 2e.  premiseB -- Deriv (substF 0 O P).
  --
  -- substF 0 O P substitutes var 0 (= N) by O.  Since X, K, Rc are
  -- free of var 0, the result reduces to the operational base case
  -- target at (X, O, K).

  premiseB : Deriv (substF zero O P)
  premiseB =
    let cInit : Term
        cInit = cfgEV Rc (ap2 pi X O) K
        cMid : Term
        cMid = cfgEV (mcode1 g) X K
        cAfterG : Term
        cAfterG = cfgRT (ap1 g X) K
        cFinal : Term
        cFinal = cfgRT (ap2 (R g h1 h2) X O) K

        oneT : Term
        oneT = ap1 s O

        -- Run segment 1: stepU_at_evRbase.
        step1 : Deriv (eqF (ap1 step cInit) cMid)
        step1 = stepU_at_evRbase g h1 h2 X K

        run1 : Deriv (eqF (ap2 (iter step) cInit oneT) cMid)
        run1 = iter-step1 cInit cMid step1

        -- Run segment 2: bG.runs1 X K.
        runG : Deriv (eqF (ap2 (iter step) cMid (ap1 fG X)) cAfterG)
        runG = runs1 bG X K

        fuel12 : Term
        fuel12 = ap2 sigma oneT (ap1 fG X)

        run12 : Deriv (eqF (ap2 (iter step) cInit fuel12) cAfterG)
        run12 =
          ruleTrans (iter_add_T cInit oneT (ap1 fG X))
            (ruleTrans (congL (iter step) (ap1 fG X) run1) runG)

        -- Rewrite value cAfterG -> cFinal.
        eVal : Deriv (eqF (ap1 g X) (ap2 (R g h1 h2) X O))
        eVal = ruleSym (ax_R_base g h1 h2 X)

        eRT : Deriv (eqF cAfterG cFinal)
        eRT = cfgRT-val-rw (ap1 g X) (ap2 (R g h1 h2) X O) K eVal

        run12_val : Deriv (eqF (ap2 (iter step) cInit fuel12) cFinal)
        run12_val = ruleTrans run12 eRT

        -- Rewrite fuel: fuel12 -> ap2 fuelR_combinator X O.
        eFuel1 : Deriv (eqF (ap1 (constN 1) X) (ap1 s O))
        eFuel1 = constN_eq 1 X

        eFuel2 : Deriv (eqF fuel12 (ap2 sigma (ap1 (constN 1) X) (ap1 fG X)))
        eFuel2 = congL sigma (ap1 fG X) (ruleSym eFuel1)

        eFuel3 : Deriv (eqF (ap2 sigma (ap1 (constN 1) X) (ap1 fG X))
                             (ap1 Snd (ap2 paired_R X O)))
        eFuel3 = ruleSym (Snd_paired_R_at_O X)

        eFuel4 : Deriv (eqF (ap1 Snd (ap2 paired_R X O))
                             (ap2 fuelR_combinator X O))
        eFuel4 = Snd_paired_R_eq X O

        eFuel : Deriv (eqF fuel12 (ap2 fuelR_combinator X O))
        eFuel = ruleTrans eFuel2 (ruleTrans eFuel3 eFuel4)

        eFuel_iter :
          Deriv (eqF (ap2 (iter step) cInit fuel12)
                      (ap2 (iter step) cInit (ap2 fuelR_combinator X O)))
        eFuel_iter = congR (iter step) cInit eFuel

        conclusion :
          Deriv (eqF (ap2 (iter step) cInit (ap2 fuelR_combinator X O)) cFinal)
        conclusion = ruleTrans (ruleSym eFuel_iter) run12_val

        -- Bridge:  substF 0 O P  has  substT 0 O Rc  in place of  Rc .
        -- Since Rc is closed at var 0 (cav-Rc-0), they are equal.

        Pred-B : Term -> Set
        Pred-B rc =
          Deriv (eqF (ap2 (iter step) (cfgEV rc (ap2 pi X O) K)
                            (ap2 fuelR_combinator X O))
                      cFinal)

    in eqSubst Pred-B (eqSym eq-Rc-0) conclusion

  ----------------------------------------------------------------------
  -- Section 2f.  premiseS -- the 7-segment R-step proof.

  premiseS : Deriv (imp (substF (suc zero) (ap2 g_R_kons N V) P)
                         (substF zero (ap1 s N) P))
  premiseS =
    let
        ----------------------------------------------------------------
        -- Notation.

        sN : Term
        sN = ap1 s N

        gV : Term
        gV = ap2 g_R_kons N V

        Sgv : Term         -- Hyp's "x".
        Sgv = ap1 Snd gV

        Fgv : Term         -- Hyp's "K".
        Fgv = ap1 Fst gV

        konsForm : Term
        konsForm = kons (frmApp2 h1c (ap2 h2 X N)) K

        ----------------------------------------------------------------
        -- Equational bridges between (Sgv, Fgv) and (X, konsForm).

        eq-Sgv : Deriv (eqF Sgv X)
        eq-Sgv = eq_Snd_g N V

        eq-Fgv : Deriv (eqF Fgv konsForm)
        eq-Fgv = eq_Fst_g N V

        ----------------------------------------------------------------
        -- "Clean" forms of the Hyp and Concl.

        HypClean-LHS : Term
        HypClean-LHS = ap2 (iter step) (cfgEV Rc (ap2 pi X N) konsForm)
                                       (ap2 fuelR_combinator X N)

        HypClean-RHS : Term
        HypClean-RHS = cfgRT (ap2 (R g h1 h2) X N) konsForm

        HypClean : Formula
        HypClean = eqF HypClean-LHS HypClean-RHS

        ConclClean-LHS : Term
        ConclClean-LHS = ap2 (iter step) (cfgEV Rc (ap2 pi X sN) K)
                                          (ap2 fuelR_combinator X sN)

        ConclClean-RHS : Term
        ConclClean-RHS = cfgRT (ap2 (R g h1 h2) X sN) K

        ConclClean : Formula
        ConclClean = eqF ConclClean-LHS ConclClean-RHS

        ----------------------------------------------------------------
        -- The "computed" form of the Hyp (matches substF 1 gV P modulo
        -- the substT 1 gV Rc bridge).  Sgv, Fgv are kept abstract.

        HypP-Comp-LHS : Term
        HypP-Comp-LHS = ap2 (iter step) (cfgEV Rc (ap2 pi Sgv N) Fgv)
                                        (ap2 fuelR_combinator Sgv N)

        HypP-Comp-RHS : Term
        HypP-Comp-RHS = cfgRT (ap2 (R g h1 h2) Sgv N) Fgv

        HypP-Comp : Formula
        HypP-Comp = eqF HypP-Comp-LHS HypP-Comp-RHS

        ConclP-Comp-LHS : Term
        ConclP-Comp-LHS = ap2 (iter step) (cfgEV Rc (ap2 pi X sN) K)
                                          (ap2 fuelR_combinator X sN)

        ConclP-Comp-RHS : Term
        ConclP-Comp-RHS = cfgRT (ap2 (R g h1 h2) X sN) K

        ConclP-Comp : Formula
        ConclP-Comp = eqF ConclP-Comp-LHS ConclP-Comp-RHS

        ----------------------------------------------------------------
        -- Bridge HypP-Comp to HypClean via cong rewrites with eq-Sgv,
        -- eq-Fgv.

        eq-HypLHS :
          Deriv (eqF HypP-Comp-LHS HypClean-LHS)
        eq-HypLHS =
          let -- iter step c f rewrites: change c and f.
              -- c: cfgEV Rc (pi Sgv N) Fgv -> cfgEV Rc (pi X N) konsForm.
              -- f: fuelR_combinator Sgv N -> fuelR_combinator X N.
              e_arg : Deriv (eqF (ap2 pi Sgv N) (ap2 pi X N))
              e_arg = congL pi N eq-Sgv

              e_c1 : Deriv (eqF (cfgEV Rc (ap2 pi Sgv N) Fgv)
                                 (cfgEV Rc (ap2 pi X N) Fgv))
              e_c1 = cfgEV-arg-rw Rc (ap2 pi Sgv N) (ap2 pi X N) Fgv e_arg

              e_c2 : Deriv (eqF (cfgEV Rc (ap2 pi X N) Fgv)
                                 (cfgEV Rc (ap2 pi X N) konsForm))
              e_c2 = cfgEV-kont-rw Rc (ap2 pi X N) Fgv konsForm eq-Fgv

              e_c : Deriv (eqF (cfgEV Rc (ap2 pi Sgv N) Fgv)
                                (cfgEV Rc (ap2 pi X N) konsForm))
              e_c = ruleTrans e_c1 e_c2

              e_fuel : Deriv (eqF (ap2 fuelR_combinator Sgv N)
                                   (ap2 fuelR_combinator X N))
              e_fuel = congL fuelR_combinator N eq-Sgv

              e_iter_c : Deriv (eqF HypP-Comp-LHS
                                     (ap2 (iter step) (cfgEV Rc (ap2 pi X N) konsForm)
                                                       (ap2 fuelR_combinator Sgv N)))
              e_iter_c = congL (iter step) (ap2 fuelR_combinator Sgv N) e_c

              e_iter_f : Deriv (eqF (ap2 (iter step) (cfgEV Rc (ap2 pi X N) konsForm)
                                                       (ap2 fuelR_combinator Sgv N))
                                     HypClean-LHS)
              e_iter_f = congR (iter step) (cfgEV Rc (ap2 pi X N) konsForm) e_fuel
          in ruleTrans e_iter_c e_iter_f

        eq-HypRHS :
          Deriv (eqF HypP-Comp-RHS HypClean-RHS)
        eq-HypRHS =
          let e_val : Deriv (eqF (ap2 (R g h1 h2) Sgv N) (ap2 (R g h1 h2) X N))
              e_val = congL (R g h1 h2) N eq-Sgv

              e_c1 : Deriv (eqF (cfgRT (ap2 (R g h1 h2) Sgv N) Fgv)
                                 (cfgRT (ap2 (R g h1 h2) X N) Fgv))
              e_c1 = cfgRT-val-rw (ap2 (R g h1 h2) Sgv N) (ap2 (R g h1 h2) X N) Fgv e_val

              e_c2 : Deriv (eqF (cfgRT (ap2 (R g h1 h2) X N) Fgv)
                                 HypClean-RHS)
              e_c2 = cfgRT-kont-rw (ap2 (R g h1 h2) X N) Fgv konsForm eq-Fgv
          in ruleTrans e_c1 e_c2

        -- Bridge HypP-Comp -> HypClean as Deriv (imp HypP-Comp HypClean).
        D-HypP-to-Clean :
          Deriv (imp HypP-Comp HypClean)
        D-HypP-to-Clean =
          let s1 : Deriv (imp HypP-Comp (eqF HypClean-LHS HypP-Comp-RHS))
              s1 = mp (ax_eqTrans HypP-Comp-LHS HypClean-LHS HypP-Comp-RHS)
                       eq-HypLHS
              s2 : Deriv (imp (eqF HypClean-LHS HypP-Comp-RHS) HypClean)
              s2 = appendEqRight HypClean-LHS HypP-Comp-RHS HypClean-RHS eq-HypRHS
          in impTrans s1 s2

        ----------------------------------------------------------------
        -- 7-segment R-step proof: Deriv (imp HypClean ConclClean).
        --
        -- Mirrors the existing StepU2CorrectR.Construct.stepCase but with
        -- N, X, K abstract Terms.

        cInitN : Term
        cInitN = cfgEV Rc (ap2 pi X sN) K

        cAfter1 : Term
        cAfter1 = cfgEV (mcode2 h2) (ap2 pi X N)
                         (kons (frmR1 Rc h1c X N) K)

        cAfter2 : Term
        cAfter2 = cfgRT (ap2 h2 X N) (kons (frmR1 Rc h1c X N) K)

        cAfter3 : Term
        cAfter3 = cfgEV Rc (ap2 pi X N) konsForm

        cAfter4_konsForm : Term
        cAfter4_konsForm = cfgRT (ap2 (R g h1 h2) X N) konsForm

        cAfter5 : Term
        cAfter5 =
          cfgEV h1c (ap2 pi (ap2 h2 X N) (ap2 (R g h1 h2) X N)) K

        cAfter6 : Term
        cAfter6 =
          cfgRT (ap2 h1 (ap2 h2 X N) (ap2 (R g h1 h2) X N)) K

        cFinalN : Term
        cFinalN = cfgRT (ap2 (R g h1 h2) X sN) K

        oneT : Term
        oneT = ap1 s O

        fH2v : Term
        fH2v = ap2 fH2 X N

        fuelR_N : Term
        fuelR_N = ap2 fuelR_combinator X N

        fH1v : Term
        fH1v = ap2 fH1 (ap2 h2 X N) (ap2 (R g h1 h2) X N)

        ----------------------------------------------------------------
        -- Segments 1-3 (unconditional).

        step_seg1 : Deriv (eqF (ap1 step cInitN) cAfter1)
        step_seg1 = stepU_at_evRstep g h1 h2 X N K

        run_seg1 : Deriv (eqF (ap2 (iter step) cInitN oneT) cAfter1)
        run_seg1 = iter-step1 cInitN cAfter1 step_seg1

        run_seg2 : Deriv (eqF (ap2 (iter step) cAfter1 fH2v) cAfter2)
        run_seg2 = runs2 bH2 X N (kons (frmR1 Rc h1c X N) K)

        step_seg3 : Deriv (eqF (ap1 step cAfter2) cAfter3)
        step_seg3 = stepU_at_rtR1 (ap2 h2 X N) Rc h1c X N K

        run_seg3 : Deriv (eqF (ap2 (iter step) cAfter2 oneT) cAfter3)
        run_seg3 = iter-step1 cAfter2 cAfter3 step_seg3

        fuel123 : Term
        fuel123 = ap2 sigma (ap2 sigma oneT fH2v) oneT

        run_seg12 :
          Deriv (eqF (ap2 (iter step) cInitN (ap2 sigma oneT fH2v)) cAfter2)
        run_seg12 =
          ruleTrans (iter_add_T cInitN oneT fH2v)
            (ruleTrans (congL (iter step) fH2v run_seg1) run_seg2)

        run_seg123 :
          Deriv (eqF (ap2 (iter step) cInitN fuel123) cAfter3)
        run_seg123 =
          ruleTrans (iter_add_T cInitN (ap2 sigma oneT fH2v) oneT)
            (ruleTrans (congL (iter step) oneT run_seg12) run_seg3)

        ----------------------------------------------------------------
        -- Segment 4: IH (= HypClean).

        -- HypClean says iter step cAfter3 fuelR_N = cAfter4_konsForm
        -- (since cAfter3 = cfgEV Rc (pi X N) konsForm
        --        cAfter4_konsForm = cfgRT (R X N) konsForm).
        -- So HypClean IS the equation we need at the IH segment.

        ----------------------------------------------------------------
        -- Segments 5-6.

        step_seg5 :
          Deriv (eqF (ap1 step cAfter4_konsForm) cAfter5)
        step_seg5 = stepU_at_rtApp2 (ap2 (R g h1 h2) X N) h1c (ap2 h2 X N) K

        run_seg5 :
          Deriv (eqF (ap2 (iter step) cAfter4_konsForm oneT) cAfter5)
        run_seg5 = iter-step1 cAfter4_konsForm cAfter5 step_seg5

        run_seg6 : Deriv (eqF (ap2 (iter step) cAfter5 fH1v) cAfter6)
        run_seg6 = runs2 bH1 (ap2 h2 X N) (ap2 (R g h1 h2) X N) K

        fuel56 : Term
        fuel56 = ap2 sigma oneT fH1v

        run_seg56 :
          Deriv (eqF (ap2 (iter step) cAfter4_konsForm fuel56) cAfter6)
        run_seg56 =
          ruleTrans (iter_add_T cAfter4_konsForm oneT fH1v)
            (ruleTrans (congL (iter step) fH1v run_seg5) run_seg6)

        ----------------------------------------------------------------
        -- Final value bridge: cAfter6 -> cFinalN via ax_R_step.

        eVal :
          Deriv (eqF (ap2 h1 (ap2 h2 X N) (ap2 (R g h1 h2) X N))
                      (ap2 (R g h1 h2) X sN))
        eVal = ruleSym (ax_R_step g h1 h2 X N)

        eRT_final :
          Deriv (eqF cAfter6 cFinalN)
        eRT_final = cfgRT-val-rw
                      (ap2 h1 (ap2 h2 X N) (ap2 (R g h1 h2) X N))
                      (ap2 (R g h1 h2) X sN) K eVal

        ----------------------------------------------------------------
        -- Composition of segments 1-3 + IH + segments 5-6 + final bridge.
        -- Under HypClean.

        -- fuel_full = sigma (sigma fuel123 fuelR_N) fuel56.
        fuel_full : Term
        fuel_full = ap2 sigma (ap2 sigma fuel123 fuelR_N) fuel56

        -- Under HypClean, build:
        --   iter step cInitN fuel_full = cFinalN.

        -- IH (HypClean) gives: iter step cAfter3 fuelR_N = cAfter4_konsForm.

        -- Step 1: combine run_seg123 with IH at cAfter3 via congL.
        --   iter step (iter step cInitN fuel123) fuelR_N
        --     = iter step cAfter3 fuelR_N     [congL via run_seg123]
        --     = cAfter4_konsForm              [via HypClean].

        -- Imp form.
        HypClean-imp-self : Deriv (imp HypClean HypClean)
        HypClean-imp-self = identP HypClean

        cong-IH-conf :
          Deriv (imp HypClean
                  (eqF (ap2 (iter step) (ap2 (iter step) cInitN fuel123) fuelR_N)
                        (ap2 (iter step) cAfter3 fuelR_N)))
        cong-IH-conf =
          mp (axK (eqF (ap2 (iter step) (ap2 (iter step) cInitN fuel123) fuelR_N)
                        (ap2 (iter step) cAfter3 fuelR_N))
                   HypClean)
              (congL (iter step) fuelR_N run_seg123)

        IH-at-cAfter3 :
          Deriv (imp HypClean
                  (eqF (ap2 (iter step) (ap2 (iter step) cInitN fuel123) fuelR_N)
                        cAfter4_konsForm))
        IH-at-cAfter3 =
          let s1 = mp (ax_eqTrans (ap2 (iter step) cAfter3 fuelR_N)
                                     (ap2 (iter step) (ap2 (iter step) cInitN fuel123) fuelR_N)
                                     cAfter4_konsForm)
                       (ruleSym (congL (iter step) fuelR_N run_seg123))
              -- s1 : Deriv (imp (eqF cAfter3-iter cAfter4) (eqF lhs cAfter4))
              -- Where cAfter3-iter = ap2 (iter step) cAfter3 fuelR_N
              --       lhs = ap2 (iter step) (iter cInitN fuel123) fuelR_N
              -- and HypClean = eqF cAfter3-iter cAfter4_konsForm (since cAfter3 = cfgEV Rc ... konsForm, cAfter4 = cfgRT R konsForm).
          in s1

        -- iter_add_T cInitN fuel123 fuelR_N : iter step cInitN (sigma fuel123 fuelR_N)
        --                                  = iter step (iter step cInitN fuel123) fuelR_N.

        iter-add-123-IH :
          Deriv (eqF (ap2 (iter step) cInitN (ap2 sigma fuel123 fuelR_N))
                      (ap2 (iter step) (ap2 (iter step) cInitN fuel123) fuelR_N))
        iter-add-123-IH = iter_add_T cInitN fuel123 fuelR_N

        -- Under HypClean: iter step cInitN (sigma fuel123 fuelR_N) = cAfter4_konsForm.
        run-to-after4 :
          Deriv (imp HypClean
                  (eqF (ap2 (iter step) cInitN (ap2 sigma fuel123 fuelR_N))
                        cAfter4_konsForm))
        run-to-after4 =
          let s1 : Deriv (imp HypClean (eqF (ap2 (iter step) cInitN (ap2 sigma fuel123 fuelR_N))
                                              (ap2 (iter step) (ap2 (iter step) cInitN fuel123) fuelR_N)))
              s1 = mp (axK _ HypClean) iter-add-123-IH
              s2 : Deriv (imp HypClean (eqF (ap2 (iter step) cInitN (ap2 sigma fuel123 fuelR_N))
                                              cAfter4_konsForm))
              s2 = transUnderOne s1 IH-at-cAfter3
          in s2

        -- Now compose with run_seg56 + final-bridge.

        iter-add-after :
          Deriv (eqF (ap2 (iter step) cInitN
                            (ap2 sigma (ap2 sigma fuel123 fuelR_N) fuel56))
                      (ap2 (iter step)
                            (ap2 (iter step) cInitN (ap2 sigma fuel123 fuelR_N))
                            fuel56))
        iter-add-after = iter_add_T cInitN (ap2 sigma fuel123 fuelR_N) fuel56

        -- Under HypClean, congL via run-to-after4.
        cong-step-56 :
          Deriv (imp HypClean
                  (eqF (ap2 (iter step)
                              (ap2 (iter step) cInitN (ap2 sigma fuel123 fuelR_N))
                              fuel56)
                        (ap2 (iter step) cAfter4_konsForm fuel56)))
        cong-step-56 =
          let cong-imp = ax_eqCongL (iter step)
                            (ap2 (iter step) cInitN (ap2 sigma fuel123 fuelR_N))
                            cAfter4_konsForm fuel56
          in bComb (mp (axK _ HypClean) cong-imp) run-to-after4

        -- Under HypClean: iter step cInitN fuel_full = cAfter6.
        run-full :
          Deriv (imp HypClean
                  (eqF (ap2 (iter step) cInitN fuel_full) cAfter6))
        run-full =
          let s1 : Deriv (imp HypClean (eqF (ap2 (iter step) cInitN fuel_full)
                                              (ap2 (iter step)
                                                    (ap2 (iter step) cInitN (ap2 sigma fuel123 fuelR_N))
                                                    fuel56)))
              s1 = mp (axK _ HypClean) iter-add-after
              s2 : Deriv (imp HypClean (eqF (ap2 (iter step) cInitN fuel_full)
                                              (ap2 (iter step) cAfter4_konsForm fuel56)))
              s2 = transUnderOne s1 cong-step-56
              s3 : Deriv (imp HypClean (eqF (ap2 (iter step) cInitN fuel_full) cAfter6))
              s3 = transUnderOne s2 (mp (axK _ HypClean) run_seg56)
          in s3

        -- Final bridge: cAfter6 -> cFinalN.
        run-to-final :
          Deriv (imp HypClean
                  (eqF (ap2 (iter step) cInitN fuel_full) cFinalN))
        run-to-final =
          transUnderOne run-full (mp (axK _ HypClean) eRT_final)

        ----------------------------------------------------------------
        -- Rewrite fuel: fuel_full -> fuelR_combinator X sN.
        -- Mirrors StepU2CorrectR Section 4d.2 (fuel_full -> target_fuel via
        -- iter-level association, then -> fuelR via Snd_paired_R_at_s +
        -- fuel-next-unfold).

        c0 : Term
        c0 = cInitN

        c1 : Term
        c1 = ap2 (iter step) c0 oneT

        c2 : Term
        c2 = ap2 (iter step) c1 fH2v

        c3 : Term
        c3 = ap2 (iter step) c2 oneT

        c4 : Term
        c4 = ap2 (iter step) c3 fuelR_N

        c5 : Term
        c5 = ap2 (iter step) c4 oneT

        c6 : Term
        c6 = ap2 (iter step) c5 fH1v

        target_fuel : Term
        target_fuel =
          ap2 sigma
              (ap2 sigma
                  (ap2 sigma
                    (ap2 sigma
                      (ap2 sigma oneT fH2v) oneT)
                    fuelR_N) oneT) fH1v

        -- Step (a): iter step c0 fuel_full = iter step (iter c0 (sigma fuel123 fuelR_N)) fuel56.
        ea : Deriv (eqF (ap2 (iter step) c0 fuel_full)
                          (ap2 (iter step) (ap2 (iter step) c0 (ap2 sigma fuel123 fuelR_N)) fuel56))
        ea = iter_add_T c0 (ap2 sigma fuel123 fuelR_N) fuel56

        eb1 : Deriv (eqF (ap2 (iter step) c0 (ap2 sigma fuel123 fuelR_N))
                           (ap2 (iter step) (ap2 (iter step) c0 fuel123) fuelR_N))
        eb1 = iter_add_T c0 fuel123 fuelR_N

        eb2 : Deriv (eqF (ap2 (iter step) c0 fuel123)
                          (ap2 (iter step) (ap2 (iter step) c0 (ap2 sigma oneT fH2v)) oneT))
        eb2 = iter_add_T c0 (ap2 sigma oneT fH2v) oneT

        eb3 : Deriv (eqF (ap2 (iter step) c0 (ap2 sigma oneT fH2v))
                          (ap2 (iter step) (ap2 (iter step) c0 oneT) fH2v))
        eb3 = iter_add_T c0 oneT fH2v

        eb3_to_c2 : Deriv (eqF (ap2 (iter step) c0 (ap2 sigma oneT fH2v)) c2)
        eb3_to_c2 = eb3

        eb2_to_c3 : Deriv (eqF (ap2 (iter step) c0 fuel123) c3)
        eb2_to_c3 = ruleTrans eb2 (congL (iter step) oneT eb3_to_c2)

        eb1_to_c4 : Deriv (eqF (ap2 (iter step) c0 (ap2 sigma fuel123 fuelR_N)) c4)
        eb1_to_c4 = ruleTrans eb1 (congL (iter step) fuelR_N eb2_to_c3)

        ea_to_c4 :
          Deriv (eqF (ap2 (iter step) c0 fuel_full)
                      (ap2 (iter step) c4 fuel56))
        ea_to_c4 = ruleTrans ea (congL (iter step) fuel56 eb1_to_c4)

        ec1 : Deriv (eqF (ap2 (iter step) c4 fuel56)
                           (ap2 (iter step) c5 fH1v))
        ec1 = iter_add_T c4 oneT fH1v

        ea_to_c6 :
          Deriv (eqF (ap2 (iter step) c0 fuel_full) c6)
        ea_to_c6 = ruleTrans ea_to_c4 ec1

        ed : Deriv (eqF (ap2 (iter step) c0 target_fuel)
                         (ap2 (iter step)
                                (ap2 (iter step) c0 (ap2 sigma (ap2 sigma (ap2 sigma (ap2 sigma oneT fH2v) oneT) fuelR_N) oneT))
                                fH1v))
        ed = iter_add_T c0 (ap2 sigma (ap2 sigma (ap2 sigma (ap2 sigma oneT fH2v) oneT) fuelR_N) oneT) fH1v

        ed1 : Deriv (eqF (ap2 (iter step) c0 (ap2 sigma (ap2 sigma (ap2 sigma (ap2 sigma oneT fH2v) oneT) fuelR_N) oneT))
                          (ap2 (iter step) (ap2 (iter step) c0 (ap2 sigma (ap2 sigma (ap2 sigma oneT fH2v) oneT) fuelR_N)) oneT))
        ed1 = iter_add_T c0 (ap2 sigma (ap2 sigma (ap2 sigma oneT fH2v) oneT) fuelR_N) oneT

        ed2 : Deriv (eqF (ap2 (iter step) c0 (ap2 sigma (ap2 sigma (ap2 sigma oneT fH2v) oneT) fuelR_N))
                          (ap2 (iter step) (ap2 (iter step) c0 (ap2 sigma (ap2 sigma oneT fH2v) oneT)) fuelR_N))
        ed2 = iter_add_T c0 (ap2 sigma (ap2 sigma oneT fH2v) oneT) fuelR_N

        ed3 : Deriv (eqF (ap2 (iter step) c0 (ap2 sigma (ap2 sigma oneT fH2v) oneT))
                          (ap2 (iter step) (ap2 (iter step) c0 (ap2 sigma oneT fH2v)) oneT))
        ed3 = iter_add_T c0 (ap2 sigma oneT fH2v) oneT

        ed3_to_c3 : Deriv (eqF (ap2 (iter step) c0 (ap2 sigma (ap2 sigma oneT fH2v) oneT)) c3)
        ed3_to_c3 = ruleTrans ed3 (congL (iter step) oneT eb3_to_c2)

        ed2_to_c4 : Deriv (eqF (ap2 (iter step) c0 (ap2 sigma (ap2 sigma (ap2 sigma oneT fH2v) oneT) fuelR_N)) c4)
        ed2_to_c4 = ruleTrans ed2 (congL (iter step) fuelR_N ed3_to_c3)

        ed1_to_c5 : Deriv (eqF (ap2 (iter step) c0 (ap2 sigma (ap2 sigma (ap2 sigma (ap2 sigma oneT fH2v) oneT) fuelR_N) oneT)) c5)
        ed1_to_c5 = ruleTrans ed1 (congL (iter step) oneT ed2_to_c4)

        ed_to_c6 : Deriv (eqF (ap2 (iter step) c0 target_fuel) c6)
        ed_to_c6 = ruleTrans ed (congL (iter step) fH1v ed1_to_c5)

        e_fuel_eq :
          Deriv (eqF (ap2 (iter step) c0 fuel_full) (ap2 (iter step) c0 target_fuel))
        e_fuel_eq = ruleTrans ea_to_c6 (ruleSym ed_to_c6)

        -- Bridge target_fuel -> fuelR_combinator X sN.
        eTarget_fuelR :
          Deriv (eqF target_fuel (ap2 fuelR_combinator X sN))
        eTarget_fuelR =
          let e1 : Deriv (eqF target_fuel (ap2 fuel_next_Fun2 (ap2 F3 X N) (ap2 paired_R X N)))
              e1 = ruleSym (fuel-next-unfold X N)
              e2 : Deriv (eqF (ap2 fuel_next_Fun2 (ap2 F3 X N) (ap2 paired_R X N))
                                (ap1 Snd (ap2 paired_R X sN)))
              e2 = ruleSym (Snd_paired_R_at_s X N)
              e3 : Deriv (eqF (ap1 Snd (ap2 paired_R X sN))
                                (ap2 fuelR_combinator X sN))
              e3 = Snd_paired_R_eq X sN
          in ruleTrans e1 (ruleTrans e2 e3)

        e_target_eq :
          Deriv (eqF (ap2 (iter step) c0 target_fuel)
                       (ap2 (iter step) c0 (ap2 fuelR_combinator X sN)))
        e_target_eq = congR (iter step) c0 eTarget_fuelR

        e_fuel_to_fuelR :
          Deriv (eqF (ap2 (iter step) c0 fuel_full)
                       (ap2 (iter step) c0 (ap2 fuelR_combinator X sN)))
        e_fuel_to_fuelR = ruleTrans e_fuel_eq e_target_eq

        e_fuel_to_fuelR_sym :
          Deriv (eqF (ap2 (iter step) c0 (ap2 fuelR_combinator X sN))
                       (ap2 (iter step) c0 fuel_full))
        e_fuel_to_fuelR_sym = ruleSym e_fuel_to_fuelR

        -- Combine: under HypClean,
        --   iter step cInitN (fuelR X sN) = cFinalN.

        D-Clean :
          Deriv (imp HypClean ConclClean)
        D-Clean =
          let s1 : Deriv (imp HypClean (eqF (ap2 (iter step) cInitN (ap2 fuelR_combinator X sN))
                                              (ap2 (iter step) cInitN fuel_full)))
              s1 = mp (axK _ HypClean) e_fuel_to_fuelR_sym
              s2 : Deriv (imp HypClean ConclClean)
              s2 = transUnderOne s1 run-to-final
          in s2

        ----------------------------------------------------------------
        -- Compose: D-HypP-to-Clean + D-Clean ==> Deriv (imp HypP-Comp ConclClean).

        D-HypPComp-to-ConclClean :
          Deriv (imp HypP-Comp ConclClean)
        D-HypPComp-to-ConclClean = impTrans D-HypP-to-Clean D-Clean

        ----------------------------------------------------------------
        -- Bridge to actual substF forms via eqSubst on the Rc walks.

        -- ConclP-Comp = ConclClean (no substT 0 sN Rc bridge needed --
        -- actually substT 0 sN Rc != Rc.  Bridge via cav-Rc-0).

        -- substF 0 sN P computes to:
        --   eqF (iter step (cfgEV (substT 0 sN Rc) (pi X sN) K) (fuelR X sN))
        --       (cfgRT (R X sN) K)
        -- which is ConclP-Comp with substT 0 sN Rc in place of Rc.

        -- Pred for ConclP eqSubst:
        Pred-Concl : Term -> Set
        Pred-Concl rc =
          Deriv (imp HypP-Comp
                  (eqF (ap2 (iter step) (cfgEV rc (ap2 pi X sN) K)
                              (ap2 fuelR_combinator X sN))
                        (cfgRT (ap2 (R g h1 h2) X sN) K)))

        D-HypPComp-to-ConclP-Comp :
          Deriv (imp HypP-Comp
                  (eqF (ap2 (iter step) (cfgEV (substT zero sN Rc) (ap2 pi X sN) K)
                              (ap2 fuelR_combinator X sN))
                        (cfgRT (ap2 (R g h1 h2) X sN) K)))
        D-HypPComp-to-ConclP-Comp =
          eqSubst Pred-Concl (eqSym (cavSubst cav-Rc-0 sN))
                  D-HypPComp-to-ConclClean

        -- Pred for HypP eqSubst.
        Pred-Hyp : Term -> Set
        Pred-Hyp rc =
          Deriv (imp
                  (eqF (ap2 (iter step) (cfgEV rc (ap2 pi Sgv N) Fgv)
                              (ap2 fuelR_combinator Sgv N))
                        (cfgRT (ap2 (R g h1 h2) Sgv N) Fgv))
                  (eqF (ap2 (iter step) (cfgEV (substT zero sN Rc) (ap2 pi X sN) K)
                              (ap2 fuelR_combinator X sN))
                        (cfgRT (ap2 (R g h1 h2) X sN) K)))

    in eqSubst Pred-Hyp (eqSym (cavSubst cav-Rc-1 gV))
               D-HypPComp-to-ConclP-Comp

  ----------------------------------------------------------------------
  -- Section 2g.  Invoke PeterRec.

  peter : Deriv P
  peter = PeterRec g_R_kons P premiseB premiseS

  ----------------------------------------------------------------------
  -- Section 2h.  Bundle wrapper correct2_R.
  --
  -- Specialise peter at (var 0 := y, var 1 := pi K x); bridge
  -- Snd (pi K x) -> x and Fst (pi K x) -> K via axFst/axSnd.

  runs-R : (x y K0 : Term) ->
    Deriv (eqF (ap2 (iter step) (cfgEV Rc (ap2 pi x y) K0)
                                  (ap2 fuelR_combinator x y))
                (cfgRT (ap2 (R g h1 h2) x y) K0))
  runs-R x y K0 =
    let
        Vxy : Term
        Vxy = ap2 pi K0 x

        -- Specialise peter at (var 0 := y, var 1 := Vxy) SIMULTANEOUSLY
        -- via ruleInst2 (sequential ruleInst would cause the outer
        -- substT to walk INTO the inserted Vxy, getting stuck at the
        -- opaque K0 and x; simSubst inserts both substitutes AS-IS).
        spec : Deriv (simSubstF zero y (suc zero) Vxy P)
        spec = ruleInst2 zero y (suc zero) Vxy refl peter

        -- simSubstF 0 y 1 Vxy P, after Agda computation, has Rc replaced
        -- by simSubstT 0 y 1 Vxy Rc (because simSubstT walks structurally
        -- through Rc and gets stuck at opaque mcode positions).  Bridge
        -- via sim-Rc.

        Pred-spec : Term -> Set
        Pred-spec rc =
          Deriv (eqF (ap2 (iter step) (cfgEV rc (ap2 pi (ap1 Snd Vxy) y) (ap1 Fst Vxy))
                            (ap2 fuelR_combinator (ap1 Snd Vxy) y))
                      (cfgRT (ap2 (R g h1 h2) (ap1 Snd Vxy) y) (ap1 Fst Vxy)))

        spec-clean : Pred-spec Rc
        spec-clean = eqSubst Pred-spec (sim-Rc y Vxy) spec

        -- Now bridge Snd Vxy -> x and Fst Vxy -> K0.
        eq-Snd-Vxy : Deriv (eqF (ap1 Snd Vxy) x)
        eq-Snd-Vxy = axSnd K0 x

        eq-Fst-Vxy : Deriv (eqF (ap1 Fst Vxy) K0)
        eq-Fst-Vxy = axFst K0 x

        -- Bridge the LHS (the iter step expression).
        eq-LHS-arg :
          Deriv (eqF (ap2 pi (ap1 Snd Vxy) y) (ap2 pi x y))
        eq-LHS-arg = congL pi y eq-Snd-Vxy

        eq-LHS-cInit-1 :
          Deriv (eqF (cfgEV Rc (ap2 pi (ap1 Snd Vxy) y) (ap1 Fst Vxy))
                      (cfgEV Rc (ap2 pi x y) (ap1 Fst Vxy)))
        eq-LHS-cInit-1 =
          cfgEV-arg-rw Rc (ap2 pi (ap1 Snd Vxy) y) (ap2 pi x y) (ap1 Fst Vxy)
            eq-LHS-arg

        eq-LHS-cInit-2 :
          Deriv (eqF (cfgEV Rc (ap2 pi x y) (ap1 Fst Vxy))
                      (cfgEV Rc (ap2 pi x y) K0))
        eq-LHS-cInit-2 =
          cfgEV-kont-rw Rc (ap2 pi x y) (ap1 Fst Vxy) K0 eq-Fst-Vxy

        eq-LHS-cInit :
          Deriv (eqF (cfgEV Rc (ap2 pi (ap1 Snd Vxy) y) (ap1 Fst Vxy))
                      (cfgEV Rc (ap2 pi x y) K0))
        eq-LHS-cInit = ruleTrans eq-LHS-cInit-1 eq-LHS-cInit-2

        eq-LHS-fuel :
          Deriv (eqF (ap2 fuelR_combinator (ap1 Snd Vxy) y)
                      (ap2 fuelR_combinator x y))
        eq-LHS-fuel = congL fuelR_combinator y eq-Snd-Vxy

        eq-LHS-iter-c :
          Deriv (eqF (ap2 (iter step) (cfgEV Rc (ap2 pi (ap1 Snd Vxy) y) (ap1 Fst Vxy))
                            (ap2 fuelR_combinator (ap1 Snd Vxy) y))
                      (ap2 (iter step) (cfgEV Rc (ap2 pi x y) K0)
                            (ap2 fuelR_combinator (ap1 Snd Vxy) y)))
        eq-LHS-iter-c = congL (iter step) (ap2 fuelR_combinator (ap1 Snd Vxy) y) eq-LHS-cInit

        eq-LHS-iter-f :
          Deriv (eqF (ap2 (iter step) (cfgEV Rc (ap2 pi x y) K0)
                            (ap2 fuelR_combinator (ap1 Snd Vxy) y))
                      (ap2 (iter step) (cfgEV Rc (ap2 pi x y) K0)
                            (ap2 fuelR_combinator x y)))
        eq-LHS-iter-f = congR (iter step) (cfgEV Rc (ap2 pi x y) K0) eq-LHS-fuel

        eq-LHS :
          Deriv (eqF (ap2 (iter step) (cfgEV Rc (ap2 pi (ap1 Snd Vxy) y) (ap1 Fst Vxy))
                            (ap2 fuelR_combinator (ap1 Snd Vxy) y))
                      (ap2 (iter step) (cfgEV Rc (ap2 pi x y) K0)
                            (ap2 fuelR_combinator x y)))
        eq-LHS = ruleTrans eq-LHS-iter-c eq-LHS-iter-f

        -- Bridge the RHS.
        eq-RHS-val :
          Deriv (eqF (ap2 (R g h1 h2) (ap1 Snd Vxy) y)
                      (ap2 (R g h1 h2) x y))
        eq-RHS-val = congL (R g h1 h2) y eq-Snd-Vxy

        eq-RHS-cRT-1 :
          Deriv (eqF (cfgRT (ap2 (R g h1 h2) (ap1 Snd Vxy) y) (ap1 Fst Vxy))
                      (cfgRT (ap2 (R g h1 h2) x y) (ap1 Fst Vxy)))
        eq-RHS-cRT-1 =
          cfgRT-val-rw (ap2 (R g h1 h2) (ap1 Snd Vxy) y) (ap2 (R g h1 h2) x y)
                        (ap1 Fst Vxy) eq-RHS-val

        eq-RHS-cRT-2 :
          Deriv (eqF (cfgRT (ap2 (R g h1 h2) x y) (ap1 Fst Vxy))
                      (cfgRT (ap2 (R g h1 h2) x y) K0))
        eq-RHS-cRT-2 = cfgRT-kont-rw (ap2 (R g h1 h2) x y) (ap1 Fst Vxy) K0 eq-Fst-Vxy

        eq-RHS :
          Deriv (eqF (cfgRT (ap2 (R g h1 h2) (ap1 Snd Vxy) y) (ap1 Fst Vxy))
                      (cfgRT (ap2 (R g h1 h2) x y) K0))
        eq-RHS = ruleTrans eq-RHS-cRT-1 eq-RHS-cRT-2

        -- Compose: spec-clean : eqF (Snd-Vxy-form-LHS) (Snd-Vxy-form-RHS).
        -- We want:           : eqF (clean-LHS) (clean-RHS).
        -- Bridge via ruleTrans (ruleSym eq-LHS) spec-clean ... no wait, need to chain.

        -- spec-clean (=type Pred-spec Rc) is:
        --   eqF (iter step (cfgEV Rc (pi (Snd Vxy) y) (Fst Vxy)) (fuelR (Snd Vxy) y))
        --       (cfgRT (R (Snd Vxy) y) (Fst Vxy))
        -- = eqF lhs-V rhs-V (where Snd Vxy and Fst Vxy appear).

        -- We want eqF lhs-clean rhs-clean.
        -- eq-LHS : eqF lhs-V lhs-clean.
        -- eq-RHS : eqF rhs-V rhs-clean.
        -- spec-clean : eqF lhs-V rhs-V.
        -- => eqF lhs-clean rhs-clean via:
        --   ruleSym eq-LHS : eqF lhs-clean lhs-V.
        --   ruleTrans (ruleSym eq-LHS) spec-clean : eqF lhs-clean rhs-V.
        --   ruleTrans <prev> eq-RHS : eqF lhs-clean rhs-clean.

        final : Deriv (eqF (ap2 (iter step) (cfgEV Rc (ap2 pi x y) K0)
                                  (ap2 fuelR_combinator x y))
                            (cfgRT (ap2 (R g h1 h2) x y) K0))
        final = ruleTrans (ruleSym eq-LHS) (ruleTrans spec-clean eq-RHS)

    in final

  correct2_R : Correct2 (R g h1 h2)
  correct2_R = mkC2 fuelR_combinator runs-R
