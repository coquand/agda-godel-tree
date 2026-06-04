{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.StepU2MuCorrectImp -- Carneiro-lifted (imp Rf) variant of
-- T4.StepU2MuCorrect.Construct.runs_mu.
--
-- Mirrors  T4.StepU2MuCorrect.Construct  step-by-step under  imp Rf
-- via  T4.Thm12.ImpHelpers  +  T4.ImpExtras .
--
-- The original  Construct  module takes a CLOSED  isHit  hypothesis:
--   isHit : Deriv (eqF (ap1 gFun k_max) O)
-- The imp-lifted variant  ImpConstruct  takes a Carneiro-lifted variant:
--   imp_isHit : Deriv (imp Rf (eqF (ap1 gFun k_max) O))
-- All OTHER Construct hypotheses (missSucc, subSuccBridge_at, ..., closure
-- witnesses) remain CLOSED -- they're independent of  hyp  in the original
-- Carneiro chain (see  T4.ChaitinG1DischargeKdefImp ).
--
-- HEADLINE.
--
--   imp_runs_mu :
--     (x_outer K0 : Term) ->
--     Deriv (imp Rf
--            (eqF (ap2 (iter step)
--                       (cfgEV (mcodeMu gc) x_outer K0)
--                       (ap2 sigma (ap1 s O)
--                                   (ap2 fuelMu_fun k_max k_max)))
--                  (cfgRT k_max K0)))
--
-- STRUCTURE.
--
--   Sections 1-1c:   Closed components (fuelMu_fun, cav-mcode1/2,
--                    gc-sub0/sub1, sim-mcode1/2, gc-sim).  COPIED VERBATIM
--                    from  Construct  -- they don't reference  isHit .
--
--   Section 2:      Motive  P  (= original Construct's motive).  We use
--                   ruleIndNat  with motive  Q := imp Rf P .
--
--   Section 2a:     Closed cfg helpers (verbatim).
--
--   Section 2b:     Imp-lifted cfg helpers (new).
--
--   Section 3:      imp_clean-O -- mirrors  clean-O  step-by-step with
--                   imp_isHit  in place of  isHit  at the
--                   cAfterG-bridge  step.  Rest of chain is  impLift  of
--                   the closed  Construct -compatible chain.
--
--   Section 4:      imp_premiseB -- bridge  imp_clean-O  through closure
--                   witnesses (k_max_sub0 + gc-sub0) to
--                   Deriv (substF zero O Q) ; uses  sub0_Rf  for Rf.
--
--   Section 5:      premiseS_closed (verbatim) -- doesn't use isHit.
--                   imp_premiseS via  axS  + sub0_Rf  bridge (3 lines).
--
--   Section 6:      imp_peter := ruleIndNat zero {Q} imp_premiseB
--                                  imp_premiseS .
--
--   Section 7:      imp_runs_mu bundle -- mirrors  Construct.runs_mu
--                   wrapper.  ruleInst2 + sim_Rf  bridge + closed
--                   leqRefl_k_max / sub_k_max_k_max + stepU_at_evMu prepend.

module T4.StepU2MuCorrectImp where

open import T4.Base
open import T4.StepU2
  using ( step
        ; cfgEV ; cfgRT ; kons ; mcode1 ; mcode2
        ; tagRT ; tagEV )
open import T4.EvalU
  using ( mcodeMu ; frmM )
open import T4.EvalUStep
  using ( stepU_at_evMu ; stepU_at_rtMbase ; stepU_at_rtMstep )
open import T4.StepU2Reach
  using ( iter_add_T )
open import T4.Tags
  using ( tag_s ; tag_o ; tag_u ; tag_C ; tag_v ; tag_R )
open import T4.StepU2CorrectAPI
  using ( Correct1 ; fuelF ; runs1 )

open import T4.Thm12.ImpHelpers
  using ( impRefl ; impLift ; impMp ; impEqTrans
        ; impCong1 ; impCongL ; impCongR ; impRuleSym )

open import BRA3.CourseOfValues
  using ( iter )
open import BRA3.RecBRA3AtPairUniv
  using ( iter_base_univ ; iter_step_univ )
open import BRA3.Church
  using ( pi ; sigma ; sub )
open import BRA3.ChurchLeq
  using ( leq )
open import BRA3.PairAlgebra
  using ( Post ; axPost ; Fan ; Lift1 ; Lift2 )
open import BRA3.Fan
  using ( Fan_eq ; Lift1_eq ; Lift2_eq )
open import BRA3.Logic
  using ( prependEqLeft ; appendEqRight ; impTrans )
open import BRA3.Contrapositive
  using ( identP ; liftP ; bComb ; bCombTwo ; compI )
open import BRA3.RuleInst2
  using ( ruleInst2 ; simSubstT ; simSubstF )

------------------------------------------------------------------------
-- Section 0.  Module ImpConstruct.

module ImpConstruct
  (Rf : Formula)
  (gFun : Fun1)
  (bF : Correct1 gFun)
  (k_max : Term)
  (predFun : Fun1)
  (imp_isHit : Deriv (imp Rf (eqF (ap1 gFun k_max) O)))
  (missSucc : (x : Term) ->
              Deriv (imp (leq (ap1 s x) k_max)
                          (eqF (ap1 gFun x) (ap1 s (ap1 predFun x)))))
  (subSuccBridge : (y : Term) ->
                   Deriv (imp (leq (ap1 s y) k_max)
                               (eqF (ap1 s (ap2 sub k_max (ap1 s y)))
                                    (ap2 sub k_max y))))
  (leqDecrease : (y : Term) ->
                 Deriv (imp (leq (ap1 s y) k_max) (leq y k_max)))
  (subBoundsAux : (y : Term) ->
                  Deriv (imp (leq (ap1 s y) k_max)
                              (leq (ap1 s (ap2 sub k_max (ap1 s y))) k_max)))
  (leqRefl_k_max : Deriv (leq k_max k_max))
  (sub_k_max_k_max : Deriv (eqF (ap2 sub k_max k_max) O))
  (k_max_sub0 : (a : Term) -> Eq (substT zero a k_max) k_max)
  (k_max_sub1 : (a : Term) -> Eq (substT (suc zero) a k_max) k_max)
  (k_max_sim : (a b : Term) -> Eq (simSubstT zero a (suc zero) b k_max) k_max)
  (sub0_Rf : (a : Term) -> Eq (substF zero a Rf) Rf)
  (sub1_Rf : (a : Term) -> Eq (substF (suc zero) a Rf) Rf)
  (sim_Rf : (a b : Term) -> Eq (simSubstF zero a (suc zero) b Rf) Rf)
  where

  ----------------------------------------------------------------------
  -- Section 1.  Closed components copied from Construct.

  gc : Term
  gc = mcode1 gFun

  fG : Fun1
  fG = fuelF bF

  ----------------------------------------------------------------------
  -- Section 1a.  fuelMu_fun :  Fun2  -- depth-fuel for the mu walk.

  fuelBase : Fun1
  fuelBase = C sigma fG (constN 1)

  fuelBase-eq : (k : Term) ->
                Deriv (eqF (ap1 fuelBase k) (ap2 sigma (ap1 fG k) (ap1 s O)))
  fuelBase-eq k =
    let e1 = ax_C sigma fG (constN 1) k
        e2 = congR sigma (ap1 fG k) (constN_eq 1 k)
    in ruleTrans e1 e2

  sub_at_s : Fun2
  sub_at_s = Fan (Lift1 u) (Lift2 s) sub

  sub_at_s-eq : (a b : Term) ->
                Deriv (eqF (ap2 sub_at_s a b) (ap2 sub a (ap1 s b)))
  sub_at_s-eq a b =
    let e1 : Deriv (eqF (ap2 sub_at_s a b)
                         (ap2 sub (ap2 (Lift1 u) a b) (ap2 (Lift2 s) a b)))
        e1 = Fan_eq (Lift1 u) (Lift2 s) sub a b
        eL : Deriv (eqF (ap2 (Lift1 u) a b) a)
        eL = ruleTrans (Lift1_eq u a b) (ax_u a)
        eR : Deriv (eqF (ap2 (Lift2 s) a b) (ap1 s b))
        eR = Lift2_eq s a b
        e2 : Deriv (eqF (ap2 sub (ap2 (Lift1 u) a b) (ap2 (Lift2 s) a b))
                         (ap2 sub a (ap1 s b)))
        e2 = ruleTrans (congL sub (ap2 (Lift2 s) a b) eL) (congR sub a eR)
    in ruleTrans e1 e2

  fuelStepH2 : Fun2
  fuelStepH2 = Fan (Post fG sub_at_s) (Lift1 (constN 1)) sigma

  fuelStepH2-eq : (a b : Term) ->
                  Deriv (eqF (ap2 fuelStepH2 a b)
                              (ap2 sigma (ap1 fG (ap2 sub a (ap1 s b)))
                                          (ap1 s O)))
  fuelStepH2-eq a b =
    let e1 : Deriv (eqF (ap2 fuelStepH2 a b)
                         (ap2 sigma (ap2 (Post fG sub_at_s) a b)
                                     (ap2 (Lift1 (constN 1)) a b)))
        e1 = Fan_eq (Post fG sub_at_s) (Lift1 (constN 1)) sigma a b
        eL : Deriv (eqF (ap2 (Post fG sub_at_s) a b)
                         (ap1 fG (ap2 sub a (ap1 s b))))
        eL = ruleTrans (axPost fG sub_at_s a b) (cong1 fG (sub_at_s-eq a b))
        eR : Deriv (eqF (ap2 (Lift1 (constN 1)) a b) (ap1 s O))
        eR = ruleTrans (Lift1_eq (constN 1) a b) (constN_eq 1 a)
        e2 : Deriv (eqF (ap2 sigma (ap2 (Post fG sub_at_s) a b)
                                    (ap2 (Lift1 (constN 1)) a b))
                         (ap2 sigma (ap1 fG (ap2 sub a (ap1 s b))) (ap1 s O)))
        e2 = ruleTrans (congL sigma (ap2 (Lift1 (constN 1)) a b) eL)
                        (congR sigma (ap1 fG (ap2 sub a (ap1 s b))) eR)
    in ruleTrans e1 e2

  fuelMu_fun : Fun2
  fuelMu_fun = R fuelBase sigma fuelStepH2

  fuelMu_at_O : (a : Term) ->
                Deriv (eqF (ap2 fuelMu_fun a O)
                            (ap2 sigma (ap1 fG a) (ap1 s O)))
  fuelMu_at_O a =
    ruleTrans (ax_R_base fuelBase sigma fuelStepH2 a) (fuelBase-eq a)

  fuelMu_at_s : (a b : Term) ->
                Deriv (eqF (ap2 fuelMu_fun a (ap1 s b))
                            (ap2 sigma
                                 (ap2 sigma (ap1 fG (ap2 sub a (ap1 s b))) (ap1 s O))
                                 (ap2 fuelMu_fun a b)))
  fuelMu_at_s a b =
    let e1 : Deriv (eqF (ap2 fuelMu_fun a (ap1 s b))
                         (ap2 sigma (ap2 fuelStepH2 a b) (ap2 fuelMu_fun a b)))
        e1 = ax_R_step fuelBase sigma fuelStepH2 a b
        e2 : Deriv (eqF (ap2 sigma (ap2 fuelStepH2 a b) (ap2 fuelMu_fun a b))
                         (ap2 sigma
                              (ap2 sigma (ap1 fG (ap2 sub a (ap1 s b))) (ap1 s O))
                              (ap2 fuelMu_fun a b)))
        e2 = congL sigma (ap2 fuelMu_fun a b) (fuelStepH2-eq a b)
    in ruleTrans e1 e2

  ----------------------------------------------------------------------
  -- Section 1b.  ClosedAtVar for gc + gc-sub0 / gc-sub1  (sealed via
  -- abstract to keep type-checker from walking deep gFun structures).

  cav-natCode : (k : Nat) (n : Nat) -> Eq (substT k O (natCode n)) (natCode n)
  cav-natCode k zero    = refl
  cav-natCode k (suc n) = eqCong (ap1 s) (cav-natCode k n)

  cav-substT-natCode : (k : Nat) (a : Term) (n : Nat) ->
    Eq (substT k a (natCode n)) (natCode n)
  cav-substT-natCode k a zero    = refl
  cav-substT-natCode k a (suc n) = eqCong (ap1 s) (cav-substT-natCode k a n)

  cav-mcode1-sub : (k : Nat) (a : Term) (f : Fun1) ->
    Eq (substT k a (mcode1 f)) (mcode1 f)
  cav-mcode2-sub : (k : Nat) (a : Term) (g' : Fun2) ->
    Eq (substT k a (mcode2 g')) (mcode2 g')

  cav-mcode1-sub k a s =
    eqCong (\ t -> ap2 pi t O) (cav-substT-natCode k a tag_s)
  cav-mcode1-sub k a o =
    eqCong (\ t -> ap2 pi t O) (cav-substT-natCode k a tag_o)
  cav-mcode1-sub k a u =
    eqCong (\ t -> ap2 pi t O) (cav-substT-natCode k a tag_u)
  cav-mcode1-sub k a (C g' h1' h2') =
    eqTrans
      (eqCong (\ t -> ap2 pi t
                          (ap2 pi (substT k a (mcode2 g'))
                                   (ap2 pi (substT k a (mcode1 h1'))
                                            (substT k a (mcode1 h2')))))
              (cav-substT-natCode k a tag_C))
      (eqTrans
        (eqCong (\ t -> ap2 pi (natCode tag_C)
                                (ap2 pi t
                                        (ap2 pi (substT k a (mcode1 h1'))
                                                (substT k a (mcode1 h2')))))
                (cav-mcode2-sub k a g'))
        (eqTrans
          (eqCong (\ t -> ap2 pi (natCode tag_C)
                                  (ap2 pi (mcode2 g')
                                          (ap2 pi t
                                                  (substT k a (mcode1 h2')))))
                  (cav-mcode1-sub k a h1'))
          (eqCong (\ t -> ap2 pi (natCode tag_C)
                                  (ap2 pi (mcode2 g')
                                          (ap2 pi (mcode1 h1') t)))
                  (cav-mcode1-sub k a h2'))))

  cav-mcode2-sub k a v =
    eqCong (\ t -> ap2 pi t O) (cav-substT-natCode k a tag_v)
  cav-mcode2-sub k a (R g' h1' h2') =
    eqTrans
      (eqCong (\ t -> ap2 pi t
                          (ap2 pi (substT k a (mcode1 g'))
                                   (ap2 pi (substT k a (mcode2 h1'))
                                            (substT k a (mcode2 h2')))))
              (cav-substT-natCode k a tag_R))
      (eqTrans
        (eqCong (\ t -> ap2 pi (natCode tag_R)
                                (ap2 pi t
                                        (ap2 pi (substT k a (mcode2 h1'))
                                                (substT k a (mcode2 h2')))))
                (cav-mcode1-sub k a g'))
        (eqTrans
          (eqCong (\ t -> ap2 pi (natCode tag_R)
                                  (ap2 pi (mcode1 g')
                                          (ap2 pi t
                                                  (substT k a (mcode2 h2')))))
                  (cav-mcode2-sub k a h1'))
          (eqCong (\ t -> ap2 pi (natCode tag_R)
                                  (ap2 pi (mcode1 g')
                                          (ap2 pi (mcode2 h1') t)))
                  (cav-mcode2-sub k a h2'))))

  -- Sealed via  abstract  per
  -- feedback_slow_typecheck_means_abstract_constants .

  abstract
    gc-sub0 : (a : Term) -> Eq (substT zero a gc) gc
    gc-sub0 a = cav-mcode1-sub zero a gFun

    gc-sub1 : (a : Term) -> Eq (substT (suc zero) a gc) gc
    gc-sub1 a = cav-mcode1-sub (suc zero) a gFun

  ----------------------------------------------------------------------
  -- Section 1c.  sim-mcode1 / sim-mcode2  -- simultaneous-substitution
  -- closedness for mcode1 / mcode2 (used at bundle wrapper).

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

  abstract
    gc-sim : (a b : Term) -> Eq (simSubstT zero a (suc zero) b gc) gc
    gc-sim a b = sim-mcode1 a b gFun

  ----------------------------------------------------------------------
  -- Section 2.  Motive  P  and  Q := imp Rf P .

  y_var : Term
  y_var = var zero

  K_var : Term
  K_var = var (suc zero)

  k_at : Term -> Term
  k_at y = ap2 sub k_max y

  K_ext_at : Term -> Term
  K_ext_at y = kons (frmM gc (k_at y)) K_var

  cInit_at : Term -> Term
  cInit_at y = cfgEV gc (k_at y) (K_ext_at y)

  cFinal : Term
  cFinal = cfgRT k_max K_var

  fuelAt : Term -> Term
  fuelAt y = ap2 fuelMu_fun k_max y

  P_eq_at : Term -> Formula
  P_eq_at y = eqF (ap2 (iter step) (cInit_at y) (fuelAt y)) cFinal

  P_eq : Formula
  P_eq = P_eq_at y_var

  P : Formula
  P = imp (leq y_var k_max) P_eq

  Q : Formula
  Q = imp Rf P

  ----------------------------------------------------------------------
  -- Section 2a.  Local closed cfg-rewrites (copied verbatim from
  -- Construct).

  cfgRT-val-rw : (val val' K : Term) ->
                  Deriv (eqF val val') ->
                  Deriv (eqF (cfgRT val K) (cfgRT val' K))
  cfgRT-val-rw val val' K e = congR pi (natCode tagRT) (congL pi K e)

  cfgEV-arg-rw : (fc a a' K : Term) ->
                  Deriv (eqF a a') ->
                  Deriv (eqF (cfgEV fc a K) (cfgEV fc a' K))
  cfgEV-arg-rw fc a a' K e =
    congR pi (natCode tagEV) (congL pi K (congR pi fc e))

  cfgEV-kont-rw : (fc a K K' : Term) ->
                   Deriv (eqF K K') ->
                   Deriv (eqF (cfgEV fc a K) (cfgEV fc a K'))
  cfgEV-kont-rw fc a K K' e =
    congR pi (natCode tagEV) (congR pi (ap2 pi fc a) e)

  iter-step1 : (c c' : Term) ->
                Deriv (eqF (ap1 step c) c') ->
                Deriv (eqF (ap2 (iter step) c (ap1 s O)) c')
  iter-step1 c c' e =
    let e1 = iter_step_univ step c O
        e2 = cong1 step (iter_base_univ step c)
    in ruleTrans e1 (ruleTrans e2 e)

  frmM-index-rw : (t t' : Term) ->
                   Deriv (eqF t t') ->
                   Deriv (eqF (frmM gc t) (frmM gc t'))
  frmM-index-rw t t' e = congR pi (natCode 4) (congR pi gc e)

  ----------------------------------------------------------------------
  -- Section 2b.  Imp-lifted cfg-rewrites.

  imp_cfgRT-val-rw : (val val' K : Term) ->
                     Deriv (imp Rf (eqF val val')) ->
                     Deriv (imp Rf (eqF (cfgRT val K) (cfgRT val' K)))
  imp_cfgRT-val-rw val val' K e_imp =
    impCongR {Rf} pi (ap2 pi val K) (ap2 pi val' K) (natCode tagRT)
      (impCongL {Rf} pi val val' K e_imp)

  ----------------------------------------------------------------------
  -- Section 3.  imp_clean-O -- mirror clean-O with imp_isHit.
  --
  -- We follow clean-O's outline closely.  All steps that don't use isHit
  -- are imp-lifted via  impLift  + closed body ; the single
  -- cAfterG-bridge  step uses  imp_isHit  via  imp_cfgRT-val-rw .

  open import BRA3.ChurchSubSucc using ( T_sub_O )

  imp_clean-O :
    Deriv (imp Rf
           (eqF (ap2 (iter step) (cInit_at O) (fuelAt O)) cFinal))
  imp_clean-O =
    let
      kMaxK : Term
      kMaxK = kons (frmM gc k_max) K_var

      eSub : Deriv (eqF (ap2 sub k_max O) k_max)
      eSub = T_sub_O k_max

      cInit-bridge1 : Deriv (eqF (cInit_at O) (cfgEV gc k_max (K_ext_at O)))
      cInit-bridge1 = cfgEV-arg-rw gc (ap2 sub k_max O) k_max (K_ext_at O) eSub

      eFrmM : Deriv (eqF (frmM gc (ap2 sub k_max O)) (frmM gc k_max))
      eFrmM = frmM-index-rw (ap2 sub k_max O) k_max eSub

      eKExt : Deriv (eqF (K_ext_at O) kMaxK)
      eKExt = congR pi (ap1 s O) (congL pi K_var eFrmM)

      cInit-bridge2 : Deriv (eqF (cfgEV gc k_max (K_ext_at O)) (cfgEV gc k_max kMaxK))
      cInit-bridge2 = cfgEV-kont-rw gc k_max (K_ext_at O) kMaxK eKExt

      cInit-bridge : Deriv (eqF (cInit_at O) (cfgEV gc k_max kMaxK))
      cInit-bridge = ruleTrans cInit-bridge1 cInit-bridge2

      eFuel : Deriv (eqF (fuelAt O) (ap2 sigma (ap1 fG k_max) (ap1 s O)))
      eFuel = fuelMu_at_O k_max

      addStep : Deriv (eqF (ap2 (iter step) (cfgEV gc k_max kMaxK)
                                              (ap2 sigma (ap1 fG k_max) (ap1 s O)))
                            (ap2 (iter step)
                                  (ap2 (iter step) (cfgEV gc k_max kMaxK) (ap1 fG k_max))
                                  (ap1 s O)))
      addStep = iter_add_T (cfgEV gc k_max kMaxK) (ap1 fG k_max) (ap1 s O)

      runG : Deriv (eqF (ap2 (iter step) (cfgEV gc k_max kMaxK) (ap1 fG k_max))
                         (cfgRT (ap1 gFun k_max) kMaxK))
      runG = runs1 bF k_max kMaxK

      -- imp-lifted cAfterG-bridge via imp_isHit.
      imp_cAfterG-bridge :
        Deriv (imp Rf (eqF (cfgRT (ap1 gFun k_max) kMaxK) (cfgRT O kMaxK)))
      imp_cAfterG-bridge =
        imp_cfgRT-val-rw (ap1 gFun k_max) O kMaxK imp_isHit

      stepMbase : Deriv (eqF (ap1 step (cfgRT O kMaxK)) (cfgRT k_max K_var))
      stepMbase = stepU_at_rtMbase gc k_max K_var

      one_step : Deriv (eqF (ap2 (iter step) (cfgRT O kMaxK) (ap1 s O))
                             (cfgRT k_max K_var))
      one_step = iter-step1 (cfgRT O kMaxK) (cfgRT k_max K_var) stepMbase

      imp_half1 :
        Deriv (imp Rf (eqF (ap2 (iter step) (cfgEV gc k_max kMaxK) (ap1 fG k_max))
                            (cfgRT O kMaxK)))
      imp_half1 =
        impEqTrans (ap2 (iter step) (cfgEV gc k_max kMaxK) (ap1 fG k_max))
                   (cfgRT (ap1 gFun k_max) kMaxK) (cfgRT O kMaxK)
                   (impLift {Rf} runG) imp_cAfterG-bridge

      imp_half2 :
        Deriv (imp Rf (eqF (ap2 (iter step)
                                  (ap2 (iter step) (cfgEV gc k_max kMaxK) (ap1 fG k_max))
                                  (ap1 s O))
                            (cfgRT k_max K_var)))
      imp_half2 =
        impEqTrans (ap2 (iter step)
                         (ap2 (iter step) (cfgEV gc k_max kMaxK) (ap1 fG k_max))
                         (ap1 s O))
                   (ap2 (iter step) (cfgRT O kMaxK) (ap1 s O))
                   (cfgRT k_max K_var)
                   (impCongL {Rf} (iter step)
                              (ap2 (iter step) (cfgEV gc k_max kMaxK) (ap1 fG k_max))
                              (cfgRT O kMaxK) (ap1 s O) imp_half1)
                   (impLift {Rf} one_step)

      imp_full_sigma :
        Deriv (imp Rf (eqF (ap2 (iter step) (cfgEV gc k_max kMaxK)
                                              (ap2 sigma (ap1 fG k_max) (ap1 s O)))
                            (cfgRT k_max K_var)))
      imp_full_sigma =
        impEqTrans (ap2 (iter step) (cfgEV gc k_max kMaxK)
                                     (ap2 sigma (ap1 fG k_max) (ap1 s O)))
                   (ap2 (iter step)
                         (ap2 (iter step) (cfgEV gc k_max kMaxK) (ap1 fG k_max))
                         (ap1 s O))
                   (cfgRT k_max K_var)
                   (impLift {Rf} addStep) imp_half2

      imp_full_fuelMu_at_kMaxK :
        Deriv (imp Rf
               (eqF (ap2 (iter step) (cfgEV gc k_max kMaxK) (fuelAt O))
                     (cfgRT k_max K_var)))
      imp_full_fuelMu_at_kMaxK =
        impEqTrans (ap2 (iter step) (cfgEV gc k_max kMaxK) (fuelAt O))
                   (ap2 (iter step) (cfgEV gc k_max kMaxK)
                                     (ap2 sigma (ap1 fG k_max) (ap1 s O)))
                   (cfgRT k_max K_var)
                   (impLift {Rf} (congR (iter step) (cfgEV gc k_max kMaxK) eFuel))
                   imp_full_sigma

      imp_full :
        Deriv (imp Rf
               (eqF (ap2 (iter step) (cInit_at O) (fuelAt O)) cFinal))
      imp_full =
        impEqTrans (ap2 (iter step) (cInit_at O) (fuelAt O))
                   (ap2 (iter step) (cfgEV gc k_max kMaxK) (fuelAt O))
                   cFinal
                   (impLift {Rf} (congL (iter step) (fuelAt O) cInit-bridge))
                   imp_full_fuelMu_at_kMaxK
    in imp_full

  ----------------------------------------------------------------------
  -- Section 4.  imp_premiseB --  Deriv (substF zero O Q) .
  --
  -- substF zero O Q = substF zero O (imp Rf P)
  --                 = imp (substF zero O Rf) (substF zero O P)
  --                 (definitional, BRA3.Formula).
  --
  -- We first build  Deriv (imp Rf (substF zero O P))  by mirroring
  -- premiseB's eqSubst chain over (k_max_sub0 O, gc-sub0 O), then bridge
  -- to  Deriv (substF zero O Q)  via  sub0_Rf O .

  Pred-B-imp : Term -> Term -> Set
  Pred-B-imp gcArg kArg =
    Deriv (imp Rf
           (imp (eqF (ap2 sub O kArg) O)
                (eqF (ap2 (iter step)
                          (cfgEV gcArg (ap2 sub kArg O)
                                        (kons (frmM gcArg (ap2 sub kArg O)) (var (suc zero))))
                          (ap2 fuelMu_fun kArg O))
                      (cfgRT kArg (var (suc zero))))))

  imp_clean-B : Pred-B-imp gc k_max
  imp_clean-B =
    let antP : Formula
        antP = eqF (ap2 sub O k_max) O
        QinnerEq : Formula
        QinnerEq = eqF (ap2 (iter step)
                            (cfgEV gc (ap2 sub k_max O)
                                       (kons (frmM gc (ap2 sub k_max O)) (var (suc zero))))
                            (ap2 fuelMu_fun k_max O))
                       (cfgRT k_max (var (suc zero)))
        weaken_under_Rf :
          Deriv (imp Rf (imp QinnerEq (imp antP QinnerEq)))
        weaken_under_Rf = impLift {Rf} (axK QinnerEq antP)
    in impMp {Rf} weaken_under_Rf imp_clean-O

  imp_premiseB_inner : Deriv (imp Rf (substF zero O P))
  imp_premiseB_inner =
    let
      P1 : Term -> Set
      P1 gcArg = Pred-B-imp gcArg (substT zero O k_max)

      step1 : Pred-B-imp gc (substT zero O k_max)
      step1 = eqSubst (\ k -> Pred-B-imp gc k) (eqSym (k_max_sub0 O)) imp_clean-B

      step2 : Pred-B-imp (substT zero O gc) (substT zero O k_max)
      step2 = eqSubst P1 (eqSym (gc-sub0 O)) step1
    in step2

  imp_premiseB : Deriv (substF zero O Q)
  imp_premiseB =
    -- substF zero O Q = imp (substF zero O Rf) (substF zero O P)  (def).
    -- We have  Deriv (imp Rf (substF zero O P)) ;  bridge Rf ->
    -- substF zero O Rf  via  eqSym (sub0_Rf O) .
    eqSubst (\ R' -> Deriv (imp R' (substF zero O P)))
            (eqSym (sub0_Rf O)) imp_premiseB_inner

  ----------------------------------------------------------------------
  -- Section 5.  premiseS_closed -- copied verbatim from
  -- Construct.premiseS .  Does NOT use isHit -- only depends on missSucc,
  -- subSuccBridge, leqDecrease, subBoundsAux (all closed module params).

  sy : Term
  sy = ap1 s y_var

  Hyp1 : Formula
  Hyp1 = P

  Hyp2 : Formula
  Hyp2 = leq sy k_max

  Ant_y : Formula
  Ant_y = leq y_var k_max

  P_eq_y : Formula
  P_eq_y = P_eq_at y_var

  under2 : (X : Formula) -> Deriv X -> Deriv (imp Hyp1 (imp Hyp2 X))
  under2 X dX = liftP Hyp1 (liftP Hyp2 dX)

  ----------------------------------------------------------------------
  -- Section 5a.  Imp-form cong rewrites (for chaining under Hyp2).

  cfgRT-val-imp : (a b K : Term) ->
                  Deriv (imp (eqF a b) (eqF (cfgRT a K) (cfgRT b K)))
  cfgRT-val-imp a b K =
    compI (ax_eqCongL pi a b K)
          (ax_eqCongR pi (ap2 pi a K) (ap2 pi b K) (natCode tagRT))

  cfgEV-arg-imp : (fc a a' K : Term) ->
                  Deriv (imp (eqF a a') (eqF (cfgEV fc a K) (cfgEV fc a' K)))
  cfgEV-arg-imp fc a a' K =
    compI (ax_eqCongR pi a a' fc)
      (compI (ax_eqCongL pi (ap2 pi fc a) (ap2 pi fc a') K)
             (ax_eqCongR pi (ap2 pi (ap2 pi fc a) K) (ap2 pi (ap2 pi fc a') K)
                             (natCode tagEV)))

  cfgEV-kont-imp : (fc a K K' : Term) ->
                   Deriv (imp (eqF K K') (eqF (cfgEV fc a K) (cfgEV fc a K')))
  cfgEV-kont-imp fc a K K' =
    compI (ax_eqCongR pi K K' (ap2 pi fc a))
          (ax_eqCongR pi (ap2 pi (ap2 pi fc a) K) (ap2 pi (ap2 pi fc a) K')
                          (natCode tagEV))

  frmM-index-imp : (t t' : Term) ->
                   Deriv (imp (eqF t t') (eqF (frmM gc t) (frmM gc t')))
  frmM-index-imp t t' =
    compI (ax_eqCongR pi t t' gc)
          (ax_eqCongR pi (ap2 pi gc t) (ap2 pi gc t') (natCode 4))

  kons-frame-imp : (frame frame' K : Term) ->
                   Deriv (imp (eqF frame frame') (eqF (kons frame K) (kons frame' K)))
  kons-frame-imp frame frame' K =
    compI (ax_eqCongL pi frame frame' K)
          (ax_eqCongR pi (ap2 pi frame K) (ap2 pi frame' K) (ap1 s O))

  iterL-imp : (c c' fuel : Term) ->
              Deriv (imp (eqF c c') (eqF (ap2 (iter step) c fuel)
                                           (ap2 (iter step) c' fuel)))
  iterL-imp c c' fuel = ax_eqCongL (iter step) c c' fuel

  iterR-imp : (c f f' : Term) ->
              Deriv (imp (eqF f f') (eqF (ap2 (iter step) c f)
                                           (ap2 (iter step) c f')))
  iterR-imp c f f' = ax_eqCongR (iter step) f f' c

  ----------------------------------------------------------------------
  -- Section 5b.  Symmetry as implication.

  axSymImp : (x y : Term) -> Deriv (imp (eqF x y) (eqF y x))
  axSymImp x y =
    bComb (ax_eqTrans x y x) (liftP (eqF x y) (axRefl x))

  transUnder2 :
    {a b c : Term} ->
    Deriv (imp Hyp1 (imp Hyp2 (eqF a b))) ->
    Deriv (imp Hyp1 (imp Hyp2 (eqF b c))) ->
    Deriv (imp Hyp1 (imp Hyp2 (eqF a c)))
  transUnder2 {a} {b} {c} D1 D2 =
    let lift_trans : Deriv (imp Hyp1 (imp Hyp2
                              (imp (eqF b a) (imp (eqF b c) (eqF a c)))))
        lift_trans = under2 _ (ax_eqTrans b a c)
        sym-ab : Deriv (imp (eqF a b) (eqF b a))
        sym-ab = axSymImp a b
        symD1 : Deriv (imp Hyp1 (imp Hyp2 (eqF b a)))
        symD1 = bCombTwo (under2 _ sym-ab) D1
        step1 : Deriv (imp Hyp1 (imp Hyp2 (imp (eqF b c) (eqF a c))))
        step1 = bCombTwo lift_trans symD1
    in bCombTwo step1 D2

  ----------------------------------------------------------------------
  -- Section 5c.  Key Terms.

  X1 : Term
  X1 = ap1 fG (ap2 sub k_max sy)

  X2 : Term
  X2 = ap1 s O

  X3 : Term
  X3 = ap2 fuelMu_fun k_max y_var

  c0 : Term
  c0 = cInit_at sy

  Kext : Term
  Kext = K_ext_at sy

  c1 : Term
  c1 = cfgRT (ap1 gFun (ap2 sub k_max sy)) Kext

  c1' : Term
  c1' = cfgRT (ap1 s (ap1 predFun (ap2 sub k_max sy))) Kext

  c2 : Term
  c2 = cfgEV gc (ap1 s (ap2 sub k_max sy))
              (kons (frmM gc (ap1 s (ap2 sub k_max sy))) K_var)

  c2' : Term
  c2' = cInit_at y_var

  ----------------------------------------------------------------------
  -- Section 5d.  Hyp2-only derivations.

  D-Ant_y : Deriv (imp Hyp2 Ant_y)
  D-Ant_y = leqDecrease y_var

  D-SubSucc : Deriv (imp Hyp2 (eqF (ap1 s (ap2 sub k_max sy)) (ap2 sub k_max y_var)))
  D-SubSucc = subSuccBridge y_var

  D-MissBounds : Deriv (imp Hyp2 (leq (ap1 s (ap2 sub k_max sy)) k_max))
  D-MissBounds = subBoundsAux y_var

  D-MissSucc :
    Deriv (imp Hyp2 (eqF (ap1 gFun (ap2 sub k_max sy))
                          (ap1 s (ap1 predFun (ap2 sub k_max sy)))))
  D-MissSucc = compI D-MissBounds (missSucc (ap2 sub k_max sy))

  ----------------------------------------------------------------------
  -- Section 5e.  Segment derivations (under Hyp1, Hyp2).

  segA : Deriv (eqF (ap2 (iter step) c0 X1) c1)
  segA = runs1 bF (ap2 sub k_max sy) Kext

  D-A : Deriv (imp Hyp1 (imp Hyp2 (eqF (ap2 (iter step) c0 X1) c1)))
  D-A = under2 _ segA

  D-segB : Deriv (imp Hyp2 (eqF c1 c1'))
  D-segB = compI D-MissSucc
            (cfgRT-val-imp (ap1 gFun (ap2 sub k_max sy))
                            (ap1 s (ap1 predFun (ap2 sub k_max sy)))
                            Kext)

  D-B : Deriv (imp Hyp1 (imp Hyp2 (eqF c1 c1')))
  D-B = liftP Hyp1 D-segB

  segC : Deriv (eqF (ap2 (iter step) c1' X2) c2)
  segC = iter-step1 c1' c2
           (stepU_at_rtMstep (ap1 predFun (ap2 sub k_max sy))
                              gc (ap2 sub k_max sy) K_var)

  D-C : Deriv (imp Hyp1 (imp Hyp2 (eqF (ap2 (iter step) c1' X2) c2)))
  D-C = under2 _ segC

  D-segD-arg :
    Deriv (imp Hyp2 (eqF c2 (cfgEV gc (ap2 sub k_max y_var)
                                       (kons (frmM gc (ap1 s (ap2 sub k_max sy))) K_var))))
  D-segD-arg = compI D-SubSucc
                 (cfgEV-arg-imp gc (ap1 s (ap2 sub k_max sy)) (ap2 sub k_max y_var)
                                 (kons (frmM gc (ap1 s (ap2 sub k_max sy))) K_var))

  D-frmM-rw : Deriv (imp Hyp2 (eqF (frmM gc (ap1 s (ap2 sub k_max sy)))
                                     (frmM gc (ap2 sub k_max y_var))))
  D-frmM-rw = compI D-SubSucc
                (frmM-index-imp (ap1 s (ap2 sub k_max sy)) (ap2 sub k_max y_var))

  D-kons-rw : Deriv (imp Hyp2 (eqF (kons (frmM gc (ap1 s (ap2 sub k_max sy))) K_var)
                                    (kons (frmM gc (ap2 sub k_max y_var)) K_var)))
  D-kons-rw = compI D-frmM-rw
                (kons-frame-imp (frmM gc (ap1 s (ap2 sub k_max sy)))
                                 (frmM gc (ap2 sub k_max y_var)) K_var)

  D-segD-kont :
    Deriv (imp Hyp2 (eqF (cfgEV gc (ap2 sub k_max y_var)
                                    (kons (frmM gc (ap1 s (ap2 sub k_max sy))) K_var))
                         c2'))
  D-segD-kont = compI D-kons-rw
                 (cfgEV-kont-imp gc (ap2 sub k_max y_var)
                                  (kons (frmM gc (ap1 s (ap2 sub k_max sy))) K_var)
                                  (kons (frmM gc (ap2 sub k_max y_var)) K_var))

  transUnder1 :
    {Q' : Formula} {a b c : Term} ->
    Deriv (imp Q' (eqF a b)) ->
    Deriv (imp Q' (eqF b c)) ->
    Deriv (imp Q' (eqF a c))
  transUnder1 {Q'} {a} {b} {c} D1 D2 =
    let lift_trans : Deriv (imp Q' (imp (eqF b a) (imp (eqF b c) (eqF a c))))
        lift_trans = liftP Q' (ax_eqTrans b a c)
        symD1 : Deriv (imp Q' (eqF b a))
        symD1 = compI D1 (axSymImp a b)
        step1 : Deriv (imp Q' (imp (eqF b c) (eqF a c)))
        step1 = bComb lift_trans symD1
    in bComb step1 D2

  D-segD : Deriv (imp Hyp2 (eqF c2 c2'))
  D-segD = transUnder1 D-segD-arg D-segD-kont

  D-D : Deriv (imp Hyp1 (imp Hyp2 (eqF c2 c2')))
  D-D = liftP Hyp1 D-segD

  D-segE-Pey : Deriv (imp Hyp1 (imp Hyp2 P_eq_y))
  D-segE-Pey = bCombTwo (axK Hyp1 Hyp2) (liftP Hyp1 D-Ant_y)

  D-E : Deriv (imp Hyp1 (imp Hyp2 (eqF (ap2 (iter step) c2' X3) cFinal)))
  D-E = D-segE-Pey

  ----------------------------------------------------------------------
  -- Section 5f.  Chain the 5 segments + fuel folding.

  D-iterAdd-inner :
    Deriv (imp Hyp1 (imp Hyp2 (eqF (ap2 (iter step) c0 (ap2 sigma X1 X2))
                                    (ap2 (iter step) (ap2 (iter step) c0 X1) X2))))
  D-iterAdd-inner = under2 _ (iter_add_T c0 X1 X2)

  D-A-X2 :
    Deriv (imp Hyp1 (imp Hyp2 (eqF (ap2 (iter step) (ap2 (iter step) c0 X1) X2)
                                    (ap2 (iter step) c1 X2))))
  D-A-X2 = under2 _ (congL (iter step) X2 segA)

  D-B-X2 :
    Deriv (imp Hyp1 (imp Hyp2 (eqF (ap2 (iter step) c1 X2)
                                    (ap2 (iter step) c1' X2))))
  D-B-X2 =
    let inner : Deriv (imp Hyp2 (eqF (ap2 (iter step) c1 X2)
                                       (ap2 (iter step) c1' X2)))
        inner = compI D-segB (iterL-imp c1 c1' X2)
    in liftP Hyp1 inner

  D-HalfA :
    Deriv (imp Hyp1 (imp Hyp2 (eqF (ap2 (iter step) c0 (ap2 sigma X1 X2)) c2)))
  D-HalfA = transUnder2 D-iterAdd-inner
              (transUnder2 D-A-X2 (transUnder2 D-B-X2 D-C))

  D-D-X3 :
    Deriv (imp Hyp1 (imp Hyp2 (eqF (ap2 (iter step) c2 X3)
                                    (ap2 (iter step) c2' X3))))
  D-D-X3 =
    let inner : Deriv (imp Hyp2 (eqF (ap2 (iter step) c2 X3)
                                       (ap2 (iter step) c2' X3)))
        inner = compI D-segD (iterL-imp c2 c2' X3)
    in liftP Hyp1 inner

  D-HalfB : Deriv (imp Hyp1 (imp Hyp2 (eqF (ap2 (iter step) c2 X3) cFinal)))
  D-HalfB = transUnder2 D-D-X3 D-E

  D-iterAdd-outer :
    Deriv (imp Hyp1 (imp Hyp2 (eqF (ap2 (iter step) c0 (ap2 sigma (ap2 sigma X1 X2) X3))
                                    (ap2 (iter step) (ap2 (iter step) c0 (ap2 sigma X1 X2)) X3))))
  D-iterAdd-outer = under2 _ (iter_add_T c0 (ap2 sigma X1 X2) X3)

  iter-congL-under2 :
    {a b : Term} (f : Term) ->
    Deriv (imp Hyp1 (imp Hyp2 (eqF a b))) ->
    Deriv (imp Hyp1 (imp Hyp2 (eqF (ap2 (iter step) a f) (ap2 (iter step) b f))))
  iter-congL-under2 {a} {b} f D =
    bCombTwo (under2 _ (iterL-imp a b f)) D

  D-HalfA-X3 :
    Deriv (imp Hyp1 (imp Hyp2 (eqF (ap2 (iter step) (ap2 (iter step) c0 (ap2 sigma X1 X2)) X3)
                                    (ap2 (iter step) c2 X3))))
  D-HalfA-X3 = iter-congL-under2 X3 D-HalfA

  D-FullSigma :
    Deriv (imp Hyp1 (imp Hyp2 (eqF (ap2 (iter step) c0 (ap2 sigma (ap2 sigma X1 X2) X3))
                                    cFinal)))
  D-FullSigma = transUnder2 D-iterAdd-outer (transUnder2 D-HalfA-X3 D-HalfB)

  D-FuelBridge :
    Deriv (imp Hyp1 (imp Hyp2 (eqF (ap2 (iter step) c0 (fuelAt sy))
                                    (ap2 (iter step) c0 (ap2 sigma (ap2 sigma X1 X2) X3)))))
  D-FuelBridge = under2 _ (congR (iter step) c0 (fuelMu_at_s k_max y_var))

  D-Concl-clean :
    Deriv (imp Hyp1 (imp Hyp2 (eqF (ap2 (iter step) c0 (fuelAt sy)) cFinal)))
  D-Concl-clean = transUnder2 D-FuelBridge D-FullSigma

  D-imp-clean : Deriv (imp Hyp1 (imp Hyp2 (P_eq_at sy)))
  D-imp-clean = D-Concl-clean

  ----------------------------------------------------------------------
  -- Section 5g.  Bridge to  substF zero sy P  via closure witnesses.

  Pred-PS : Term -> Term -> Set
  Pred-PS gcArg kArg =
    Deriv (imp Hyp1
              (imp (eqF (ap2 sub sy kArg) O)
                   (eqF (ap2 (iter step)
                             (cfgEV gcArg (ap2 sub kArg sy)
                                           (kons (frmM gcArg (ap2 sub kArg sy)) (var (suc zero))))
                             (ap2 fuelMu_fun kArg sy))
                         (cfgRT kArg (var (suc zero))))))

  clean-PS : Pred-PS gc k_max
  clean-PS = D-imp-clean

  premiseS_closed : Deriv (imp Hyp1 (substF zero sy P))
  premiseS_closed =
    let
      P1 : Term -> Set
      P1 gcArg = Pred-PS gcArg (substT zero sy k_max)

      step1 : Pred-PS gc (substT zero sy k_max)
      step1 = eqSubst (\ k -> Pred-PS gc k) (eqSym (k_max_sub0 sy)) clean-PS

      step2 : Pred-PS (substT zero sy gc) (substT zero sy k_max)
      step2 = eqSubst P1 (eqSym (gc-sub0 sy)) step1
    in step2

  ----------------------------------------------------------------------
  -- Section 5h.  imp_premiseS -- derive  Deriv (imp Q (substF zero sy Q))
  -- from the closed  premiseS_closed  via  axS  +  sub0_Rf sy  bridge.
  --
  -- Hyp1 = P.   substF zero sy Q = substF zero sy (imp Rf P)
  --                              = imp (substF zero sy Rf) (substF zero sy P)  (def).
  -- After  sub0_Rf sy  bridge:  imp Rf (substF zero sy P) .
  --
  -- From  premiseS_closed : imp P (substF zero sy P) , we need
  --   imp (imp Rf P) (imp Rf (substF zero sy P)) .
  --
  -- via  axS Rf P (substF zero sy P) :
  --   imp (imp Rf (imp P X)) (imp (imp Rf P) (imp Rf X))   where X = substF zero sy P.

  imp_premiseS_inner : Deriv (imp Q (imp Rf (substF zero sy P)))
  imp_premiseS_inner =
    let
      X : Formula
      X = substF zero sy P

      lifted : Deriv (imp Rf (imp P X))
      lifted = impLift {Rf} premiseS_closed

      axS_inst : Deriv (imp (imp Rf (imp P X)) (imp (imp Rf P) (imp Rf X)))
      axS_inst = axS Rf P X
    in mp axS_inst lifted

  imp_premiseS : Deriv (imp Q (substF zero sy Q))
  imp_premiseS =
    eqSubst (\ R' -> Deriv (imp Q (imp R' (substF zero sy P))))
            (eqSym (sub0_Rf sy)) imp_premiseS_inner

  ----------------------------------------------------------------------
  -- Section 6.  imp_peter via ruleIndNat at motive Q.

  imp_peter : Deriv Q
  imp_peter = ruleIndNat zero {Q} imp_premiseB imp_premiseS

  ----------------------------------------------------------------------
  -- Section 7.  imp_runs_mu bundle wrapper.

  imp_runs_mu :
    (x_outer K0 : Term) ->
    Deriv (imp Rf
           (eqF (ap2 (iter step) (cfgEV (mcodeMu gc) x_outer K0)
                                  (ap2 sigma (ap1 s O) (ap2 fuelMu_fun k_max k_max)))
                (cfgRT k_max K0)))
  imp_runs_mu x_outer K0 =
    let
      -- Step 1.  Instantiate imp_peter at (var 0 := k_max, var 1 := K0).
      raw_spec : Deriv (simSubstF zero k_max (suc zero) K0 Q)
      raw_spec = ruleInst2 zero k_max (suc zero) K0 refl imp_peter

      -- simSubstF distributes over imp definitionally.
      -- raw_spec : Deriv (imp (simSubstF 0 k_max 1 K0 Rf)
      --                        (simSubstF 0 k_max 1 K0 P))
      -- Bridge  simSubstF 0 k_max 1 K0 Rf -> Rf  via sim_Rf k_max K0.

      spec : Deriv (imp Rf (simSubstF zero k_max (suc zero) K0 P))
      spec = eqSubst (\ R' -> Deriv (imp R' (simSubstF zero k_max (suc zero) K0 P)))
                      (sim_Rf k_max K0) raw_spec

      -- Pred-Bundle-imp parameterised in (gcArg, kArg).
      Pred-Bundle-imp : Term -> Term -> Set
      Pred-Bundle-imp gcArg kArg =
        Deriv (imp Rf
               (imp (eqF (ap2 sub k_max kArg) O)
                    (eqF (ap2 (iter step)
                              (cfgEV gcArg (ap2 sub kArg k_max)
                                             (kons (frmM gcArg (ap2 sub kArg k_max)) K0))
                              (ap2 fuelMu_fun kArg k_max))
                          (cfgRT kArg K0))))

      step1 : Pred-Bundle-imp gc (simSubstT zero k_max (suc zero) K0 k_max)
      step1 = eqSubst (\ g -> Pred-Bundle-imp g (simSubstT zero k_max (suc zero) K0 k_max))
                       (gc-sim k_max K0) spec

      step2 : Pred-Bundle-imp gc k_max
      step2 = eqSubst (\ k -> Pred-Bundle-imp gc k) (k_max_sim k_max K0) step1

      -- Step 2.  Discharge antecedent via leqRefl_k_max under imp Rf.
      imp_D-spec-eqF :
        Deriv (imp Rf
               (eqF (ap2 (iter step)
                         (cfgEV gc (ap2 sub k_max k_max)
                                     (kons (frmM gc (ap2 sub k_max k_max)) K0))
                         (ap2 fuelMu_fun k_max k_max))
                     (cfgRT k_max K0)))
      imp_D-spec-eqF = impMp {Rf} step2 (impLift {Rf} leqRefl_k_max)

      -- Step 3.  Bridge sub k_max k_max -> O  (closed eCfgEV chain).
      eSub : Deriv (eqF (ap2 sub k_max k_max) O)
      eSub = sub_k_max_k_max

      eK : Deriv (eqF (kons (frmM gc (ap2 sub k_max k_max)) K0)
                       (kons (frmM gc O) K0))
      eK = congR pi (ap1 s O) (congL pi K0 (frmM-index-rw (ap2 sub k_max k_max) O eSub))

      eCfgEV : Deriv (eqF (cfgEV gc (ap2 sub k_max k_max)
                                      (kons (frmM gc (ap2 sub k_max k_max)) K0))
                           (cfgEV gc O (kons (frmM gc O) K0)))
      eCfgEV = ruleTrans (cfgEV-arg-rw gc (ap2 sub k_max k_max) O
                                         (kons (frmM gc (ap2 sub k_max k_max)) K0) eSub)
                          (cfgEV-kont-rw gc O
                                          (kons (frmM gc (ap2 sub k_max k_max)) K0)
                                          (kons (frmM gc O) K0) eK)

      cMid : Term
      cMid = cfgEV gc O (kons (frmM gc O) K0)

      imp_D-spec-clean :
        Deriv (imp Rf
               (eqF (ap2 (iter step) cMid (ap2 fuelMu_fun k_max k_max))
                     (cfgRT k_max K0)))
      imp_D-spec-clean =
        let
          flip : Deriv (eqF (ap2 (iter step) cMid (ap2 fuelMu_fun k_max k_max))
                             (ap2 (iter step)
                                   (cfgEV gc (ap2 sub k_max k_max)
                                                (kons (frmM gc (ap2 sub k_max k_max)) K0))
                                   (ap2 fuelMu_fun k_max k_max)))
          flip = ruleSym (congL (iter step) (ap2 fuelMu_fun k_max k_max) eCfgEV)
        in impEqTrans (ap2 (iter step) cMid (ap2 fuelMu_fun k_max k_max))
                       (ap2 (iter step)
                             (cfgEV gc (ap2 sub k_max k_max)
                                          (kons (frmM gc (ap2 sub k_max k_max)) K0))
                             (ap2 fuelMu_fun k_max k_max))
                       (cfgRT k_max K0)
                       (impLift {Rf} flip) imp_D-spec-eqF

      -- Step 4.  Prepend 1 stepU_at_evMu step.
      stepMu : Deriv (eqF (ap1 step (cfgEV (mcodeMu gc) x_outer K0)) cMid)
      stepMu = stepU_at_evMu gc x_outer K0

      run_one : Deriv (eqF (ap2 (iter step) (cfgEV (mcodeMu gc) x_outer K0) (ap1 s O))
                            cMid)
      run_one = iter-step1 (cfgEV (mcodeMu gc) x_outer K0) cMid stepMu

      -- Step 5.  Compose via iter_add_T (closed).
      cInit : Term
      cInit = cfgEV (mcodeMu gc) x_outer K0

      fuelFull : Term
      fuelFull = ap2 sigma (ap1 s O) (ap2 fuelMu_fun k_max k_max)

      addStep : Deriv (eqF (ap2 (iter step) cInit fuelFull)
                            (ap2 (iter step) (ap2 (iter step) cInit (ap1 s O))
                                              (ap2 fuelMu_fun k_max k_max)))
      addStep = iter_add_T cInit (ap1 s O) (ap2 fuelMu_fun k_max k_max)

      mid_iter : Deriv (eqF (ap2 (iter step) (ap2 (iter step) cInit (ap1 s O))
                                              (ap2 fuelMu_fun k_max k_max))
                             (ap2 (iter step) cMid (ap2 fuelMu_fun k_max k_max)))
      mid_iter = congL (iter step) (ap2 fuelMu_fun k_max k_max) run_one

      pre_bridge : Deriv (eqF (ap2 (iter step) cInit fuelFull)
                               (ap2 (iter step) cMid (ap2 fuelMu_fun k_max k_max)))
      pre_bridge = ruleTrans addStep mid_iter

      final : Deriv (imp Rf (eqF (ap2 (iter step) cInit fuelFull)
                                  (cfgRT k_max K0)))
      final = impEqTrans (ap2 (iter step) cInit fuelFull)
                          (ap2 (iter step) cMid (ap2 fuelMu_fun k_max k_max))
                          (cfgRT k_max K0)
                          (impLift {Rf} pre_bridge) imp_D-spec-clean
    in final
