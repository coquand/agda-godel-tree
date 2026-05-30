{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.StepU2MuCorrect -- mu-loop completeness for the Layer-1
-- universal interpreter, via OBJECT-LEVEL ruleIndNat 0 on the depth
-- variable.  This is Piece 2B of Goal 2 from
-- BRA4/PETERREC-NEXT-SESSION-HANDOFF.md.
--
-- STATUS (2026-05-29).  COMPLETE.   1099 LoC, ~1s cold typecheck,
-- --safe --without-K --exact-split, no holes, no postulates.
--
-- Sections:
--   * Section 1:  fuelMu_fun : Fun2  via R, with closed-form unfolds.
--   * Section 1b: cav-mcode1 / cav-mcode2 closedness for gc.
--   * Section 2:  motive P  (var 0 = depth, var 1 = K_outer, k_max free).
--   * Section 2a: helper cfg-rewrites.
--   * Section 3:  clean-O  -- base-case operational chain at depth O.
--   * Section 4:  premiseB  : Deriv (substF zero O P).
--   * Section 5:  premiseS  -- 5-segment step chain (A: bF.runs1 + B:
--                 missSucc + C: stepU_at_rtMstep + D: subSuccBridge +
--                 E: IH-via-leqDecrease), all under two antecedents
--                 Hyp1 = P, Hyp2 = leq (s y) k_max.
--   * Section 6:  peter := ruleIndNat zero {P} premiseB premiseS.
--   * Section 7:  runs_mu  -- bundle wrapper via ruleInst2 (var 0 := k_max,
--                 var 1 := K0) + sim-mcode1/k_max_sim bridge + leqRefl_k_max
--                 + sub_k_max_k_max + stepU_at_evMu prepend.
--
-- TOP-LEVEL EXPORT:
--
--   runs_mu : (x_outer K0 : Term) ->
--     Deriv (eqF (ap2 (iter step) (cfgEV (mcodeMu gc) x_outer K0)
--                                   (ap2 sigma (ap1 s O)
--                                              (ap2 fuelMu_fun k_max k_max)))
--                 (cfgRT k_max K0))
--
-- ARCHITECTURE.  The mu-loop's continuation has ONE frmM frame whose
-- search index is rewritten at each miss step -- there is no iterated
-- K-stack accumulating per step.  So PeterRec's mutated-V machinery
-- is unnecessary and plain  ruleIndNat 0  on the depth variable is
-- the structurally honest principle.   k_max stays FREE in the motive
-- (not packed at var 1), since it doesn't iterate; K_outer = var 1 is
-- left FREE (universally quantified) and instantiated at bundle time.
--
-- HYPOTHESES (module Construct parameters).  In addition to the
-- expected (gFun, bF, k_max, isHit, missSucc, predFun), the caller
-- supplies three BRA bridges over  sub  and  leq  that are pure
-- arithmetic facts about  k_max  (independent of gFun).  This keeps
-- the present module a CLEAN OPERATIONAL PROOF; the caller's burden
-- to discharge the bridges is a one-off per choice of  k_max  (e.g.,
-- via FirstHit's leastNumber for a numeral / search-derived  k_max ).
--
-- MOTIVE.  P has the depth variable at  var 0 = y  and the outer
-- continuation at  var 1 = K_outer .   k_max  is a free Term (not a
-- var).   The motive's antecedent  leq y k_max  guards the depth
-- range; its conclusion is the operational chain at search index
-- sub k_max y , extended-K  kons (frmM gc (sub k_max y)) K_outer .
--
--   P :=
--     imp (leq y k_max)
--          (eqF (iter step
--                 (cfgEV gc (sub k_max y)
--                              (kons (frmM gc (sub k_max y)) K_outer))
--                 (fuelMu_fun k_max y))
--                (cfgRT k_max K_outer))
--
-- BASE (y = O).  Search index = sub k_max O = k_max .  1 fG(k_max)
-- gc-eval + 1 stepU_at_rtMbase.
--
-- STEP (y = s y').  Search index = sub k_max (s y') (a miss).  IH at
-- y' gives the chain from sub k_max y'.  We compose:
--    fG(sub k_max (s y')) gc-eval at miss
--   + 1 stepU_at_rtMstep (peels the miss frame, advances to
--     search index s (sub k_max (s y')))
--   + bridge  s (sub k_max (s y')) = sub k_max y'  (= the
--     subSuccBridge hypothesis)
--   + IH  at y'.
--
-- BUNDLE.   runs-Mu (x_outer K0 : Term) :   instantiates peter at
-- var 0 := k_max, var 1 := K0 via ruleInst2; bridges leq k_max k_max
-- (T_leq_refl on k_max), sub k_max k_max = O (T_sub_refl on k_max);
-- prepends 1 stepU_at_evMu step from cfgEV (mcodeMu gc) x_outer K0 .
--
-- The caller bundles  isHit ,  missSucc ,  subSuccBridge ,
-- leqDecrease , subBoundsAux  for their concrete  k_max  (typically a
-- numeral or a FirstHit-derived term).

module BRA4.StepU2MuCorrect where

open import BRA4.Base
open import BRA4.StepU2
  using ( step
        ; cfgEV ; cfgRT ; kons ; mcode1 ; mcode2
        ; tagRT ; tagEV )
open import BRA4.EvalU
  using ( mcodeMu ; frmM )
open import BRA4.EvalUStep
  using ( stepU_at_evMu ; stepU_at_rtMbase ; stepU_at_rtMstep )
open import BRA4.StepU2Reach
  using ( iter_add_T )
open import BRA4.LoopReaches
  using ( ClosedAtVar ; mkCAV ; cavSubst
        ; cav_O ; cav_ap1 ; cav_ap2 ; cav_natCode )
open import BRA4.Tags
  using ( tag_s ; tag_o ; tag_u ; tag_C ; tag_v ; tag_R )
open import BRA4.StepU2CorrectAPI
  using ( Correct1 ; Correct2 ; mkC2
        ; fuelF ; runs1 )

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
-- Section 1.  Module Construct -- per-(gFun, k_max, ...) mu chain.

module Construct
  (gFun : Fun1)
  (bF : Correct1 gFun)
  (k_max : Term)
  (predFun : Fun1)
  (isHit : Deriv (eqF (ap1 gFun k_max) O))
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
  -- Closedness of k_max at vars 0 and 1 (caller-supplied since k_max is
  -- a black-box Term; for typical use -- numeral or FirstHit-derived
  -- closed Term -- both are trivial).
  (k_max_sub0 : (a : Term) -> Eq (substT zero a k_max) k_max)
  (k_max_sub1 : (a : Term) -> Eq (substT (suc zero) a k_max) k_max)
  -- Simultaneous-substitution closedness for k_max (used at the bundle
  -- wrapper for ruleInst2; trivial for closed k_max).
  (k_max_sim : (a b : Term) -> Eq (simSubstT zero a (suc zero) b k_max) k_max)
  where

  ----------------------------------------------------------------------
  -- Closed components.

  gc : Term
  gc = mcode1 gFun

  fG : Fun1
  fG = fuelF bF

  ----------------------------------------------------------------------
  -- Section 1a.  fuelMu_fun : Fun2  -- depth-fuel for the mu walk.
  --
  --   fuelMu_fun k_max O      = sigma (fG k_max) (s O)
  --   fuelMu_fun k_max (s y') = sigma (sigma (fG (sub k_max (s y'))) (s O))
  --                                    (fuelMu_fun k_max y')
  --
  -- Built with  R fuelBase sigma fuelStepH2 .

  -- fuelBase : Fun1 with ap1 fuelBase k = sigma (fG k) (s O).
  fuelBase : Fun1
  fuelBase = C sigma fG (constN 1)

  fuelBase-eq : (k : Term) ->
                Deriv (eqF (ap1 fuelBase k) (ap2 sigma (ap1 fG k) (ap1 s O)))
  fuelBase-eq k =
    let e1 = ax_C sigma fG (constN 1) k
        e2 = congR sigma (ap1 fG k) (constN_eq 1 k)
    in ruleTrans e1 e2

  -- sub_at_s : Fun2 with ap2 sub_at_s a b = sub a (s b).
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

  -- fuelStepH2 : Fun2 with ap2 fuelStepH2 a b = sigma (fG (sub a (s b))) (s O).
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

  -- fuelMu_fun : Fun2 via R-recursion on the 2nd arg.
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
  -- Section 1b.  ClosedAtVar witness for gc = mcode1 gFun.

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

  -- SEALED  abstract :   downstream openings of  Construct  at  gFun :=
  -- predFlip Lstar  would otherwise trigger sim-mcode1 / cav-mcode1 to
  -- recurse through the deeply-nested  hitK / out_L / wrapAll  Fun1 chain,
  -- blowing up Agda's type-checker.   With these witnesses abstract, the
  -- premiseB / premiseS / runs_mu  eqSubst calls keep them as opaque  Eq
  -- witnesses -- type-checking aligns without normalising  gFun .
  abstract
    cav-gc-0 : ClosedAtVar zero gc
    cav-gc-0 = cav-mcode1 zero gFun

    cav-gc-1 : ClosedAtVar (suc zero) gc
    cav-gc-1 = cav-mcode1 (suc zero) gFun

    gc-sub0 : (a : Term) -> Eq (substT zero a gc) gc
    gc-sub0 a = cavSubst cav-gc-0 a

    gc-sub1 : (a : Term) -> Eq (substT (suc zero) a gc) gc
    gc-sub1 a = cavSubst cav-gc-1 a

  ----------------------------------------------------------------------
  -- Section 1c.  fuelMu_fun closedness:  Eq (substT k a fuelMu_fun) fuelMu_fun
  -- not needed since fuelMu_fun is a Fun2 (no Term substitution).
  -- But  ap2 fuelMu_fun k_max y  involves the Term  y , so we'll need
  --   Eq (substT k a (ap2 fuelMu_fun k_max y)) (ap2 fuelMu_fun (substT k a k_max) (substT k a y))
  -- which is automatic from the ap2 case.   For our purposes we use the
  -- k_max_sub0/sub1 witnesses on  k_max  directly.

  ----------------------------------------------------------------------
  -- Section 2.  Motive P -- ruleIndNat 0 on  y = var 0  with V := var 1
  -- left FREE (it is the outer continuation K_outer, not mutated).
  -- k_max is a free Term (Construct parameter).
  --
  -- (Note: the dichotomy "PeterRec uses var 1 packed = mutated" / "we
  -- use var 1 free = constant" is the structural simplification --
  -- the mu continuation's frmM frame just changes index, no kons stack
  -- accumulates.)

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

  ----------------------------------------------------------------------
  -- Section 2a.  Local helper rewrites (mirroring StepU2CorrectRPeter).

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

  -- One step of iter: from "step c = c'" derive "iter step c (s O) = c'".
  iter-step1 : (c c' : Term) ->
                Deriv (eqF (ap1 step c) c') ->
                Deriv (eqF (ap2 (iter step) c (ap1 s O)) c')
  iter-step1 c c' e =
    let e1 = iter_step_univ step c O
        e2 = cong1 step (iter_base_univ step c)
    in ruleTrans e1 (ruleTrans e2 e)

  ----------------------------------------------------------------------
  -- Section 3.  Clean chain at depth O -- the BASE operational core.
  --
  -- At y = O, search index = sub k_max O = k_max (T_sub_O).  We run
  -- bF at (k_max, K_ext_at_k_max), get cfgRT (gFun k_max) K_ext;
  -- isHit rewrites gFun k_max to O; one stepU_at_rtMbase fires.

  open import BRA3.ChurchSubSucc using ( T_sub_O )

  -- frmM-index-rw : congruence rewriting the search index inside frmM.
  frmM-index-rw : (t t' : Term) ->
                   Deriv (eqF t t') ->
                   Deriv (eqF (frmM gc t) (frmM gc t'))
  frmM-index-rw t t' e = congR pi (natCode 4) (congR pi gc e)
    -- frmM gc k = pi (natCode tagM) (pi gc k), tagM = 4 in BRA4.EvalU.

  -- Clean target for depth O (= the substituted form ignoring substT
  -- closedness lemmas).
  clean-O :
    Deriv (eqF (ap2 (iter step) (cInit_at O) (fuelAt O)) cFinal)
  clean-O =
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

      cAfterG-bridge : Deriv (eqF (cfgRT (ap1 gFun k_max) kMaxK) (cfgRT O kMaxK))
      cAfterG-bridge = cfgRT-val-rw (ap1 gFun k_max) O kMaxK isHit

      stepMbase : Deriv (eqF (ap1 step (cfgRT O kMaxK)) (cfgRT k_max K_var))
      stepMbase = stepU_at_rtMbase gc k_max K_var

      one_step : Deriv (eqF (ap2 (iter step) (cfgRT O kMaxK) (ap1 s O))
                             (cfgRT k_max K_var))
      one_step = iter-step1 (cfgRT O kMaxK) (cfgRT k_max K_var) stepMbase

      half1 : Deriv (eqF (ap2 (iter step) (cfgEV gc k_max kMaxK) (ap1 fG k_max))
                          (cfgRT O kMaxK))
      half1 = ruleTrans runG cAfterG-bridge

      half2 : Deriv (eqF (ap2 (iter step)
                                (ap2 (iter step) (cfgEV gc k_max kMaxK) (ap1 fG k_max))
                                (ap1 s O))
                          (cfgRT k_max K_var))
      half2 = ruleTrans (congL (iter step) (ap1 s O) half1) one_step

      full_sigma : Deriv (eqF (ap2 (iter step) (cfgEV gc k_max kMaxK)
                                                 (ap2 sigma (ap1 fG k_max) (ap1 s O)))
                               (cfgRT k_max K_var))
      full_sigma = ruleTrans addStep half2

      full_fuelMu_at_kMaxK :
        Deriv (eqF (ap2 (iter step) (cfgEV gc k_max kMaxK) (fuelAt O))
                    (cfgRT k_max K_var))
      full_fuelMu_at_kMaxK =
        ruleTrans (congR (iter step) (cfgEV gc k_max kMaxK) eFuel) full_sigma

      full :
        Deriv (eqF (ap2 (iter step) (cInit_at O) (fuelAt O))
                    (cfgRT k_max K_var))
      full =
        ruleTrans (congL (iter step) (fuelAt O) cInit-bridge) full_fuelMu_at_kMaxK
    in full

  ----------------------------------------------------------------------
  -- Section 4.  premiseB :  Deriv (substF zero O P).
  --
  -- substF 0 O P reduces (by Agda computation) to a Formula with
  -- substT 0 O gc and substT 0 O k_max in place of gc, k_max.  We
  -- bridge via the closedness witnesses.

  -- Pred-B is the SHAPE of substF 0 O P parameterised in two Terms,
  -- one for each opaque (gc, k_max) position.  At (gc, k_max) it
  -- coincides with the clean form (= clean-O wrapped with antecedent).

  Pred-B : Term -> Term -> Set
  Pred-B gcArg kArg =
    Deriv (imp (eqF (ap2 sub O kArg) O)
               (eqF (ap2 (iter step)
                         (cfgEV gcArg (ap2 sub kArg O)
                                       (kons (frmM gcArg (ap2 sub kArg O)) (var (suc zero))))
                         (ap2 fuelMu_fun kArg O))
                     (cfgRT kArg (var (suc zero)))))

  -- Weakening: Deriv Q -> Deriv (imp ant Q) for any Formula ant.
  weaken-imp : (Q ant : Formula) -> Deriv Q -> Deriv (imp ant Q)
  weaken-imp Q ant dQ = mp (axK Q ant) dQ

  -- Clean form (lifted with the antecedent).
  clean-B : Pred-B gc k_max
  clean-B =
    let antP : Formula
        antP = eqF (ap2 sub O k_max) O
        Q : Formula
        Q = eqF (ap2 (iter step)
                     (cfgEV gc (ap2 sub k_max O)
                                (kons (frmM gc (ap2 sub k_max O)) (var (suc zero))))
                     (ap2 fuelMu_fun k_max O))
                (cfgRT k_max (var (suc zero)))
    in weaken-imp Q antP clean-O

  -- Bridge clean-B from (gc, k_max) to (substT 0 O gc, substT 0 O k_max).

  premiseB : Deriv (substF zero O P)
  premiseB =
    let
      P1 : Term -> Set
      P1 gcArg = Pred-B gcArg (substT zero O k_max)

      step1 : Pred-B gc (substT zero O k_max)
      step1 = eqSubst (\ k -> Pred-B gc k) (eqSym (k_max_sub0 O)) clean-B

      step2 : Pred-B (substT zero O gc) (substT zero O k_max)
      step2 = eqSubst P1 (eqSym (gc-sub0 O)) step1
    in step2

  ----------------------------------------------------------------------
  -- Section 5.  premiseS  --  the step-case operational chain.
  --
  --   Goal:  Deriv (imp P (substF zero (ap1 s y_var) P)) .

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

  -- "under two antecedents" weakening.
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
    -- frmM gc t = pi (natCode tagM) (pi gc t), tagM = 4.

  kons-frame-imp : (frame frame' K : Term) ->
                   Deriv (imp (eqF frame frame') (eqF (kons frame K) (kons frame' K)))
  kons-frame-imp frame frame' K =
    compI (ax_eqCongL pi frame frame' K)
          (ax_eqCongR pi (ap2 pi frame K) (ap2 pi frame' K) (ap1 s O))
    -- kons frame K = pi (s O) (pi frame K).

  -- congL (iter step) under Hyp2.
  iterL-imp : (c c' fuel : Term) ->
              Deriv (imp (eqF c c') (eqF (ap2 (iter step) c fuel)
                                           (ap2 (iter step) c' fuel)))
  iterL-imp c c' fuel = ax_eqCongL (iter step) c c' fuel

  -- congR (iter step) under Hyp2.
  iterR-imp : (c f f' : Term) ->
              Deriv (imp (eqF f f') (eqF (ap2 (iter step) c f)
                                           (ap2 (iter step) c f')))
  iterR-imp c f f' = ax_eqCongR (iter step) f f' c

  ----------------------------------------------------------------------
  -- Section 5b.  Symmetry of eqF as an implication.

  axSymImp : (x y : Term) -> Deriv (imp (eqF x y) (eqF y x))
  axSymImp x y =
    -- ax_eqTrans x y x : imp (eqF x y) (imp (eqF x x) (eqF y x)).
    -- bComb with axRefl x.
    bComb (ax_eqTrans x y x) (liftP (eqF x y) (axRefl x))

  -- transUnder2  --  eqF transitivity under two antecedents.

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
  -- Section 5c.  Key Terms (intermediate configurations and fuels).

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

  -- Segment A: iter step c0 X1 = c1   (Term-only, via bF.runs1).

  segA : Deriv (eqF (ap2 (iter step) c0 X1) c1)
  segA = runs1 bF (ap2 sub k_max sy) Kext

  D-A : Deriv (imp Hyp1 (imp Hyp2 (eqF (ap2 (iter step) c0 X1) c1)))
  D-A = under2 _ segA

  -- Segment B: c1 = c1'   (Hyp2-dep via D-MissSucc + cfgRT-val cong).

  D-segB : Deriv (imp Hyp2 (eqF c1 c1'))
  D-segB = compI D-MissSucc
            (cfgRT-val-imp (ap1 gFun (ap2 sub k_max sy))
                            (ap1 s (ap1 predFun (ap2 sub k_max sy)))
                            Kext)

  D-B : Deriv (imp Hyp1 (imp Hyp2 (eqF c1 c1')))
  D-B = liftP Hyp1 D-segB

  -- Segment C: iter step c1' X2 = c2   (Term-only via iter-step1 + stepU_at_rtMstep).

  segC : Deriv (eqF (ap2 (iter step) c1' X2) c2)
  segC = iter-step1 c1' c2
           (stepU_at_rtMstep (ap1 predFun (ap2 sub k_max sy))
                              gc (ap2 sub k_max sy) K_var)

  D-C : Deriv (imp Hyp1 (imp Hyp2 (eqF (ap2 (iter step) c1' X2) c2)))
  D-C = under2 _ segC

  -- Segment D: c2 = c2'   (Hyp2-dep via D-SubSucc applied at TWO positions:
  -- the cfgEV's argument and inside frmM).

  -- First: rewrite the cfgEV's argument position.
  D-segD-arg :
    Deriv (imp Hyp2 (eqF c2 (cfgEV gc (ap2 sub k_max y_var)
                                       (kons (frmM gc (ap1 s (ap2 sub k_max sy))) K_var))))
  D-segD-arg = compI D-SubSucc
                 (cfgEV-arg-imp gc (ap1 s (ap2 sub k_max sy)) (ap2 sub k_max y_var)
                                 (kons (frmM gc (ap1 s (ap2 sub k_max sy))) K_var))

  -- Second: rewrite inside the frmM frame in the kont.
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

  -- Transitivity at the single-antecedent layer.
  transUnder1 :
    {Q : Formula} {a b c : Term} ->
    Deriv (imp Q (eqF a b)) ->
    Deriv (imp Q (eqF b c)) ->
    Deriv (imp Q (eqF a c))
  transUnder1 {Q} {a} {b} {c} D1 D2 =
    let lift_trans : Deriv (imp Q (imp (eqF b a) (imp (eqF b c) (eqF a c))))
        lift_trans = liftP Q (ax_eqTrans b a c)
        symD1 : Deriv (imp Q (eqF b a))
        symD1 = compI D1 (axSymImp a b)
        step1 : Deriv (imp Q (imp (eqF b c) (eqF a c)))
        step1 = bComb lift_trans symD1
    in bComb step1 D2

  D-segD : Deriv (imp Hyp2 (eqF c2 c2'))
  D-segD = transUnder1 D-segD-arg D-segD-kont

  D-D : Deriv (imp Hyp1 (imp Hyp2 (eqF c2 c2')))
  D-D = liftP Hyp1 D-segD

  -- Segment E: iter step c2' X3 = cFinal  (the IH, Hyp1 + leqDecrease(Hyp2)).
  -- Note: P_eq_y = eqF (iter step c2' X3) cFinal definitionally.

  D-segE-Pey : Deriv (imp Hyp1 (imp Hyp2 P_eq_y))
  D-segE-Pey = bCombTwo (axK Hyp1 Hyp2) (liftP Hyp1 D-Ant_y)

  D-E : Deriv (imp Hyp1 (imp Hyp2 (eqF (ap2 (iter step) c2' X3) cFinal)))
  D-E = D-segE-Pey

  ----------------------------------------------------------------------
  -- Section 5f.  Chain the 5 segments + fuel folding into the full
  -- step-case Deriv.

  -- HalfA: iter step c0 (sigma X1 X2) = c2.
  -- = iter step (iter step c0 X1) X2 [iter_add_T inner]
  -- = iter step c1 X2 [segA + congL X2]
  -- = iter step c1' X2 [segB + congL X2, Hyp2]
  -- = c2 [segC]

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

  -- HalfB: iter step c2 X3 = cFinal.
  -- = iter step c2' X3 [segD + congL X3, Hyp2]
  -- = cFinal [segE]

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

  -- Now combine: iter step c0 (sigma (sigma X1 X2) X3) = cFinal.
  -- = iter step (iter step c0 (sigma X1 X2)) X3 [iter_add_T outer]
  -- = iter step c2 X3 [HalfA + congL X3]
  -- = cFinal [HalfB]

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

  -- Bridge from fuelAt sy to sigma (sigma X1 X2) X3.
  D-FuelBridge :
    Deriv (imp Hyp1 (imp Hyp2 (eqF (ap2 (iter step) c0 (fuelAt sy))
                                    (ap2 (iter step) c0 (ap2 sigma (ap2 sigma X1 X2) X3)))))
  D-FuelBridge = under2 _ (congR (iter step) c0 (fuelMu_at_s k_max y_var))

  D-Concl-clean :
    Deriv (imp Hyp1 (imp Hyp2 (eqF (ap2 (iter step) c0 (fuelAt sy)) cFinal)))
  D-Concl-clean = transUnder2 D-FuelBridge D-FullSigma

  ----------------------------------------------------------------------
  -- Section 5g.  Close: Deriv (imp Hyp1 (imp Hyp2 P_eq_sy)).
  --
  -- P_eq_sy = P_eq_at sy = eqF (iter step c0 (fuelAt sy)) cFinal.
  -- So D-Concl-clean has the right type.

  D-imp-clean : Deriv (imp Hyp1 (imp Hyp2 (P_eq_at sy)))
  D-imp-clean = D-Concl-clean

  ----------------------------------------------------------------------
  -- Section 5h.  Bridge to substF zero (s y_var) P via closure witnesses.
  --
  -- substF 0 (s y_var) P computes to:
  --   imp (eqF (ap2 sub (s var0) (substT 0 (s var0) k_max)) O)
  --       (eqF (ap2 (iter step)
  --             (cfgEV (substT 0 (s var0) gc)
  --                    (ap2 sub (substT 0 (s var0) k_max) (s var0))
  --                    (kons (frmM (substT 0 (s var0) gc)
  --                                 (ap2 sub (substT 0 (s var0) k_max) (s var0)))
  --                          (var 1)))
  --             (ap2 fuelMu_fun (substT 0 (s var0) k_max) (s var0)))
  --        (cfgRT (substT 0 (s var0) k_max) (var 1)))
  --
  -- After eqSubst over (k_max_sub0 (s var0), gc-sub0 (s var0)), this equals
  -- imp Hyp2 P_eq_sy = imp (leq sy k_max) (P_eq_at sy).

  -- D-imp-clean has type Deriv (imp Hyp1 (imp Hyp2 (P_eq_at sy))).  This
  -- matches Deriv (imp Hyp1 (substF 0 sy P)) at the CLEAN form (gc, k_max).
  -- substF 0 sy P computationally reduces to a form with substT 0 sy gc /
  -- substT 0 sy k_max in place of gc, k_max.  Bridge via eqSubst over
  -- (gc-sub0 sy, k_max_sub0 sy).

  -- Pred-PS bundle: Deriv (imp Hyp1 (substF 0 sy P)) shape, parameterised
  -- over (gc', kArg).
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

  premiseS : Deriv (imp Hyp1 (substF zero sy P))
  premiseS =
    let
      P1 : Term -> Set
      P1 gcArg = Pred-PS gcArg (substT zero sy k_max)

      step1 : Pred-PS gc (substT zero sy k_max)
      step1 = eqSubst (\ k -> Pred-PS gc k) (eqSym (k_max_sub0 sy)) clean-PS

      step2 : Pred-PS (substT zero sy gc) (substT zero sy k_max)
      step2 = eqSubst P1 (eqSym (gc-sub0 sy)) step1
    in step2

  ----------------------------------------------------------------------
  -- Section 6.  Invoke ruleIndNat.

  peter : Deriv P
  peter = ruleIndNat zero {P} premiseB premiseS

  ----------------------------------------------------------------------
  -- Section 7.  Bundle wrapper:  runs_mu (x_outer K0 : Term).
  --
  -- Instantiate peter at (var 0 := k_max, var 1 := K0) via ruleInst2;
  -- bridge via leqRefl_k_max, sub_k_max_k_max, sim-mcode1, k_max_sim.
  -- Prepend 1 stepU_at_evMu step from cfgEV (mcodeMu gc) x_outer K0 .

  -- sim-mcode1 / sim-mcode2: simultaneous-substitution closedness for
  -- mcode1, mcode2.   Mirrors cav-mcode1/cav-mcode2 but via simSubstT.

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

  -- See the abstract block at  gc-sub0/sub1  for the rationale: the
  -- sim-mcode1 recursion is the COSTLY one for deep gFun structures.
  abstract
    gc-sim : (a b : Term) -> Eq (simSubstT zero a (suc zero) b gc) gc
    gc-sim a b = sim-mcode1 a b gFun

  ----------------------------------------------------------------------
  -- Bundle wrapper.

  runs_mu :
    (x_outer K0 : Term) ->
    Deriv (eqF (ap2 (iter step) (cfgEV (mcodeMu gc) x_outer K0)
                                  (ap2 sigma (ap1 s O) (ap2 fuelMu_fun k_max k_max)))
                (cfgRT k_max K0))
  runs_mu x_outer K0 =
    let
      -- Step 1.  Instantiate peter at (var 0 := k_max, var 1 := K0).
      spec : Deriv (simSubstF zero k_max (suc zero) K0 P)
      spec = ruleInst2 zero k_max (suc zero) K0 refl peter

      -- The clean form expected after substituting var 0 -> k_max, var 1 -> K0:
      --   imp (leq k_max (simSubstT 0 k_max 1 K0 k_max))   [antecedent: var 0 -> k_max in y_var; original k_max -> simSubstT]
      --       (eqF (iter step (cfgEV (simSubstT gc) (sub (simSubstT k_max) k_max) (kons (frmM (simSubstT gc) (sub (simSubstT k_max) k_max)) K0))
      --                        (fuelMu_fun (simSubstT k_max) k_max))
      --             (cfgRT (simSubstT k_max) K0))
      --
      -- Bridge (simSubstT gc -> gc) via gc-sim, (simSubstT k_max -> k_max)
      -- via k_max_sim.   Pred-Bundle parameterised in (gcArg, kArg) where
      -- both bridge to (gc, k_max).

      Pred-Bundle : Term -> Term -> Set
      Pred-Bundle gcArg kArg =
        Deriv (imp (eqF (ap2 sub k_max kArg) O)
                   (eqF (ap2 (iter step)
                             (cfgEV gcArg (ap2 sub kArg k_max)
                                            (kons (frmM gcArg (ap2 sub kArg k_max)) K0))
                             (ap2 fuelMu_fun kArg k_max))
                         (cfgRT kArg K0)))

      step1 : Pred-Bundle gc (simSubstT zero k_max (suc zero) K0 k_max)
      step1 = eqSubst (\ g -> Pred-Bundle g (simSubstT zero k_max (suc zero) K0 k_max))
                       (gc-sim k_max K0) spec

      step2 : Pred-Bundle gc k_max
      step2 = eqSubst (\ k -> Pred-Bundle gc k) (k_max_sim k_max K0) step1

      -- Step 2.  Discharge antecedent via leqRefl_k_max.
      D-spec-eqF :
        Deriv (eqF (ap2 (iter step)
                        (cfgEV gc (ap2 sub k_max k_max)
                                    (kons (frmM gc (ap2 sub k_max k_max)) K0))
                        (ap2 fuelMu_fun k_max k_max))
                    (cfgRT k_max K0))
      D-spec-eqF = mp step2 leqRefl_k_max

      -- Step 3.  Bridge sub k_max k_max -> O.
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

      D-spec-clean :
        Deriv (eqF (ap2 (iter step) cMid (ap2 fuelMu_fun k_max k_max))
                    (cfgRT k_max K0))
      D-spec-clean =
        ruleTrans (ruleSym (congL (iter step) (ap2 fuelMu_fun k_max k_max) eCfgEV))
                   D-spec-eqF

      -- Step 4.  Prepend 1 stepU_at_evMu step.
      stepMu : Deriv (eqF (ap1 step (cfgEV (mcodeMu gc) x_outer K0)) cMid)
      stepMu = stepU_at_evMu gc x_outer K0

      run_one : Deriv (eqF (ap2 (iter step) (cfgEV (mcodeMu gc) x_outer K0) (ap1 s O))
                            cMid)
      run_one = iter-step1 (cfgEV (mcodeMu gc) x_outer K0) cMid stepMu

      -- Step 5.  Compose via iter_add_T.
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

      final : Deriv (eqF (ap2 (iter step) cInit fuelFull) (cfgRT k_max K0))
      final = ruleTrans addStep (ruleTrans mid_iter D-spec-clean)
    in final
